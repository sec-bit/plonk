use ark_std::{vec, vec::Vec};

use crate::{Error, Field, Map};

use super::{Composer, Variable};

#[derive(Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct Key<F: Field>(Vec<F>);

#[derive(Debug, Default)]
pub struct Table<F: Field> {
    id: String,
    index: usize,
    size: usize,
    width: usize,
    key_width: usize,

    columns: Vec<Vec<F>>,
    lookups: Vec<usize>,

    key_map: Map<Vec<F>, usize>,
}

impl<F: Field> Table<F> {
    fn get_value_by_key(&mut self, key: &[F]) -> Result<Vec<F>, Error> {
        assert_eq!(key.len(), self.key_width);

        match self.key_map.get(key) {
            None => Err(Error::MissingLookupEntry),
            Some(&index) => {
                self.lookups.push(index);
                let values = (self.key_width..self.width)
                    .map(|i| self.columns[i][index])
                    .collect();
                Ok(values)
            }
        }
    }

    fn table_index(&self) -> usize {
        self.index
    }

    fn set_table_index(&mut self, index: usize) {
        self.index = index;
    }
}

impl<F: Field> Table<F> {
    pub fn xor_table(bits: usize) -> Self {
        let entries: u64 = 1 << bits;
        let size = 1 << bits * 2;
        let width = 3;
        let key_width = 2;
        let mut columns = vec![Vec::with_capacity(size); width];
        let mut key_map = Map::with_capacity(size);
        let mut row = 0;
        for l in 0..entries {
            for r in 0..entries {
                for (i, v) in vec![F::from(l), F::from(r), F::from(l ^ r)]
                    .into_iter()
                    .enumerate()
                {
                    columns[i].push(v);
                }

                key_map.insert(vec![F::from(l), F::from(r)], row);
                row += 1;
            }
        }

        Self {
            id: "xor".to_string(),
            index: 0,
            size,
            width,
            key_width,
            columns,
            lookups: Vec::new(),

            key_map,
        }
    }
}

impl<F: Field> Composer<F> {
    pub(super) fn compute_table_values(&self) -> Vec<Vec<F>> {
        // one column
        let mut table_values = vec![Vec::with_capacity(self.table_size()); self.program_width + 1];
        for (i, table) in self.tables.iter().enumerate() {
            for col in 0..table.width {
                table_values[col].extend(table.columns[col].iter());
            }
            for col in table.width..(self.program_width) {
                table_values[col].extend(vec![F::zero(); table.size]);
            }
            table_values[self.program_width].extend(vec![F::from((i + 1) as u64); table.size])
        }

        table_values
    }

    pub(super) fn compute_sorted_values(&self) -> Vec<Vec<F>> {
        let mut sorted_values =
            vec![Vec::with_capacity(self.sorted_size()); self.program_width + 1];

        for (i, table) in self.tables.iter().enumerate() {
            let mut lookups: Vec<_> = (0..table.size).collect();
            lookups.extend(&table.lookups);
            lookups.sort();

            for col in 0..table.width {
                sorted_values[col].extend(lookups.iter().map(|&i| table.columns[col][i]));
            }
            for col in table.width..self.program_width {
                sorted_values[col].extend(vec![F::zero(); lookups.len()]);
            }
            sorted_values[self.program_width].extend(vec![F::from((i + 1) as u64); lookups.len()])
        }

        sorted_values
    }

    pub(super) fn table_size(&self) -> usize {
        let mut size = 0;
        for table in self.tables.iter() {
            size += table.size;
        }

        size
    }

    pub(super) fn sorted_size(&self) -> usize {
        let mut size = 0;
        for table in self.tables.iter() {
            size += table.size + table.lookups.len();
        }

        size
    }
}

impl<F: Field> Composer<F> {
    /// table index starts at 1
    pub fn add_table(&mut self, mut table: Table<F>) -> usize {
        let index = self.tables.len() + 1;
        table.set_table_index(index);
        for t in self.tables.iter() {
            assert_ne!(&t.id, &table.id);
        }
        self.tables.push(table);

        index
    }

    pub fn get_table(&self, index: usize) -> &Table<F> {
        assert!(index - 1 < self.tables.len());
        &self.tables[index - 1]
    }

    pub fn get_table_mut(&mut self, index: usize) -> &mut Table<F> {
        assert!(index - 1 < self.tables.len());
        &mut self.tables[index - 1]
    }

    pub fn read_from_table(
        &mut self,
        table_index: usize,
        key: Vec<Variable>,
    ) -> Result<Vec<Variable>, Error> {
        assert!(!self.is_finalized);

        let lookup_key = self.get_assignments(&key);
        let lookup_value = self
            .get_table_mut(table_index)
            .get_value_by_key(&lookup_key)?;
        let value: Vec<_> = lookup_value.into_iter().map(|v| self.alloc(v)).collect();

        let wires = key.into_iter().chain(value.clone()).collect();
        let index = self.insert_gate(wires);

        self.selectors.get_mut("q_lookup").unwrap()[index] = F::one();
        self.selectors.get_mut("q_table").unwrap()[index] = F::from(table_index as u64);

        Ok(value)
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::Fr;
    use ark_ff::{One, Zero};

    use super::*;

    #[test]
    fn composer_lookup() -> Result<(), Error> {
        let mut cs = Composer::new(4);
        let table_index = cs.add_table(Table::xor_table(2));
        let x = cs.alloc(Fr::from(1));
        let y = cs.alloc(Fr::from(2));
        let z = cs.read_from_table(table_index, vec![x, y])?;
        cs.enforce_constant(z[0], Fr::from(3));
        cs.finalize();

        assert_eq!(cs.size(), 2);
        assert_eq!(cs.selectors["q_range"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_arith"], vec![Fr::zero(), Fr::one()]);
        assert_eq!(cs.selectors["q_lookup"], vec![Fr::one(), Fr::zero()]);
        assert_eq!(cs.selectors["q_table"], vec![Fr::one(), Fr::zero()]);
        assert_eq!(cs.selectors["q_m"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_c"], vec![Fr::zero(), -Fr::from(3)]);
        assert_eq!(cs.selectors["q_0"], vec![Fr::zero(), Fr::one()]);
        assert_eq!(cs.selectors["q_1"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_2"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_3"], vec![Fr::zero(), Fr::zero()]);

        assert_eq!(cs.wires["w_0"], vec![Variable(1), Variable(3)]);
        assert_eq!(cs.wires["w_1"], vec![Variable(2), Variable(0)]);
        assert_eq!(cs.wires["w_2"], vec![Variable(3), Variable(0)]);
        assert_eq!(cs.wires["w_3"], vec![Variable(0), Variable(0)]);

        for (i, v) in cs.assignments.iter().enumerate() {
            println!("{}: {}", i, v);
        }

        Ok(())
    }
}
