#[derive(PartialEq, Eq, Debug)]
pub struct Grid2D<T> {
    grid: Vec<Vec<T>>,
}

impl<T> Grid2D<T> {
    /// Create Grid2D from str iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::grid2d::Grid2D;
    /// let test_map: &str = concat!(
    ///     "X..X..X.\n",
    ///     "..X..X..\n",
    ///     ".X..X..X\n",
    ///     "X..X..X.\n",
    ///     "..X..X..\n",
    ///     ".X..X..X\n");
    /// let grid = Grid2D::new(
    ///         &mut test_map.lines(),
    ///         std::collections::HashMap::from([
    ///             ('X', 1),
    ///             ('.', 0),
    ///         ]));
    /// println!("{:#}", grid);
    /// ```
    pub fn new(
        lines: &mut dyn Iterator<Item=&str>,
        translations: std::collections::HashMap<char, T>) -> Self
        where T: Clone + std::fmt::Display
    {
        Self{ grid: lines.take_while(|s| *s != "").map(|s| {
            s.chars().map(|c| translations[&c].clone()).collect::<Vec<T>>()
        })
        .collect::<Vec<Vec<T>>>()
        }
    }

    /// Get number of rows
    ///
    /// ```
    /// use rust_tools::grid2d::Grid2D;
    /// let grid = Grid2D::<i32>::from([
    ///     [0, 1, 2, 3, 4],
    ///     [4, 3, 4, 5, 1],
    ///     ]);
    /// assert!(grid.rows() == 2);
    /// ```
    pub fn rows(&self) -> usize {
        self.grid.len()
    }

    /// Get number of rows
    ///
    /// ```
    /// use rust_tools::grid2d::Grid2D;
    /// let grid = Grid2D::<i32>::from([
    ///     [0, 1, 2, 3, 4],
    ///     [4, 3, 4, 5, 1],
    ///     ]);
    /// assert!(grid.cols() == 5);
    /// ```
    pub fn cols(&self) -> usize {
        if let Some(col) = self.grid.get(0) {
            col.len()
        } else {
            0
        }
    }
}

impl<T> std::default::Default for Grid2D<T> {
    /// Create an empty grid.
    ///
    /// ```
    /// use rust_tools::grid2d::Grid2D;
    /// let grid: Grid2D::<i32> = Grid2D::default();
    /// assert!(grid.cols() == 0);
    /// assert!(grid.rows() == 0);
    /// ```
    fn default() -> Self {
        Self { grid: Vec::new() }
    }
}

impl<T: std::fmt::Display> std::fmt::Display for Grid2D<T> {
    /// Display format, where the alternate form ('#') prepends
    /// each line with the row number
    ///
    /// # Examples
    ///
    ///````
    /// use rust_tools::grid2d::Grid2D;
    /// let grid = Grid2D::<bool>::from([
    ///     [true, false, false, true],
    ///     [false, true, true, true],
    ///     [true, true, true, false]
    ///     ]);
    /// println!("Without row numbers: {}", grid);
    /// println!("With row numbers: {:#}", grid);
    /// ````
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if f.alternate() {
            let row_digits: usize = (self.rows().checked_ilog10().unwrap_or(0) + 1) as usize;
            for (row_idx, row) in self.grid.iter().enumerate() {
                for cell in row {
                    write!(f, "{0:1$} {2}", row_idx, row_digits, *cell)?;
                }
                write!(f, "\n")?;
            }
        } else {
            for row in self.grid.iter() {
                for cell in row {
                    write!(f, "{}", *cell)?;
                }
                write!(f, "\n")?;
            }
        }
        Ok(())
    }
}

impl<T: Clone, const X: usize, const Y: usize> std::convert::From<[[T;X];Y]> for Grid2D<T> {
    /// Create grid from array of array
    /// # Examples
    ///
    ///````
    /// use rust_tools::grid2d::Grid2D;
    /// let grid = Grid2D::<bool>::from([
    ///     [true, false, false, true],
    ///     [false, true, true, true],
    ///     [true, true, true, false]
    ///     ]);
    ///````
    fn from(value: [[T;X];Y]) -> Self {
        let mut grid: Vec<Vec<T>> = Vec::new();
        for row in &value {
            grid.push(row.to_vec());
        }
        Self { grid: grid }
    }
}

#[cfg(test)]
mod grid2d {
    use super::*;
    const TEST_MAP: &str = concat!(
        "...X...X\n",
        "..X..X..\n",
        ".X..X..X\n",
        "X..X..X.\n",
        "..X..X..\n",
        ".X..X..X\n");

    #[derive(PartialEq, Eq, Clone, Debug)]
    enum TestCell {
        Occupied,
        NotOccupied,
    }

    impl std::fmt::Display for TestCell {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", match self {
                TestCell::Occupied => '#',
                TestCell::NotOccupied => '.',
            })
        }
    }

    #[test]
    fn new() {
        let sut = Grid2D::new(&mut TEST_MAP.lines(),
            std::collections::HashMap::from([
                ('.', false),
                ('X', true)
            ]));
        let correct_answer: Vec<Vec<bool>> = vec![
            [false, false, false, true, false, false, false, true].to_vec(),
            [false, false, true, false, false, true, false, false].to_vec(),
            [false, true, false, false, true, false, false,  true].to_vec(),
            [true, false, false, true, false, false, true, false].to_vec(),
            [false, false, true, false, false, true, false, false].to_vec(),
            [false, true, false, false, true, false, false, true].to_vec(),
        ];
        println!("{}", sut);
        for (y, rows) in std::iter::zip(correct_answer.iter(), sut.grid.iter()).enumerate() {
            for (x, cells) in std::iter::zip(rows.0.iter(), rows.1.iter()).enumerate() {
                assert!(cells.0 == cells.1, "Mismatch at ({}, {})", x, y);
            }
        }
    }

    #[test]
    fn display() {
        let correct_debug = "Grid2D { grid: [[Occupied, NotOccupied, Occupied], [NotOccupied, NotOccupied, NotOccupied], [Occupied, Occupied, NotOccupied]] }";
        let correct_answer = concat!(
            "#.#\n",
            "...\n",
            "##.\n",
        );
        let correct_alternate_answer = concat!(
            "0 #.#\n",
            "1 ...\n",
            "2 ##.\n",
        );
        let sut = Grid2D::new(
                &mut correct_answer.lines(),
                std::collections::HashMap::from([
                    ('#', TestCell::Occupied),
                    ('.', TestCell::NotOccupied),
                ]));

        let sut_debug = format!("{:?}", sut);
        assert!(correct_debug == sut_debug,
            "Expected:\n{}\nGot:\n{}", correct_debug, sut_debug);
        let sut_display = format!("{}", sut);
        assert!(correct_answer == sut_display,
            "Expected: \n{}\nGot:\n{}", correct_answer, sut_display);
        let sut_alternate_display = format!("{:#}", sut);
        assert!(correct_answer == sut_display,
            "Expected: \n{}\nGot:\n{}", correct_alternate_answer, sut_alternate_display);
    }
}

