//! This modules is about everything related to directions.

/// Straight directions goes straight to any of the four directions:
/// north, south, east, west.
/// It can translate coordinates to directions, translate coordinates
/// given direction and distance, turn etc.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum StraightDirection {
    North,
    East,
    South,
    West
}

/// Type declaring whether to turn left or right or keep straight ahead
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Turn {
    Left,
    Right,
    Straight,
}

impl std::convert::From<[StraightDirection;2]> for Turn {
    /// Given two straight directions, try make a turn
    ///
    /// Note that the order of the directions matter.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Turn, StraightDirection};
    /// let turn_right = Turn::from([StraightDirection::South, StraightDirection::East]);
    /// let turn_left = Turn::from([StraightDirection::North, StraightDirection::East]);
    /// let turn_straight = Turn::from([StraightDirection::North, StraightDirection::South]);
    /// assert!(turn_right== Turn::Right);
    /// assert!(turn_left == Turn::Left);
    /// assert!(turn_straight == Turn::Straight)
    fn from(value: [StraightDirection;2]) -> Self {
        match (value[0], value[1]) {
            (StraightDirection::North, StraightDirection::West) => Turn::Right,
            (StraightDirection::West, StraightDirection::South) => Turn::Right,
            (StraightDirection::South, StraightDirection::East) => Turn::Right,
            (StraightDirection::East, StraightDirection::North) => Turn::Right,
            (StraightDirection::North, StraightDirection::East) => Turn::Left,
            (StraightDirection::East, StraightDirection::South) => Turn::Left,
            (StraightDirection::South, StraightDirection::West) => Turn::Left,
            (StraightDirection::West, StraightDirection::South) => Turn::Left,
            (_, _) => Turn::Straight,
        }
    }
}

impl StraightDirection {
    /// Translate from and to coordinates into a direction pointing
    /// from `from` to `to`. If the coordinates are the same, or
    /// if they do not go strictly in any direction, None is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// assert!(StraightDirection::from_pos((0, 0), (13, 0)) == Some(StraightDirection::East));
    /// assert!(StraightDirection::from_pos((1, 0), (0, 0)) == Some(StraightDirection::West));
    /// assert!(StraightDirection::from_pos((1, 1), (1, 0)) == Some(StraightDirection::North));
    /// assert!(StraightDirection::from_pos((1, 1), (1, 5)) == Some(StraightDirection::South));
    /// assert!(StraightDirection::from_pos((0, 0), (13, 13)) == None);
    pub fn from_pos(from: (usize, usize), to: (usize, usize)) -> Option<Self> {
        let north_south = match to.1.cmp(&from.1) {
            std::cmp::Ordering::Greater => Some(StraightDirection::South),
            std::cmp::Ordering::Less => Some(StraightDirection::North),
            _ => None,
        };
        let east_west = match to.0.cmp(&from.0) {
            std::cmp::Ordering::Greater => Some(StraightDirection::East),
            std::cmp::Ordering::Less => Some(StraightDirection::West),
            _ => None,
        };

        println!("{:?} {:?}", north_south, east_west);
        match (north_south, east_west) {
            (None, None) => None,
            (Some(_), Some(_)) => None,
            (Some(d), None) => Some(d),
            (None, Some(d)) => Some(d),
        }
    }

    /// Calculate a new coordinate given a `from` coordinate, direction and a
    /// distance. Returns None if any coordinate becomes negative.
    ///
    /// # Examples
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// let dir = StraightDirection::North;
    /// assert!(dir.follow((13, 13), 3) == Some((13usize, 10usize)));
    /// assert!(dir.follow((0, 0), 1) == None);
    pub fn follow(&self, from: (usize, usize), distance: usize) -> Option<(usize, usize)> {
        match self {
            StraightDirection::North => if from.1 >= distance {
                Some((from.0, from.1 - distance))
            } else {
                None
            }
            StraightDirection::East => Some((from.0 + 1, from.1)),
            StraightDirection::South => Some((from.0, from.1 + 1)),
            StraightDirection::West => if from.0 >= distance {
                Some((from.0 - distance, from.1))
            } else {
                None
            }
        }
    }

    /// Give the opposite direction.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// assert!(StraightDirection::North.opposite() == StraightDirection::South);
    /// assert!(StraightDirection::West.opposite() == StraightDirection::East);
    pub fn opposite(&self) -> StraightDirection {
        match self {
            StraightDirection::North => StraightDirection::South,
            StraightDirection::East => StraightDirection::West,
            StraightDirection::South => StraightDirection::North,
            StraightDirection::West => StraightDirection::East,
        }
    }

    /// Give the new direction after doing a turn.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Turn, StraightDirection};
    /// assert!(StraightDirection::North.turn(Turn::Right) == StraightDirection::East);
    /// assert!(StraightDirection::West.turn(Turn::Right) == StraightDirection::North);
    /// assert!(StraightDirection::North.turn(Turn::Left) == StraightDirection::West);
    /// assert!(StraightDirection::West.turn(Turn::Left) == StraightDirection::South);
    pub fn turn(&self, way: Turn) -> StraightDirection {
        match way {
            Turn::Straight => *self,
            Turn::Left => {
                match self {
                    StraightDirection::North => StraightDirection::West,
                    StraightDirection::East => StraightDirection::North,
                    StraightDirection::South => StraightDirection::East,
                    StraightDirection::West => StraightDirection::South,
                }
            }
            Turn::Right => {
                match self {
                    StraightDirection::North => StraightDirection::East,
                    StraightDirection::East => StraightDirection::South,
                    StraightDirection::South => StraightDirection::West,
                    StraightDirection::West => StraightDirection::North,
                }
            }
        }
    }
}

/// Bi-directional straight pipes
///
/// Pipes can go straight north to/from south or east to/from west, or can bend
/// 90 degrees left or right.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Pipe {
    EastWest,
    NorthSouth,
    NorthEast,
    NorthWest,
    SouthWest,
    SouthEast,
}

impl std::convert::Into<[StraightDirection;2]> for Pipe {
    /// Returns an array of which direction each end of the pipe is
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// let directions: [StraightDirection;2] = Pipe::EastWest.into();
    /// assert!(directions.contains(&StraightDirection::East) &&
    ///     directions.contains(&StraightDirection::West));
    fn into(self) -> [StraightDirection;2] {
        match self {
            Pipe::EastWest => [StraightDirection::East, StraightDirection::West],
            Pipe::NorthSouth => [StraightDirection::North, StraightDirection::South],
            Pipe::NorthEast => [StraightDirection::North, StraightDirection::East],
            Pipe::NorthWest => [StraightDirection::North, StraightDirection::West],
            Pipe::SouthWest => [StraightDirection::South, StraightDirection::West],
            Pipe::SouthEast => [StraightDirection::South, StraightDirection::East],
        }
    }
}

impl std::convert::TryFrom<[StraightDirection;2]> for Pipe {
    type Error = String;

    /// Given two straight directions, try to make a pipe
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// let pipe_valid = Pipe::try_from([StraightDirection::South, StraightDirection::East]);
    /// let pipe_invalid = Pipe::try_from([StraightDirection::North, StraightDirection::North]);
    /// assert!(pipe_valid == Ok(Pipe::SouthEast));
    /// assert!(pipe_invalid.is_err())
    fn try_from(value: [StraightDirection;2]) -> Result<Self, Self::Error> {
        if value.contains(&StraightDirection::North) {
            if value.contains(&StraightDirection::West) {
                Ok(Pipe::NorthWest)
            } else if value.contains(&StraightDirection::South) {
                Ok(Pipe::NorthSouth)
            } else if value.contains(&StraightDirection::East) {
                Ok(Pipe::NorthEast)
            } else {
                Err(format!("{:?}: Cannot translate into pipe", value))
            }
        } else if value.contains(&StraightDirection::South) {
            if value.contains(&StraightDirection::West) {
                Ok(Pipe::SouthWest)
            } else if value.contains(&StraightDirection::East) {
                Ok(Pipe::SouthEast)
            } else {
                Err(format!("{:?}: Cannot translate into pipe", value))
            }
        } else if value.contains(&StraightDirection::East) &&
            value.contains(&StraightDirection::West) {
                Ok(Pipe::EastWest)
            } else {
                Err(format!("{:?}: Cannot translate into pipe", value))
            }
    }
}

impl std::fmt::Display for Pipe {
    /// Draw the pipe using Unicode characters
    ///
    /// # Examples
    ///
    ///```
    /// use rust_tools::direction::Pipe;
    /// println!("{}", Pipe::SouthWest);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Pipe::EastWest   => write!(f, "{}", '─'),
            Pipe::NorthSouth => write!(f, "{}", '│'),
            Pipe::NorthEast  => write!(f, "{}", '╰'),
            Pipe::NorthWest  => write!(f, "{}", '╯'),
            Pipe::SouthWest  => write!(f, "{}", '╮'),
            Pipe::SouthEast  => write!(f, "{}", '╭'),
        }
    }
}

impl Pipe {
    /// Follow the pipe. Since the pipe is bidirectional, `dir` is used to
    /// determine in which direction to go through the pipe. `dir` is the
    /// direction of the last move.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// assert!(Pipe::NorthEast.follow(StraightDirection::North, (2,3)) ==
    ///     Some((StraightDirection::East, (3,3))));
    /// assert!(Pipe::NorthSouth.follow(StraightDirection::North, (2,3)) ==
    ///     Some((StraightDirection::North, (2,2))));
    /// assert!(Pipe::EastWest.follow(StraightDirection::North, (2,3)) == None);
    /// ```
    pub fn follow(&self, from: StraightDirection, curr: (usize, usize)) -> Option<(StraightDirection, (usize, usize))> {
        let other = self.directions().into_iter().filter(|&e| e != from).collect::<Vec<_>>();
        if other.len() != 1 {
            return None;
        }

        let to = match (from, other[0]) {
            (StraightDirection::North, StraightDirection::South) => StraightDirection::North,
            (StraightDirection::South, StraightDirection::North) => StraightDirection::South,
            (_, dir) => dir,
        };

        if let Some(result) = to.follow(curr, 1) {
            Some((to, result))
        } else {
            None
        }
    }

    /// Returns from <-> to directions.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// let dir = Pipe::NorthEast.directions();
    /// assert!(dir.contains(&StraightDirection::North));
    /// assert!(dir.contains(&StraightDirection::East));
    /// ```
    pub fn directions(&self) -> [StraightDirection;2] {
        match self {
            Pipe::EastWest   => [StraightDirection::East, StraightDirection::West],
            Pipe::NorthSouth => [StraightDirection::North, StraightDirection::South],
            Pipe::NorthEast  => [StraightDirection::North, StraightDirection::East],
            Pipe::NorthWest  => [StraightDirection::North, StraightDirection::West],
            Pipe::SouthWest  => [StraightDirection::South, StraightDirection::West],
            Pipe::SouthEast  => [StraightDirection::South, StraightDirection::East],
        }
    }

    pub fn intersection(&self, other: Pipe) -> Vec<StraightDirection> {
        let mut result: Vec<StraightDirection> = Vec::new();
        let other_vec = other.directions().to_vec();

        for lhs in self.directions() {
            if other_vec.contains(&lhs) {
                result.push(lhs);
            }
        }

        result
    }

    /// Checks whether two pipes are connected
    ///
    /// Check if `self` is connected to `to`, where `to` is expected to be in
    /// `dir` direction from `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// assert!(Pipe::NorthSouth.is_connected_to(StraightDirection::North, Pipe::SouthWest));
    /// assert!(Pipe::NorthWest.is_connected_to(StraightDirection::West, Pipe::NorthEast));
    /// assert!(Pipe::EastWest.is_connected_to(StraightDirection::East, Pipe::SouthWest));
    /// assert!(! Pipe::SouthEast.is_connected_to(StraightDirection::South, Pipe::EastWest));
    pub fn is_connected_to(&self, dir: StraightDirection, to: Pipe) -> bool {
        if self.directions().contains(&dir) && to.directions().contains(&dir.opposite()) {
            true
        } else {
            false
        }
    }
}

