-- Atlas attribute / macros for book-style theorem metadata.
-- (Top-level module; planned to be split out into its own library.)
import Atlas

-- Chapter 2
-- Propositions
import Geometry.Ch2.Prop.P1
import Geometry.Ch2.Prop.P2
import Geometry.Ch2.Prop.P3
import Geometry.Ch2.Prop.P4
import Geometry.Ch2.Prop.P5
-- Exercises -/
-- import Geometry.Ch2.Ex.E1

-- Chapter 3
-- Propositions
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii -- A corrolary of B4, nothing without proof.
import Geometry.Ch3.Prop.P2
import Geometry.Ch3.Prop.P3
import Geometry.Ch3.Prop.P4
import Geometry.Ch3.Prop.P5
import Geometry.Ch3.Prop.P6
import Geometry.Ch3.Prop.P7
import Geometry.Ch3.Prop.Pasch
-- Exercises
import Geometry.Ch3.Ex.Betweenness.Ex1
import Geometry.Ch3.Ex.Review.Ex2
import Geometry.Ch3.Ex.Review.Ex3

-- Interpendices (theory infrastructure that depends on chapter content
-- and so can't sit inside `Geometry/Theory.lean`'s umbrella without
-- cycling). Imported at the top level to ensure they're built.
import Geometry.Theory.Interpendices.C
