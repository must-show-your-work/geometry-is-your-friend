/-
Geometry/Construction/Matchers.lean — aggregator.

Importing this brings every registered proof-state matcher into the
env. Add new matchers by creating a file under `Matchers/`, tagging
the matcher with `@[proof_state_matcher N]`, and importing it here.
-/

import Geometry.Construction.Matchers.Between
import Geometry.Construction.Matchers.Distinct
import Geometry.Construction.Matchers.Collinear
import Geometry.Construction.Matchers.OppositeRay
import Geometry.Construction.Matchers.LineMembership
import Geometry.Construction.Matchers.Angle
import Geometry.Construction.Matchers.RaysDistinct
import Geometry.Construction.Matchers.Intersects
import Geometry.Construction.Matchers.PointEquality
