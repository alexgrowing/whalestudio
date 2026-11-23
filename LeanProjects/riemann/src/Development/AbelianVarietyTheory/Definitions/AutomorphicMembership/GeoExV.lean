import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def GeoExV (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL]
    (F : Face D A3.A) : Prop :=
  ∀ (R : RealDat D A3.A C.Q.c.F) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Formalism.L2.Host.ValLL D R.C → GlobalTheory.RealGeo.PreChar R → R.grp_levels F → C.pb = R.C.P.pb →
    Keep (A3 := A3) R F cG → ∃ dict mu chiW x₀ cE nW FW,
      (R.upd5 nW FW R.mu R.twPl R.err0).grp_chiW ∧
      Nonempty (@GlobalTheory.RealGeo.GeoHalf D G _ _ Pl0 T A3.A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
        (inferInstanceAs (Algebra C.Q.c.F D.what₂.LL)) (R.upd5 nW FW R.mu R.twPl R.err0) fun _ => 1) ∧
      ∀ i x, ∃ y, (FW i).j (sg0 D A3.A) y = R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x)

theorem GeoEx.geoExV {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL]
    {F : Face D A3.A} (h : GeoEx A3 C F) : GeoExV A3 C F := fun R cG _ => h R cG

end GlobalTheory.Mem.R3
