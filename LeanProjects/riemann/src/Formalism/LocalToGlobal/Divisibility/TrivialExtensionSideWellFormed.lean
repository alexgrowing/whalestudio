import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeRI
import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

namespace FamIn3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 I0 Ty T : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

theorem side_well_formed {s : ℕ} (h : A3.fam3.Ok3 s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3)
    (hst : Zs.Stable) (hin : Zs.InBlock) (hsep : A3.fam3.TypesSep3) : (A3.side3 P ψ Zs).WF := by
  first
  | exact DefFam3.side_well_formed h P ψ Zs hst hin hsep
  | exact A3.fam3.side_well_formed h P ψ Zs hst hin hsep
  | exact DefFam3.side_well_formed (F3 := A3.fam3) h P ψ Zs hst hin hsep

theorem typesSep3_of' (hq : ∀ P, A3.A.q P ≠ 0) (h0 : ∀ P, A3.A.heckeR A3.A.μ0 (P, 0) = 1)
    (hc : Col.PairComm (A3.A.heckeR A3.A.μ0)) (hI : A3.fam3.TrISep) : A3.fam3.TypesSep3 := by
  exact DefFam3.typesSep3_of (F3 := A3.fam3) hc (FamIn.typesSep_of' A3.A hq h0) hI

end FamIn3

namespace FamIn

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

end FamIn

end Formalism.L2.DIV
