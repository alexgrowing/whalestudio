import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem isOfFinOrder_of_conjIn_mem_St :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), IsDefUnimod hc J Λ → IsFrame β Λ → ∀ (u : UR hc J) (x : UA hc J), conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ St β → IsOfFinOrder u := by
  intro F E _ _ _ _ _ _ hc n J L β hU hβ u x hu
  have hfin := Formalism.UG.Final.AdelicStabFiniteL F E (Fin n) hc.sig J (cm_comp hc) hU.herm hU.unit hU.tdef L
    (Module.Finite.iff_fg.2 hU.lat.fg) hU.lat.span_eq_top x
  have hb := base_level_eq_adelic_level F E hc n J L β hβ
  let H : Subgroup (UR hc J) :=
    (Formalism.UG.levelAfL hc.sig J L).comap (conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
  have hH : Finite H := by
    let f : H → Formalism.UG.stabAt (UQ hc J) ((Formalism.UG.levelAfL hc.sig J L).subgroupOf (UA hc J)) x :=
      fun γ => ⟨ratEl γ.1, (ratEl_mem_stabAt x γ.1).2 γ.2⟩
    refine Finite.of_injective f ?_
    intro a b hab
    exact Subtype.ext (ratEl_injective (congrArg Subtype.val hab))
  have huH : u ∈ H := by
    show conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ Formalism.UG.levelAfL hc.sig J L
    rw [← hb]
    refine ⟨?_, hu⟩
    rw [conjIn_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) (ratEl u).1.2) x.2
  have := isOfFinOrder_of_finite (⟨u, huH⟩ : H)
  exact H.subtype.isOfFinOrder this

end GlobalTheory.DefFree
