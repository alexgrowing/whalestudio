import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LocalSituation TensorProduct GlobalTheory.Per GlobalTheory.Prism

namespace GlobalTheory.Published

def BhattScholzeCrystallineLattices : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e : P₀.A ≃+* Ainf l), IsAinf K P₀ e →
    (∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
      ∀ (LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
        letI := zlMod LL T
        ∃ (E : FCrys l ↥(OL K))
          (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
          Realises K E P₀ e ↥T.L.T (fun g => actTZ LL T g) j) ∧
    (∀ (T T' : Type) [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup T'] [Module ℤ_[l] T']
      (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T'))
      (E E' : FCrys l ↥(OL K))
      (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T))
      (j' : E'.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T')),
      Realises K E P₀ e T ρ j → Realises K E' P₀ e T' ρ' j' →
      ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) →
        ∃! u : FHom E E', ∀ x, j' (u.u P₀ x) = f.lTensor (WCb l) (j x))

example (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (g : ↥(GK K))
    (x : ↥T.L.T) : actTZ LL T g x = T.actT g x := rfl

example (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (inferInstance : TopologicalSpace ↥LL.1) =
      TopologicalSpace.induced Subtype.val (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) := rfl

example (l : ℕ) [Fact l.Prime] (K : FinExt l) :
    (inferInstance : TopologicalSpace ↥(GK K)) =
      TopologicalSpace.induced Subtype.val (krullTopology ℚ_[l] (Om l)) := rfl

end GlobalTheory.Published
