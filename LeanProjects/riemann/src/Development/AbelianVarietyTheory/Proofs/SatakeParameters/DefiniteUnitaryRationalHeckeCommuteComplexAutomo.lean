import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.EigenConj

theorem opOf_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU E n ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  intro E _ _ _ n σ t ht φ φ' z hφ hφ' hfin heig
  have key : ∀ (f : UA E n → ℂ) (x : UA E n),
      opOf (RU E n) t f x = ∑ g ∈ t.support, t g * f (x * g) := by
    intro f x
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc1 : Continuous (opOf (RU E n) t φ') := by
    have e : opOf (RU E n) t φ' = fun x => ∑ g ∈ t.support, t g * φ' (x * g) := funext (key φ')
    rw [e]
    exact continuous_finset_sum _ fun g _ =>
      continuous_const.mul (hφ'.cont.comp (continuous_id.mul continuous_const))
  have hc2 : Continuous (σ z • φ') := hφ'.cont.const_smul _
  have hl1 : ∀ γ ∈ ratU E n, ∀ x, opOf (RU E n) t φ' (γ * x) = opOf (RU E n) t φ' x := by
    intro γ hγ x
    rw [key, key]
    simp_rw [mul_assoc, hφ'.left γ hγ]
  have hl2 : ∀ γ ∈ ratU E n, ∀ x, (σ z • φ') (γ * x) = (σ z • φ') x := by
    intro γ hγ x
    simp only [Pi.smul_apply, hφ'.left γ hγ]
  have hfinEq : ∀ h ∈ finU E n, opOf (RU E n) t φ' h = (σ z • φ') h := by
    intro h hh
    have e := congrFun heig h
    rw [key, Pi.smul_apply, smul_eq_mul] at e
    rw [key, Pi.smul_apply, smul_eq_mul]
    calc ∑ g ∈ t.support, t g * φ' (h * g) = ∑ g ∈ t.support, σ (t g * φ (h * g)) :=
          Finset.sum_congr rfl fun g hg => by
            obtain ⟨hgU, q, hq⟩ := ht g hg
            rw [map_mul, hfin _ ((finU E n).mul_mem hh hgU), hq, map_ratCast]
      _ = σ (∑ g ∈ t.support, t g * φ (h * g)) := (map_sum σ _ _).symm
      _ = σ (z * φ h) := by rw [e]
      _ = σ z * φ' h := by rw [map_mul, hfin h hh]
  have hon : Set.EqOn (opOf (RU E n) t φ') (σ z • φ') ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) := by
    rintro _ ⟨γ, hγ, g, hg, rfl⟩
    rw [hl1 γ hγ, hl2 γ hγ]
    exact hfinEq g hg
  exact Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hc1 hc2 hon

end GlobalTheory.EigenConj
