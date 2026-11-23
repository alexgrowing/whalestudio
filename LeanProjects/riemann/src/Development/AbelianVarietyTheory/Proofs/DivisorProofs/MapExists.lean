import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubstStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Katz.ModHom

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem red_lift {σ : Type} (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := by
  intro α
  exact ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    simp [WittVector.constantCoeff_apply]⟩

def substW {σ τ : Type} [Finite σ] (u : σ → MvPowerSeries τ (Fr p k)) (hu : ∀ i, constantCoeff (u i) = 0) :
    MvPowerSeries σ (Fr p k) →ₗ[WittVector p k] MvPowerSeries τ (Fr p k) where
  toFun f := subst u f
  map_add' f g := subst_add (hasSubst_of_constantCoeff_zero hu) f g
  map_smul' r f := by
    rw [← algebraMap_smul (Fr p k) r f, subst_smul (hasSubst_of_constantCoeff_zero hu),
      algebraMap_smul]
    rfl

variable [PerfectRing k p]

def modMap {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν)
    {φ : Fin e → MvPowerSeries (Fin d) k} (hφ : IsHom μ ν φ) : Mod p hν →ₗ[WittVector p k] Mod p hμ :=
  Submodule.mapQ _ _
    (((substW p (fun j => Katz.lift p (φ j)) fun j => constantCoeff_lift p (hφ.const j)).comp
      (quasiLog p hν).subtype).codRestrict (quasiLog p hμ)
      fun f => (GlobalTheory.T.quasiLogarithm_pullback_teichmullerLift p k d e μ ν hμ hν φ hφ f.1 f.2).1)
    (by
      intro f hf
      rw [Submodule.mem_comap]
      change f.1 ∈ intBy p k (Fin e) 1 at hf
      change subst (fun j => Katz.lift p (φ j)) f.1 ∈ intBy p k (Fin d) 1
      exact (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e) (Fin d) _ φ (fun j => constantCoeff_lift p (hφ.const j))
        (fun j => red_lift p (φ j))).2 1 f.1 hf)

theorem modMap_mk {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν)
    {φ : Fin e → MvPowerSeries (Fin d) k} (hφ : IsHom μ ν φ) (f : quasiLog p hν) :
    ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧
      modMap p hμ hν hφ (Submodule.Quotient.mk f) = Submodule.Quotient.mk g :=
  ⟨_, rfl, rfl⟩

end GlobalTheory.Katz.ModHom

theorem GlobalTheory.Katz.ModHom.map_exists : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∃ m : Mod p hν →ₗ[WittVector p k] Mod p hμ, ∀ f : quasiLog p hν, ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧ m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ
  exact ⟨GlobalTheory.Katz.ModHom.modMap p hμ hν hφ, GlobalTheory.Katz.ModHom.modMap_mk p hμ hν hφ⟩
