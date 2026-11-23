import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfUnitV

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sigma_invol (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →ₐ[ℚ] ℂ := IsAlgClosed.lift
  apply τ.toRingHom.injective
  have h1 := hcm.2.2.2 τ.toRingHom (σ x)
  have h2 := hcm.2.2.2 τ.toRingHom x
  rw [h1, h2, star_star]

theorem sigR_invol (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul, sigma_invol σ hcm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]

theorem hR_conj (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  simp only [hR, hform, map_sum, map_mul, sigR_invol σ v hcm, JR, Matrix.map_apply, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def NormOne : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ u ∈ OEv (E := E) v, sigR (Fv F v) σ u = u →
    (∃ u' ∈ OEv (E := E) v, u * u' = 1) →
    ∃ l ∈ OEv (E := E) v, sigR (Fv F v) σ l * l * u = 1

def UnitNorm : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, ∃ u' ∈ OEv (E := E) v, hR (Fv F v) σ J p p * u' = 1

theorem unitV_of (hN : NormOne σ J ψ v) (hUN : UnitNorm σ J ψ v Λ) : UnitV σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨p, hp, u', hu'0, hu'⟩ := hUN hstd hL hsd hun ι X hX hUX hc
  have hcm := hstd.1
  have hJ := hstd.2.1.1
  have hu0 : hR (Fv F v) σ J p p ∈ OEv (E := E) v := (hsd p).1 hp.1 p hp.1
  obtain ⟨l, hl0, hl⟩ := hN hstd hun _ hu0 (hR_conj σ J v hcm hJ p p) ⟨u', hu'0, hu'⟩
  have hXl : ∀ i, hR (Fv F v) σ J (X i) (l • p) = 0 := by
    intro i
    rw [hR_smul_right, hp.2 i, mul_zero]
  refine ⟨l • p, ⟨oSmul v Λ hL l hl0 p hp.1, hXl⟩, ?_, ?_⟩
  · rw [hR_smul_left, hR_smul_right, ← mul_assoc]
    exact hl
  · intro i
    rw [← hR_conj σ J v hcm hJ, hXl i, map_zero]

theorem orbAll_of_norm (a : ℕ) (Y : TupV (E := E) v n a) (hN : NormOne σ J ψ v)
    (hUN : UnitNorm σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_unitV σ J ψ v Λ a Y (unitV_of σ J ψ v Λ hN hUN)

end PI.OmLocU.Orb
