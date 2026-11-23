import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.HomConjDet

section General

variable {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

theorem det_eq_of_equiv (e : U ≃ₗ[ℂ] V) (φ : U →ₗ[ℂ] U) (ψ : V →ₗ[ℂ] V)
    (h : ∀ x, e (φ x) = ψ (e x)) : LinearMap.det φ = LinearMap.det ψ := by
  rw [← LinearMap.det_conj φ e]
  congr 1
  ext y
  simp [h]

variable [Module.Finite ℂ U] [Module.Finite ℂ V]

theorem det_comp_left (α : V →ₗ[ℂ] V) :
    LinearMap.det (LinearMap.llcomp ℂ U V V α : (U →ₗ[ℂ] V) →ₗ[ℂ] (U →ₗ[ℂ] V)) = LinearMap.det α ^ Module.finrank ℂ U := by
  let b := Module.finBasis ℂ U
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ U) => α)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  symm
  refine det_eq_of_equiv (b.constr ℂ) _ _ fun x => ?_
  refine b.ext fun i => ?_
  simp

theorem det_comp_right (β : U →ₗ[ℂ] U) :
    LinearMap.det (LinearMap.lcomp ℂ V β) = LinearMap.det β ^ Module.finrank ℂ V := by
  let b := Module.finBasis ℂ V
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ V) => β.dualMap)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, LinearMap.det_dualMap] at h
  rw [← h]
  symm
  refine det_eq_of_equiv ((LinearEquiv.linearMapPi ℂ).trans (LinearEquiv.congrRight b.equivFun.symm))
    _ _ fun x => ?_
  ext y
  simp [LinearEquiv.congrRight]

end General

variable {n : ℕ}

def homMat (P Q : Submodule ℂ (Fin n → ℂ)) :
    (((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrix' : ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
    LinearMap.llcomp ℂ _ _ _ Q.subtype ∘ₗ LinearMap.lcomp ℂ Q P.mkQ

theorem homMat_mulVec (P Q : Submodule ℂ (Fin n → ℂ)) (T : ((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) (y : Fin n → ℂ) :
    homMat P Q T *ᵥ y = (T (P.mkQ y) : Fin n → ℂ) := by
  simp [homMat, LinearMap.toMatrix'_mulVec]

theorem homMat_injective (P Q : Submodule ℂ (Fin n → ℂ)) : Function.Injective (homMat P Q) := by
  intro S T h
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := P.mkQ_surjective x
  apply Subtype.ext
  rw [← homMat_mulVec, ← homMat_mulVec, h]

theorem range_homMat (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) : LinearMap.range (homMat P Q) = H := by
  ext X
  rw [hH]
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨fun y hy => ?_, fun y => ?_⟩
    · rw [homMat_mulVec, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hy]
      simp
    · rw [homMat_mulVec]
      exact Subtype.property _
  · rintro ⟨h1, h2⟩
    refine ⟨P.liftQ ((Matrix.toLin' X).codRestrict Q fun y => by simpa using h2 y) ?_, ?_⟩
    · intro y hy
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simpa using h1 y hy
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun y => ?_
      rw [Matrix.toLin'_apply, homMat_mulVec]
      simp

theorem det_conj_hom : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) → (∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) → Module.finrank ℂ H = (n - Module.finrank ℂ P) * Module.finrank ℂ Q ∧ ∀ φ : H →ₗ[ℂ] H, (∀ X : H, ((φ X : H) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = detOn f Q ^ (n - Module.finrank ℂ P) * detOn f P ^ Module.finrank ℂ Q := by
  intro n f g P Q H hfg hdet hP hQ hH
  obtain rfl := range_homMat P Q H hH
  let e := LinearEquiv.ofInjective _ (homMat_injective P Q)
  have hq : Module.finrank ℂ ((Fin n → ℂ) ⧸ P) = n - Module.finrank ℂ P := by
    have := P.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at this
    omega
  refine ⟨?_, fun φ hφ => ?_⟩
  · rw [← e.finrank_eq, Module.finrank_linearMap, hq]
  have hgf : g * f = 1 := mul_eq_one_comm.1 hfg
  have hgP := GlobalTheory.FlagLeviGroup.inv_keeps hgf P hP
  have hP' : ∀ y ∈ P, Matrix.toLin' f y ∈ P := fun y hy => by simpa using hP y hy
  have hQ' : ∀ y ∈ Q, Matrix.toLin' f y ∈ Q := fun y hy => by simpa using hQ y hy
  have hgP' : P ≤ P.comap (Matrix.toLin' g) := fun y hy => by simpa using hgP y hy
  set α := (Matrix.toLin' f).restrict hQ' with hα
  set β := P.mapQ P (Matrix.toLin' g) hgP' with hβ
  have h1 : LinearMap.det (LinearMap.llcomp ℂ _ _ _ α ∘ₗ LinearMap.lcomp ℂ Q β) = LinearMap.det φ := by
    refine det_eq_of_equiv e _ _ fun T => ?_
    apply Subtype.ext
    rw [hφ]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    simp only [Matrix.toLin'_apply, e, LinearEquiv.ofInjective_apply, ← Matrix.mulVec_mulVec,
      homMat_mulVec]
    simp [hα, hβ, LinearMap.restrict_apply]
  have h2 := LinearMap.det_eq_det_mul_det P (Matrix.toLin' g) hgP'
  have h3 : LinearMap.det ((Matrix.toLin' f).restrict hP') *
      LinearMap.det ((Matrix.toLin' g).restrict hgP') = 1 := by
    rw [← map_mul, ← LinearMap.det_id (A := ℂ) (M := P)]
    congr 1
    refine LinearMap.ext fun y => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec, hfg]
  have h4 : ‖g.det‖ = 1 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => ‖M.det‖) hfg
    simpa [hdet] using this
  have h5 : LinearMap.det β = LinearMap.det ((Matrix.toLin' f).restrict hP') * g.det := by
    rw [← LinearMap.det_toLin' g, h2, ← mul_assoc, h3, one_mul]
  rw [← h1, LinearMap.det_comp, det_comp_left, det_comp_right, hq, h5, detOn, detOn, dif_pos hP',
    dif_pos hQ']
  simp [h4, hα]

end GlobalTheory.HomConjDet
