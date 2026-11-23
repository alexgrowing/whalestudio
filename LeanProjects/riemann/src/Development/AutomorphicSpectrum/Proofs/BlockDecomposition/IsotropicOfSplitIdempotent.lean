import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.IsoSplit

theorem hform_comb {R : Type} [CommRing R] {n : Type} [Fintype n] (c : R →+* R) (Jm : Matrix n n R)
    (a b a' b' : n → R) (s t p q : R) :
    Formalism.UG.hform c Jm (s • a + t • b) (p • a' + q • b') =
      c s * p * Formalism.UG.hform c Jm a a' + c s * q * Formalism.UG.hform c Jm a b' +
        c t * p * Formalism.UG.hform c Jm b a' + c t * q * Formalism.UG.hform c Jm b b' := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hR_incV (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (p q : Fin M → E) :
    hR K σ J (incV K p) (incV K q) = inclR K (hf σ J p q) := by
  have hs : ∀ t : E, sigR K σ (inclR K t) = inclR K (σ t) := by
    intro t
    simp [sigR, inclR]
  simp only [hR, Formalism.UG.hform, hf, incV, JR, Matrix.map_apply, map_sum, map_mul, hs]

theorem hf_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (p q : Fin M → E) (s : E) :
    hf σ J p (s • q) = s * hf σ J p q := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_orthogonal_pair [NumberField E] (σ : E →ₐ[F] E) (hσ : ∀ t, σ (σ t) = t) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hM : 2 ≤ M) (hJ : IsHermND σ J) :
    ∃ x y : Fin M → E, hf σ J x x ≠ 0 ∧ hf σ J y y ≠ 0 ∧ hf σ J x y = 0 ∧ hf σ J y x = 0 := by
  obtain ⟨P, d, -, hPd, -, hd⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hσ
    (G := J.transpose) (fun a b => hJ.1 a b)
  have hd' := hd (by rw [Matrix.det_transpose]; exact hJ.2)
  have key : ∀ a b, hf σ J (fun k => P k b) (fun k => P k a) = Matrix.diagonal d a b := by
    intro a b
    rw [← hPd]
    simp only [hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
    ring
  have hij : (⟨0, by omega⟩ : Fin M) ≠ ⟨1, by omega⟩ := by simp
  refine ⟨fun k => P k ⟨0, by omega⟩, fun k => P k ⟨1, by omega⟩, ?_, ?_, ?_, ?_⟩
  · rw [key, Matrix.diagonal_apply_eq]; exact hd' _
  · rw [key, Matrix.diagonal_apply_eq]; exact hd' _
  · rw [key, Matrix.diagonal_apply_ne _ hij.symm]
  · rw [key, Matrix.diagonal_apply_ne _ hij]

theorem isoAt_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → IsoAt K σ J := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ K _ _ e he hsum hprod
  have hσ : ∀ t, σ (σ t) = t := by
    intro t
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]
  obtain ⟨x, y, hx, hy, hxy, hyx⟩ := exists_orthogonal_pair σ hσ J hM hJ
  set c := sigR K σ with hc
  have hcc : c (c e) = e := by
    have h := congrArg c hsum
    rw [map_add, map_one] at h
    linear_combination h - hsum
  have hce : c e * c e = c e := by rw [← map_mul, he]
  refine ⟨e • incV K x + c e • incV K y,
    e • incV K ((hf σ J y y)⁻¹ • y) + c e • incV K ((hf σ J x x)⁻¹ • x), ?_, ?_⟩
  · change Formalism.UG.hform (sigR K σ) (JR K J) _ _ = 0
    rw [hform_comb]
    change c e * e * hR K σ J _ _ + c e * c e * hR K σ J _ _ + c (c e) * e * hR K σ J _ _ +
      c (c e) * c e * hR K σ J _ _ = 0
    simp only [hR_incV, hxy, hyx, map_zero, hcc]
    linear_combination (inclR K (hf σ J x x) + inclR K (hf σ J y y)) * hprod
  · change Formalism.UG.hform (sigR K σ) (JR K J) _ _ = 1
    rw [hform_comb]
    change c e * e * hR K σ J _ _ + c e * c e * hR K σ J _ _ + c (c e) * e * hR K σ J _ _ +
      c (c e) * c e * hR K σ J _ _ = 1
    simp only [hR_incV, hf_smul_right, hxy, hyx, mul_zero, map_zero, hcc, inv_mul_cancel₀ hx,
      inv_mul_cancel₀ hy, map_one]
    linear_combination he + hce + hsum

end GlobalTheory.CompanionTheory.SaGen.IsoSplit
