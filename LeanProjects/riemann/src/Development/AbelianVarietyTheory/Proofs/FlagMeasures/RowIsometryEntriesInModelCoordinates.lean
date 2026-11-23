import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

end GlobalTheory.SnMass.VolN

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
private lemma mul_vecMulVec_mul_flag_measures {n : Type} [Fintype n] (M N : Matrix n n ℂ) (u v : n → ℂ) :
    M * vecMulVec u v * N = vecMulVec (M *ᵥ u) (v ᵥ* N) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
private lemma single_vecMul_Hpk_eI (k r : ℕ) (a : Fin r) :
    Pi.single (_root_.Formalism.QuantumDeterminants.eI k r a) 1 ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r = Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) := by
  funext j
  rw [single_one_vecMul]
  change _root_.Formalism.QuantumDeterminants.Hpk k r (_root_.Formalism.QuantumDeterminants.eI k r a) j = (Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) : _ → ℂ) j
  unfold _root_.Formalism.QuantumDeterminants.Hpk _root_.Formalism.QuantumDeterminants.eI _root_.Formalism.QuantumDeterminants.esI
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  have ha := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in

theorem _root_.GlobalTheory.SnMass.VolN.rowE_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), _root_.GlobalTheory.SnMass.VolN.IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E) (w : InfinitePlace E) (i j : Fin (2 * r + k + 1)), _root_.GlobalTheory.SnMass.VolN.gM A (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t) w i j = (if i = j then 1 else 0) + (if j = _root_.Formalism.QuantumDeterminants.esI k r a then (s a : ℂ) * (((A w).mulVec fun l => w.embedding (y l)) i + (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * w.embedding t else 0)) else 0) - (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec j) ((A w).mulVec fun l => w.embedding (y l)) else 0) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD a y t w i j
  obtain ⟨hσ, -, hJ, -, -, -, -, hA, -, hAd⟩ := hD
  set x : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (P l a.castSucc) with hx_def
  set v : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (y l) with hv_def
  have hconj : ∀ z : E, w.embedding (σ z) = star (w.embedding z) := fun z => hσ.2.2.2 w.embedding z
  have hiso : (A w)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * A w = J.map w.embedding := hA w
  have hAx : A w *ᵥ x = (s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a) := (hAd w a).1
  have hdet : IsUnit (A w).det := by
    have h1 : (J.map w.embedding).det ≠ 0 := by
      rw [show (J.map w.embedding).det = w.embedding J.det from (RingHom.map_det _ _).symm]
      exact (map_ne_zero _).2 hJ.2
    rw [← hiso, det_mul, det_mul] at h1
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h1)
  have hinv : A w * (A w)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hrow : ∀ u : Fin (2 * r + k + 1) → ℂ,
      star u ᵥ* J.map w.embedding ᵥ* (A w)⁻¹ = star (A w *ᵥ u) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r := by
    intro u
    rw [← hiso, vecMul_vecMul, Matrix.mul_assoc, hinv, Matrix.mul_one, ← vecMul_vecMul,
      ← star_mulVec]
  have hmap : (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun l => P l a.castSucc) y t).map
      w.embedding = 1 + vecMulVec (v + w.embedding t • x) (star x ᵥ* J.map w.embedding) -
        vecMulVec x (star v ᵥ* J.map w.embedding) := by
    ext p q
    simp [_root_.GlobalTheory.SnMass.VolN.rowE, vecMulVec_apply, vecMul, dotProduct, map_sum, hconj,
      one_apply, x, v]
  unfold _root_.GlobalTheory.SnMass.VolN.gM
  rw [hmap, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one, hinv,
    mul_vecMulVec_mul_flag_measures, mul_vecMulVec_mul_flag_measures, hrow, hrow, mulVec_add, mulVec_smul, hAx]
  have hstar : star ((s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r =
      (s a : ℂ) • Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1 := by
    unfold _root_.Formalism.QuantumDeterminants.bvec
    rw [star_smul, ← Pi.single_star, star_one, smul_vecMul, single_vecMul_Hpk_eI, Complex.star_def,
      Complex.conj_ofReal]
  rw [hstar]
  unfold _root_.Formalism.QuantumDeterminants.herm _root_.Formalism.QuantumDeterminants.bvec
  rw [dotProduct_mulVec, dotProduct_single_one]
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, one_apply]
  split_ifs <;> ring
