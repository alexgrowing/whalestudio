import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem frameForm_symm_zero {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : Hᴴ = H)
    (x y : Fin N → ℂ) : star x ⬝ᵥ (H *ᵥ y) = star (star y ⬝ᵥ (H *ᵥ x)) := by
  rw [star_dotProduct, star_mulVec, hH, ← dotProduct_mulVec]

private theorem dotProduct_mulVec_sum_smul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} {ι : Type}
    [Fintype ι] (x : Fin N → ℂ) (g : ι → ℂ) (v : ι → Fin N → ℂ) :
    star x ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = ∑ i, g i * (star x ⬝ᵥ (H *ᵥ v i)) := by
  simp [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul]

theorem frame_orthogonal_eq_zero {N r k : ℕ} {H : Matrix (Fin N) (Fin N) ℂ}
    {e f : Fin r → Fin N → ℂ} {z : Fin N → ℂ} {w : Fin k → Fin N → ℂ}
    (hN : N = 2 * r + k + 1) (hH : Hᴴ = H)
    (hee : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) (hff : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0)
    (hef : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0)
    (hz : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0)
    (hzz : star z ⬝ᵥ (H *ᵥ z) ≠ 0)
    (hww : ∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0)
    (hw : ∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧
      star z ⬝ᵥ (H *ᵥ w a) = 0)
    (u : Fin N → ℂ) (hu : (∀ c, star (e c) ⬝ᵥ (H *ᵥ u) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ u) = 0) ∧
      star z ⬝ᵥ (H *ᵥ u) = 0) (huw : ∀ a, star (w a) ⬝ᵥ (H *ᵥ u) = 0) : u = 0 := by
  have sym := fun x y => frameForm_symm_zero hH x y
  have hfe : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ e b) = if a = b then 1 else 0 := by
    intro a b
    rw [sym, hef b a]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab, hab.symm]
  have hze : ∀ a, star z ⬝ᵥ (H *ᵥ e a) = 0 := fun a => by rw [sym, (hz a).1, star_zero]
  have hzf : ∀ a, star z ⬝ᵥ (H *ᵥ f a) = 0 := fun a => by rw [sym, (hz a).2, star_zero]
  have hwe : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ e c) = 0 := fun a c => by rw [sym, ((hw a).1 c).1, star_zero]
  have hwf : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ f c) = 0 := fun a c => by rw [sym, ((hw a).1 c).2, star_zero]
  have hwz : ∀ a, star (w a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => by rw [sym, (hw a).2, star_zero]
  have hew : ∀ c a, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).1
  have hfw : ∀ c a, star (f c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).2
  have hzw : ∀ a, star z ⬝ᵥ (H *ᵥ w a) = 0 := fun a => (hw a).2
  have hez : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).1
  have hfz : ∀ a, star (f a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).2
  set v : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → Fin N → ℂ :=
    Sum.elim (Sum.elim e f) (Sum.elim w fun _ => z) with hv
  have key : ∀ g : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → ℂ,
      (∀ j, star (v j) ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = 0) → g = 0 := by
    intro g hg
    simp only [dotProduct_mulVec_sum_smul] at hg
    simp only [Fintype.sum_sum_type] at hg
    funext i
    rcases i with ((a | a) | (a | u))
    · have := hg (.inl (.inr a))
      simpa [hv, hfe, hff, hwe, hfw, hfz, mul_ite] using this
    · have := hg (.inl (.inl a))
      simpa [hv, hee, hef, hew, hez, mul_ite] using this
    · have := hg (.inr (.inl a))
      simpa [hv, hwe, hwf, hww, hwz, mul_ite] using this
    · have := hg (.inr (.inr u))
      simpa [hv, hze, hzf, hzw, hzz] using this
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := key g (fun j => by rw [hg, mulVec_zero, dotProduct_zero])
    exact congrFun this i
  have hcard : Fintype.card ((Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit)) = Module.finrank ℂ (Fin N → ℂ) := by
    simp [hN]
    ring
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hu' : u ∈ Submodule.span ℂ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu'
  have hg0 := key g (fun j => by
    rw [hg]
    rcases j with ((a | a) | (a | _))
    · simpa [hv] using (hu.1 a).1
    · simpa [hv] using (hu.1 a).2
    · simpa [hv] using huw a
    · simpa [hv] using hu.2)
  rw [← hg, hg0]
  simp

theorem frame_complement_change_of_basis : ∀ (N r k n : ℕ) (h : k = n) (H : Matrix (Fin N) (Fin N) ℂ) (e f : Fin r → Fin N → ℂ) (z : Fin N → ℂ) (w : Fin k → Fin N → ℂ) (q : Fin n → Fin N → ℂ), N = 2 * r + k + 1 → Hᴴ = H → IsUnit H.det → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) → (∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0) → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0) → (∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0) → star z ⬝ᵥ (H *ᵥ z) ≠ 0 → (∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧ star z ⬝ᵥ (H *ᵥ w a) = 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ q a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ q a) = 0) ∧ star z ⬝ᵥ (H *ᵥ q a) = 0) → ∀ G : Matrix (Fin n) (Fin n) ℂ, (∀ a b, G a b = star (q a) ⬝ᵥ (H *ᵥ q b)) → IsUnit G.det → ∃ o : Matrix (Fin n) (Fin n) ℂ, IsUnit o.det ∧ oᴴ * G * o = 1 ∧ ∀ s : Matrix (Fin N) (Fin N) ℂ, sᴴ * H * s = H → (∀ a, s *ᵥ e a = e a ∧ s *ᵥ f a = f a) → s *ᵥ z = z → ∃ m ∈ Matrix.unitaryGroup (Fin n) ℂ, m.submatrix (Fin.cast h) (Fin.cast h) = (Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b))) ∧ G⁻¹ * (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = o * m * o⁻¹ := by
  intro N r k n h H e f z w q hN hH _hdet hee hff hef hz hzz hww hw hq G hG hGdet
  subst h
  have sym := fun x y => frameForm_symm_zero hH x y
  have expand : ∀ x : Fin N → ℂ, ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧
      star z ⬝ᵥ (H *ᵥ x) = 0) → x = ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a := by
    intro x hx
    have h0 := frame_orthogonal_eq_zero hN hH hee hff hef hz hzz hww hw
      (x - ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a) ?_ ?_
    · exact sub_eq_zero.mp h0
    · refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).1, fun a => ((hw a).1 c).1]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).2, fun a => ((hw a).1 c).2]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hx.2, fun a => (hw a).2]
    · intro a
      simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hww, mul_ite]
  have parseval : ∀ x y : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ y) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ y) = 0) ∧ star z ⬝ᵥ (H *ᵥ y) = 0) →
      star x ⬝ᵥ (H *ᵥ y) = ∑ c, star (star (w c) ⬝ᵥ (H *ᵥ x)) * (star (w c) ⬝ᵥ (H *ᵥ y)) := by
    intro x y hy
    conv_lhs => rw [expand y hy]
    rw [dotProduct_mulVec_sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sym x (w c), mul_comm]
  set P := Matrix.of fun c b => star (w c) ⬝ᵥ (H *ᵥ q b) with hPdef
  have hGP : G = Pᴴ * P := by
    ext a b
    rw [hG, parseval (q a) (q b) (hq b), Matrix.mul_apply]
    simp [hPdef, Matrix.conjTranspose_apply]
  have hP : IsUnit P.det := by
    rw [hGP, Matrix.det_mul, Matrix.det_conjTranspose] at hGdet
    exact isUnit_of_mul_isUnit_right hGdet
  have hPh : IsUnit Pᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hP.star
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det _ hP, ?_, ?_⟩
  · rw [hGP, Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Pᴴ)⁻¹,
      Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_nonsing_inv _ hP]
  intro s hs hfix hzfix
  have pres : ∀ x y : Fin N → ℂ, star (s *ᵥ x) ⬝ᵥ (H *ᵥ (s *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hs]
  have sperp : ∀ x : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧ star z ⬝ᵥ (H *ᵥ x) = 0) →
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) ∧
        star z ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) := by
    intro x hx
    refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
    · rw [← (hfix c).1, pres]; exact (hx.1 c).1
    · rw [← (hfix c).2, pres]; exact (hx.1 c).2
    · rw [← hzfix, pres]; exact hx.2
  set M := Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b)) with hMdef
  refine ⟨M, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply, ← hww a b, ← pres (w a) (w b),
      parseval _ _ (sperp _ (hw b))]
    simp [hMdef, Matrix.conjTranspose_apply]
  · ext a b
    simp [hMdef]
  · have hQ : (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = Pᴴ * (M * P) := by
      ext a b
      have hsq : s *ᵥ q b = ∑ d, P d b • (s *ᵥ w d) := by
        conv_lhs => rw [expand (q b) (hq b)]
        rw [mulVec_sum]
        simp [mulVec_smul, hPdef]
      rw [Matrix.of_apply, parseval _ _ (sperp _ (hq b)), Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hsq, dotProduct_mulVec_sum_smul, Matrix.mul_apply]
      simp [hPdef, hMdef, Matrix.conjTranspose_apply, mul_comm]
    rw [hQ, hGP, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Pᴴ)⁻¹, Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_assoc]

end GlobalTheory
