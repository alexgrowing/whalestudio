import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.BCountable

noncomputable section

open NumberField MeasureTheory Set
open scoped NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem B_per {r : ℕ} {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ) (g : AdelicGLn.AdelicGL K n)
    (ξ : UPos n r → K) (x : UPos n r → 𝔸[K]) :
    φ (unipGL (fun i => algebraMap K 𝔸[K] (ξ i) + x i) * g) = φ (unipGL x * g) :=
  hφ.unipGL_vadd g ⟨fun p => algebraMap K 𝔸[K] (ξ p), ξ, rfl⟩ x

theorem constantTerm_unipGL_mul {r : ℕ} {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (Y : UPos n r → AdeleRing (𝓞 K) K) (g : AdelicGLn.AdelicGL K n) :
    constantTerm r φ (unipGL Y * g) = constantTerm r φ g := by
  rw [constantTerm_eq_integral, constantTerm_eq_integral]
  simp_rw [← mul_assoc, ← unipGL_add]
  exact B_translate (fun X => φ (unipGL X * g)) (fun ξ x => B_per hφ g ξ x) Y

theorem constantTermPar_eq_top {p q : ℕ} (hpq : p < q) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ)
    (g : AdelicGLn.AdelicGL K n) :
    constantTermPar {p, q} φ g = ∫ b, constantTerm q φ (parGL (joinPos (r := q) 0 b) * g)
      ∂(Measure.pi fun _ : {x : PPos n {p, q} // ¬ IsTop q x} => boxMeasure K) := by
  classical
  have hr : q ∈ ({p, q} : Finset ℕ) := by simp
  have hmax : ∀ s ∈ ({p, q} : Finset ℕ), ∀ i j : Fin n, (i : ℕ) < s → s ≤ (j : ℕ) → s ≤ q := by
    intro s hs i j _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    omega
  rw [constantTermPar_eq_integral,
    B_fubini (IsTop q) (fun X => φ (parGL X * g)) (hφ.comp (continuous_parGL.mul continuous_const))]
  congr 1
  funext b
  have e2 : ∀ a : {x : PPos n {p, q} // IsTop q x} → 𝔸[K],
      φ (parGL (fun i => if h : IsTop q i then a ⟨i, h⟩ else b ⟨i, h⟩) * g) =
      φ (unipGL (fun x => a ((topEquiv hr).symm x)) * (parGL (joinPos (r := q) 0 b) * g)) := by
    intro a
    rw [← mul_assoc, ← parGL_eq_unipGL_mul hr hmax a b]
    rfl
  simp_rw [e2]
  rw [← integral_box_reindex (topEquiv hr) (fun A => φ (unipGL A * (parGL (joinPos (r := q) 0 b) * g))),
    ← constantTerm_eq_integral]

section Bot

variable {p q : ℕ} {R : Type*} [CommRing R]

abbrev B_low (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) : Matrix (Fin n) (Fin n) R := parEntry (joinPos (r := p) 0 b)

theorem B_low_apply_ne (_hpq : p < q) (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) {i j : Fin n}
    (h : B_low b i j ≠ 0) : p ≤ (i : ℕ) ∧ (i : ℕ) < q ∧ q ≤ (j : ℕ) := by
  simp only [B_low, parEntry_apply, joinPos] at h
  split_ifs at h with h1 h2
  · exact absurd rfl h
  · obtain ⟨s, hs, h3, h4⟩ := h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    have h2' : ¬ ((i : ℕ) < p ∧ p ≤ (j : ℕ)) := h2
    rcases hs with rfl | rfl <;> omega
  · exact absurd rfl h

theorem B_low_mul_block (hpq : p < q) (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) (A : UPos n p → R) :
    B_low b * blockEntry A = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : B_low b i k = 0
  · rw [h, zero_mul]
  · have := B_low_apply_ne hpq b h
    rw [blockEntry_apply, dif_neg (by omega), mul_zero]

theorem B_low_mul_low (hpq : p < q) (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) : B_low b * B_low b = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : B_low b i k = 0
  · rw [h, zero_mul]
  · by_cases h' : B_low b k j = 0
    · rw [h', mul_zero]
    · have := B_low_apply_ne hpq b h
      have := B_low_apply_ne hpq b h'
      omega

theorem B_parEntry_join (_hpq : p < q) (a : {x : PPos n {p, q} // IsTop p x} → R)
    (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) :
    parEntry (joinPos a b) = B_low b + blockEntry (fun x => a ((topEquiv (S := {p, q}) (by simp)).symm x)) := by
  ext i j
  simp only [B_low, Matrix.add_apply, parEntry_apply, blockEntry_apply, joinPos]
  by_cases hP : ∃ s ∈ ({p, q} : Finset ℕ), (i : ℕ) < s ∧ s ≤ (j : ℕ)
  · rw [dif_pos hP, dif_pos hP]
    by_cases hT : (i : ℕ) < p ∧ p ≤ (j : ℕ)
    · have hT' : IsTop p (⟨(i, j), hP⟩ : PPos n {p, q}) := hT
      rw [dif_pos hT, dif_pos hT', dif_pos hT', Pi.zero_apply, zero_add]
      rfl
    · have hT' : ¬ IsTop p (⟨(i, j), hP⟩ : PPos n {p, q}) := hT
      rw [dif_neg hT, dif_neg hT', dif_neg hT', add_zero]
  · rw [dif_neg hP, dif_neg hP, zero_add, dif_neg]
    rintro hT
    exact hP ⟨p, by simp, hT⟩

theorem B_parGL_bot (hpq : p < q) (a : {x : PPos n {p, q} // IsTop p x} → R)
    (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) :
    parGL (joinPos a b) = parGL (joinPos 0 b) * unipGL (fun x => a ((topEquiv (S := {p, q}) (by simp)).symm x)) := by
  apply Units.ext
  simp only [Units.val_mul, coe_parGL, coe_unipGL]
  rw [parMatrix, parMatrix, unipMatrix, B_parEntry_join hpq a b,
    show parEntry (joinPos (r := p) 0 b) = B_low b from rfl]
  simp only [add_mul, mul_add, one_mul, mul_one, B_low_mul_block hpq, add_zero]
  abel

def B_ell (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) (A : UPos n p → R) : UPos n p → R :=
  fun x => (blockEntry A * B_low b) x.1.1 x.1.2

theorem B_block_sub (hpq : p < q) (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) (A : UPos n p → R) :
    blockEntry (A - B_ell b A) = blockEntry A - blockEntry A * B_low b := by
  ext i j
  rw [Matrix.sub_apply, blockEntry_apply, blockEntry_apply]
  split_ifs with h
  · rfl
  · rw [zero_sub, eq_comm, neg_eq_zero, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h' : B_low b k j = 0
    · rw [h', mul_zero]
    · have := B_low_apply_ne hpq b h'
      rw [blockEntry_apply, dif_neg (by omega), zero_mul]

theorem B_shear_mat (hpq : p < q) (b : {x : PPos n {p, q} // ¬ IsTop p x} → R) (A : UPos n p → R) :
    parGL (joinPos 0 b) * unipGL A = unipGL (A - B_ell b A) * parGL (joinPos 0 b) := by
  apply Units.ext
  simp only [Units.val_mul, coe_parGL, coe_unipGL]
  rw [parMatrix, unipMatrix, unipMatrix, B_block_sub hpq,
    show parEntry (joinPos (r := p) 0 b) = B_low b from rfl]
  have h1 := B_low_mul_block hpq b A
  have h2 := B_low_mul_low hpq b
  simp only [mul_add, add_mul, one_mul, mul_one, sub_mul, h1, add_zero, mul_assoc, h2, mul_zero, sub_zero]
  abel

end Bot

theorem constantTermPar_eq_bot {p q : ℕ} (hpq : p < q) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ)
    (hl : IsLeftInvariant φ) (g : AdelicGLn.AdelicGL K n) :
    constantTermPar {p, q} φ g = ∫ b, constantTerm p φ (parGL (joinPos (r := p) 0 b) * g)
      ∂(Measure.pi fun _ : {x : PPos n {p, q} // ¬ IsTop p x} => boxMeasure K) := by
  classical
  have hr : p ∈ ({p, q} : Finset ℕ) := by simp
  rw [constantTermPar_eq_integral,
    B_fubini (IsTop p) (fun X => φ (parGL X * g)) (hφ.comp (continuous_parGL.mul continuous_const))]
  congr 1
  funext b
  have e2 : ∀ a : {x : PPos n {p, q} // IsTop p x} → 𝔸[K],
      φ (parGL (fun i => if h : IsTop p i then a ⟨i, h⟩ else b ⟨i, h⟩) * g) =
      φ (parGL (joinPos (r := p) 0 b) * unipGL (fun x => a ((topEquiv hr).symm x)) * g) := by
    intro a
    rw [← B_parGL_bot hpq a b]
    rfl
  simp_rw [e2]
  rw [← integral_box_reindex (topEquiv hr) (fun A => φ (parGL (joinPos (r := p) 0 b) * unipGL A * g)),
    constantTerm_eq_integral]
  have e3 : ∀ A : UPos n p → 𝔸[K], φ (parGL (joinPos (r := p) 0 b) * unipGL A * g) =
      φ (unipGL (A - B_ell b A) * (parGL (joinPos (r := p) 0 b) * g)) := fun A => by
    rw [B_shear_mat hpq b, mul_assoc]
  simp_rw [e3]
  refine B_shear (fun x : UPos n p => q ≤ (x.1.2 : ℕ)) (fun A => φ (unipGL A * (parGL (joinPos (r := p) 0 b) * g)))
    (hφ.comp (continuous_unipGL.mul continuous_const)) (fun ξ x => B_per hl _ ξ x) (B_ell b) ?_ ?_ ?_
  · refine continuous_pi fun x => ?_
    have hb : Continuous fun A : UPos n p → 𝔸[K] => blockEntry A := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      show Continuous fun A : UPos n p → 𝔸[K] => (if h : (i : ℕ) < p ∧ p ≤ (j : ℕ) then A ⟨(i, j), h⟩ else 0)
      split_ifs
      · exact continuous_apply _
      · exact continuous_const
    exact (continuous_apply_apply x.1.1 x.1.2).comp (hb.matrix_mul continuous_const)
  · intro A x hx
    simp only [B_ell, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h' : B_low b k x.1.2 = 0
    · rw [h', mul_zero]
    · have := B_low_apply_ne hpq b h'
      exact absurd this.2.2 hx
  · intro A A' hA
    funext x
    simp only [B_ell, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h' : B_low b k x.1.2 = 0
    · rw [h', mul_zero, mul_zero]
    · have := B_low_apply_ne hpq b h'
      congr 1
      simp only [blockEntry_apply]
      split_ifs with h3
      · exact hA _ (by show ¬ (q ≤ (k : ℕ)); omega)
      · rfl

end PositivityTheory.Rg.Rs.SliceClasses

end
