import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConjAdapted

section Pattern

variable {R : Type*} [Ring R] {n m : ℕ} {G W : Matrix (Fin n) (Fin n) R}

def Outer (m : ℕ) (i : Fin n) : Prop := i.val < m ∨ n ≤ i.val + m

structure GramShape (m : ℕ) (G : Matrix (Fin n) (Fin n) R) : Prop where
  out : ∀ i b : Fin n, Outer m i → G i b ≠ 0 → i.val + b.val + 1 = n
  mid : ∀ i b : Fin n, ¬ Outer m i → G i b ≠ 0 → ¬ Outer m b
  one : ∀ i b : Fin n, Outer m i → i.val + b.val + 1 = n → G i b = 1

example : GramShape 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) where
  out i b _ h := by
    fin_cases i <;> fin_cases b <;> simp_all
  mid i b hi _ := by
    exact absurd (by fin_cases i <;> simp [Outer]) hi
  one i b _ h := by
    fin_cases i <;> fin_cases b <;> simp_all

theorem rev_outer (i : Fin n) (hi : Outer m i) (h2 : 2 * m ≤ n) : Outer m (Fin.rev i) := by
  have hil := i.isLt
  unfold Outer at hi ⊢
  rw [Fin.val_rev]
  omega

theorem inv_row (h2 : 2 * m ≤ n) (hG : GramShape m G) (hGW : G * W = 1) (a q : Fin n) (ha : Outer m a)
    (hne : W a q ≠ 0) : a.val + q.val + 1 = n := by
  have hal := a.isLt
  have hout := rev_outer a ha h2
  have hra : (Fin.rev a).val + a.val + 1 = n := by rw [Fin.val_rev]; omega
  have key : (G * W) (Fin.rev a) q = W a q := by
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hG.one _ _ hout hra, one_mul]
    · intro b _ hb
      have hz : G (Fin.rev a) b = 0 := by
        by_contra hc
        have h3 := hG.out _ _ hout hc
        apply hb
        apply Fin.ext
        rw [Fin.val_rev] at h3
        omega
      rw [hz, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hGW] at key
  rw [← key] at hne
  by_contra hcon
  apply hne
  apply Matrix.one_apply_ne
  intro h
  apply hcon
  rw [← h, Fin.val_rev]
  omega

theorem inv_col (h2 : 2 * m ≤ n) (hG : GramShape m G) (hWG : W * G = 1) (a q : Fin n) (hq : Outer m q)
    (hne : W a q ≠ 0) : a.val + q.val + 1 = n := by
  have hql := q.isLt
  have hout := rev_outer q hq h2
  have hrq : q.val + (Fin.rev q).val + 1 = n := by rw [Fin.val_rev]; omega
  have key : (W * G) a (Fin.rev q) = W a q := by
    rw [Matrix.mul_apply, Finset.sum_eq_single q]
    · rw [hG.one _ _ hq hrq, mul_one]
    · intro b _ hb
      have hz : G b (Fin.rev q) = 0 := by
        by_contra hc
        by_cases hbo : Outer m b
        · have h3 := hG.out _ _ hbo hc
          apply hb
          apply Fin.ext
          rw [Fin.val_rev] at h3
          omega
        · exact hG.mid _ _ hbo hc hout
      rw [hz, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ q) h
  rw [hWG] at key
  rw [← key] at hne
  by_contra hcon
  apply hne
  apply Matrix.one_apply_ne
  intro h
  apply hcon
  rw [h, Fin.val_rev]
  omega

theorem cut_core {l d : ℕ} (hlm : l + d ≤ m) (h2 : 2 * m ≤ n) (hG : GramShape m G) (hGW : G * W = 1) (hWG : W * G = 1)
    (p q a b : Fin n) (hpq : ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = n ∨ e + l = n) ∧ p.val < e ∧ e ≤ q.val)
    (hne : W a q * G p b ≠ 0) :
    ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = n ∨ e + l = n) ∧ a.val < e ∧ e ≤ b.val := by
  obtain ⟨e, he, hpe, heq⟩ := hpq
  have hWne : W a q ≠ 0 := left_ne_zero_of_mul hne
  have hGne : G p b ≠ 0 := right_ne_zero_of_mul hne
  have hql := q.isLt
  refine ⟨n - e, ?_, ?_, ?_⟩
  · omega
  · by_cases hq : Outer m q
    · have h3 := inv_col h2 hG hWG a q hq hWne
      omega
    · have ha : ¬ Outer m a := fun ha => hq (by
        have h3 := inv_row h2 hG hGW a q ha hWne
        unfold Outer at ha ⊢
        omega)
      unfold Outer at hq ha
      omega
  · by_cases hp : Outer m p
    · have h3 := hG.out p b hp hGne
      omega
    · have hb : ¬ Outer m b := hG.mid p b hp hGne
      unfold Outer at hp hb
      omega

end Pattern

section Gram

variable {n m : ℕ} {H P : Matrix (Fin n) (Fin n) ℂ} {Xc Yc : Matrix (Fin n) (Fin m) ℂ}

private theorem conjTranspose_mul_mul_apply_eq_of_col_eq {u v w : ℕ} {Q : Matrix (Fin u) (Fin u) ℂ} {Z : Matrix (Fin u) (Fin v) ℂ}
    (K : Matrix (Fin u) (Fin u) ℂ) (N : Matrix (Fin u) (Fin w) ℂ) (i : Fin u) (j : Fin v)
    (h : ∀ k, Q k i = Z k j) (b : Fin w) : (Qᴴ * K * N) i b = (Zᴴ * K * N) j b := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h]

private theorem col_lemma_2 {u v r : ℕ} {Q : Matrix (Fin u) (Fin u) ℂ} {Z : Matrix (Fin u) (Fin v) ℂ}
    (M : Matrix (Fin r) (Fin u) ℂ) (b : Fin u) (j : Fin v) (h : ∀ k, Q k b = Z k j) (i : Fin r) :
    (M * Q) i b = (M * Z) i j := by
  simp only [Matrix.mul_apply, h]

private theorem conjTranspose_mul_mul_apply_eq_zero_of_mulVec {u v : ℕ} {K Q : Matrix (Fin u) (Fin u) ℂ} {Z : Matrix (Fin u) (Fin v) ℂ} (i : Fin u)
    (h : (Zᴴ * K) *ᵥ (fun k => Q k i) = 0) (j : Fin v) : (Zᴴ * K * Q) j i = 0 := by
  have h3 := congrFun h j
  rw [Matrix.mul_apply]
  exact h3

theorem gramShape (hH : Hᴴ = H) (hxx : Xcᴴ * H * Xc = 0) (hyy : Ycᴴ * H * Yc = 0) (hxy : Xcᴴ * H * Yc = 1) (h2 : 2 * m ≤ n)
    (colX : ∀ (i : Fin n) (j : Fin m), i.val = j.val → ∀ k, P k i = Xc k j)
    (columnBlock : ∀ (i : Fin n) (j : Fin m), i.val + j.val + 1 = n → ∀ k, P k i = Yc k j)
    (perpX : ∀ i : Fin n, m ≤ i.val → i.val + m < n → (Xcᴴ * H) *ᵥ (fun k => P k i) = 0)
    (perpY : ∀ i : Fin n, m ≤ i.val → i.val + m < n → (Ycᴴ * H) *ᵥ (fun k => P k i) = 0) :
    GramShape m (Pᴴ * H * P) := by
  have hyx : Ycᴴ * H * Xc = 1 := by
    have h3 := congrArg Matrix.conjTranspose hxy
    simpa [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc] using h3
  have hGs : ∀ i b : Fin n, (Pᴴ * H * P) i b = star ((Pᴴ * H * P) b i) := by
    intro i b
    have hA : (Pᴴ * H * P)ᴴ = Pᴴ * H * P := by
      simp [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc]
    have h3 := congrFun (congrFun hA i) b
    rw [Matrix.conjTranspose_apply] at h3
    exact h3.symm
  have hrow : ∀ i b : Fin n, Outer m i →
      (Pᴴ * H * P) i b = if i.val + b.val + 1 = n then 1 else 0 := by
    intro i b hi
    have hil := i.isLt
    have hbl := b.isLt
    rcases (show i.val < m ∨ n ≤ i.val + m from hi) with hi | hi
    · rw [conjTranspose_mul_mul_apply_eq_of_col_eq H P i ⟨i.val, hi⟩ (colX i ⟨i.val, hi⟩ rfl) b]
      by_cases hb1 : b.val < m
      · rw [col_lemma_2 (Xcᴴ * H) b ⟨b.val, hb1⟩ (colX b ⟨b.val, hb1⟩ rfl), hxx, Matrix.zero_apply,
          if_neg (show ¬ (i.val + b.val + 1 = n) by omega)]
      · by_cases hb2 : n ≤ b.val + m
        · have hj : n - 1 - b.val < m := by omega
          rw [col_lemma_2 (Xcᴴ * H) b ⟨n - 1 - b.val, hj⟩
            (columnBlock b ⟨n - 1 - b.val, hj⟩ (show b.val + (n - 1 - b.val) + 1 = n by omega)), hxy, Matrix.one_apply]
          by_cases hc : i.val + b.val + 1 = n
          · rw [if_pos hc, if_pos (Fin.ext (show i.val = n - 1 - b.val by omega))]
          · rw [if_neg hc, if_neg (fun h => hc (by have h4 := Fin.mk.inj h; omega))]
        · rw [conjTranspose_mul_mul_apply_eq_zero_of_mulVec b (perpX b (by omega) (by omega)), if_neg (show ¬ (i.val + b.val + 1 = n) by omega)]
    · have hj : n - 1 - i.val < m := by omega
      rw [conjTranspose_mul_mul_apply_eq_of_col_eq H P i ⟨n - 1 - i.val, hj⟩
        (columnBlock i ⟨n - 1 - i.val, hj⟩ (show i.val + (n - 1 - i.val) + 1 = n by omega)) b]
      by_cases hb1 : b.val < m
      · rw [col_lemma_2 (Ycᴴ * H) b ⟨b.val, hb1⟩ (colX b ⟨b.val, hb1⟩ rfl), hyx, Matrix.one_apply]
        by_cases hc : i.val + b.val + 1 = n
        · rw [if_pos hc, if_pos (Fin.ext (show n - 1 - i.val = b.val by omega))]
        · rw [if_neg hc, if_neg (fun h => hc (by have h4 := Fin.mk.inj h; omega))]
      · by_cases hb2 : n ≤ b.val + m
        · have hj2 : n - 1 - b.val < m := by omega
          rw [col_lemma_2 (Ycᴴ * H) b ⟨n - 1 - b.val, hj2⟩
            (columnBlock b ⟨n - 1 - b.val, hj2⟩ (show b.val + (n - 1 - b.val) + 1 = n by omega)), hyy, Matrix.zero_apply,
            if_neg (show ¬ (i.val + b.val + 1 = n) by omega)]
        · rw [conjTranspose_mul_mul_apply_eq_zero_of_mulVec b (perpY b (by omega) (by omega)), if_neg (show ¬ (i.val + b.val + 1 = n) by omega)]
  refine ⟨?_, ?_, ?_⟩
  · intro i b hi hne
    rw [hrow i b hi] at hne
    by_contra hc
    exact hne (if_neg hc)
  · intro i b hi hne hb
    apply hne
    rw [hGs i b, hrow b i hb, if_neg (show ¬ (b.val + i.val + 1 = n) by unfold Outer at hi hb; omega), star_zero]
  · intro i b hi hc
    rw [hrow i b hi, if_pos hc]

private theorem valuation_single_one_le_one {u : ℕ} (A B : Matrix (Fin u) (Fin u) ℂ) (q p a b : Fin u) :
    (A * Matrix.single q p (1 : ℂ) * B : Matrix (Fin u) (Fin u) ℂ) a b = A a q * B p b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [Matrix.mul_apply, Finset.sum_eq_single q]
    · simp [Matrix.single_apply]
    · intro y _ hy
      simp [Matrix.single_apply, Ne.symm hy]
    · intro h
      exact absurd (Finset.mem_univ q) h
  · intro x _ hx
    rw [Matrix.mul_apply]
    simp [Matrix.single_apply, Ne.symm hx]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem conj_entry (H P : Matrix (Fin n) (Fin n) ℂ) (p q a b : Fin n) :
    (P⁻¹ * (-(H⁻¹ * (P * Matrix.single p q 1 * P⁻¹)ᴴ * H)) * P : Matrix (Fin n) (Fin n) ℂ) a b =
      -((P⁻¹ * H⁻¹ * (P⁻¹)ᴴ) a q * (Pᴴ * H * P) p b) := by
  have hS : (Matrix.single p q (1 : ℂ))ᴴ = Matrix.single q p 1 := by
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : p = y <;> by_cases h2 : q = x <;> simp [h1, h2]
  have e2 : P⁻¹ * (-(H⁻¹ * (P * Matrix.single p q 1 * P⁻¹)ᴴ * H)) * P
      = -((P⁻¹ * H⁻¹ * (P⁻¹)ᴴ) * Matrix.single q p 1 * (Pᴴ * H * P)) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [e2, Matrix.neg_apply, valuation_single_one_le_one]

end Gram

theorem conj_strict : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ l d : ℕ, l + d ≤ m →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C →
    ∀ (τ : D.what₂.Tau) (p q a b : Fin V.rank),
    (∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ p.val < e ∧ e ≤ q.val) →
    ((C.1.map (tauE D τ))⁻¹ * conjAt V τ (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) *
      C.1.map (tauE D τ)) a b ≠ 0 →
      ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val := by
  intro D V m X Y hW l d hlm C hA τ p q a b hpq hne
  have hsig : ∀ x : D.host.E, tauE D τ (D.sp.cm.sig x) = star (tauE D τ x) :=
    fun x => GlobalTheory.FockCompare.tauE_star τ x
  have hcT : ∀ {r : ℕ} (M : Matrix (Fin V.rank) (Fin r) D.host.E),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M).map (tauE D τ) = (M.map (tauE D τ))ᴴ := by
    intro r M
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact hsig (M j i)
  have hgram : ∀ i j, star (V.gram j i) = V.gram i j := fun i j => (Formalism.BasicNotions.HSpace.herm V).eq _ _
  have hH : (gramAt D V τ)ᴴ = gramAt D V τ := by
    ext i j
    simp only [Formalism.BasicNotions.TH.gramAt, Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hgram i j]
    exact (GlobalTheory.FockCompare.tauE_star τ _).symm
  have hdetJ : V.gram.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hz0
    apply hW.aniso z
    · rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    · rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    · simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, mul_assoc, ← Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i _
      have h3 := congrFun hz i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h3
      rw [h3, mul_zero]
  have hdetH : (gramAt D V τ).det ≠ 0 := by
    have h3 := RingHom.map_det (tauE D τ) V.gram
    rw [RingHom.mapMatrix_apply] at h3
    simp only [Formalism.BasicNotions.TH.gramAt]
    rw [← h3]
    exact (map_ne_zero _).mpr hdetJ
  have hmap : ∀ {r s : ℕ} (A : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin s) D.host.E),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).map (tauE D τ) =
        (A.map (tauE D τ))ᴴ * gramAt D V τ * B.map (tauE D τ) := by
    intro r s A B
    rw [Matrix.map_mul, Matrix.map_mul, hcT]
    rfl
  have hxx : (X.map (tauE D τ))ᴴ * gramAt D V τ * X.map (tauE D τ) = 0 := by
    rw [← hmap, hW.xx]
    exact Matrix.map_zero _ (map_zero _)
  have hyy : (Y.map (tauE D τ))ᴴ * gramAt D V τ * Y.map (tauE D τ) = 0 := by
    rw [← hmap, hW.yy]
    exact Matrix.map_zero _ (map_zero _)
  have hxy : (X.map (tauE D τ))ᴴ * gramAt D V τ * Y.map (tauE D τ) = 1 := by
    rw [← hmap, hW.xy]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hperp : ∀ {r : ℕ} (Z : Matrix (Fin V.rank) (Fin r) D.host.E) (i : Fin V.rank),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram) *ᵥ (fun k => C.1 k i) = 0 →
      ((Z.map (tauE D τ))ᴴ * gramAt D V τ) *ᵥ (fun k => (C.1.map (tauE D τ)) k i) = 0 := by
    intro r Z i h
    funext j
    have h3 := congrArg (tauE D τ) (congrFun h j)
    rw [RingHom.map_mulVec, Pi.zero_apply, map_zero, Matrix.map_mul, hcT] at h3
    exact h3
  have hGS := gramShape (H := gramAt D V τ) (P := C.1.map (tauE D τ)) (Xc := X.map (tauE D τ))
    (Yc := Y.map (tauE D τ)) hH hxx hyy hxy hA.le
    (fun i j h k => by simp only [Matrix.map_apply, hA.colX i j h k])
    (fun i j h k => by simp only [Matrix.map_apply, hA.columnBlock i j h k])
    (fun i h1 h2 => hperp X i (hA.perpX i h1 h2))
    (fun i h1 h2 => hperp Y i (hA.perpY i h1 h2))
  have hPQ : C.1.map (tauE D τ) * (C⁻¹).1.map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hQP : (C⁻¹).1.map (tauE D τ) * C.1.map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hPinv : (C.1.map (tauE D τ))⁻¹ = (C⁻¹).1.map (tauE D τ) := Matrix.inv_eq_right_inv hPQ
  have hPi1 : C.1.map (tauE D τ) * (C.1.map (tauE D τ))⁻¹ = 1 := by rw [hPinv]; exact hPQ
  have hPi2 : (C.1.map (tauE D τ))⁻¹ * C.1.map (tauE D τ) = 1 := by rw [hPinv]; exact hQP
  have hHu : IsUnit (gramAt D V τ).det := isUnit_iff_ne_zero.mpr hdetH
  have hHi1 : gramAt D V τ * (gramAt D V τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hHu
  have hHi2 : (gramAt D V τ)⁻¹ * gramAt D V τ = 1 := Matrix.nonsing_inv_mul _ hHu
  have hGW : ((C.1.map (tauE D τ))ᴴ * gramAt D V τ * C.1.map (tauE D τ)) *
      ((C.1.map (tauE D τ))⁻¹ * (gramAt D V τ)⁻¹ * ((C.1.map (tauE D τ))⁻¹)ᴴ) = 1 := by
    calc _ = (C.1.map (tauE D τ))ᴴ * (gramAt D V τ * ((C.1.map (tauE D τ) * (C.1.map (tauE D τ))⁻¹) *
          ((gramAt D V τ)⁻¹ * ((C.1.map (tauE D τ))⁻¹)ᴴ))) := by simp only [Matrix.mul_assoc]
      _ = (C.1.map (tauE D τ))ᴴ * ((C.1.map (tauE D τ))⁻¹)ᴴ := by
          rw [hPi1, Matrix.one_mul, ← Matrix.mul_assoc (gramAt D V τ), hHi1, Matrix.one_mul]
      _ = 1 := by rw [← Matrix.conjTranspose_mul, hPi2, Matrix.conjTranspose_one]
  have hWG : ((C.1.map (tauE D τ))⁻¹ * (gramAt D V τ)⁻¹ * ((C.1.map (tauE D τ))⁻¹)ᴴ) *
      ((C.1.map (tauE D τ))ᴴ * gramAt D V τ * C.1.map (tauE D τ)) = 1 := by
    calc _ = (C.1.map (tauE D τ))⁻¹ * ((gramAt D V τ)⁻¹ * ((((C.1.map (tauE D τ))⁻¹)ᴴ * (C.1.map (tauE D τ))ᴴ) *
          (gramAt D V τ * C.1.map (tauE D τ)))) := by simp only [Matrix.mul_assoc]
      _ = (C.1.map (tauE D τ))⁻¹ * C.1.map (tauE D τ) := by
          rw [← Matrix.conjTranspose_mul, hPi1, Matrix.conjTranspose_one, Matrix.one_mul, ← Matrix.mul_assoc (gramAt D V τ)⁻¹, hHi2,
            Matrix.one_mul]
      _ = 1 := hPi2
  rw [Formalism.L2.Theta.conjAt, conj_entry] at hne
  exact cut_core hlm hA.le hGS hGW hWG p q a b hpq (neg_ne_zero.mp hne)

end GlobalTheory.CompanionTheory.Hypotheses₂.ConjAdapted
end
