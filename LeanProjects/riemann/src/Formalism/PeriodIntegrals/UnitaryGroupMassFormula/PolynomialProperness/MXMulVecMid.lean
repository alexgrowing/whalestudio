import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.TauDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness.TM

theorem sum_emb {N n : ℕ} (e : Fin n ↪ Fin N) (f : Fin N → ℂ) (hf : ∀ i, (∀ t, e t ≠ i) → f i = 0) :
    ∑ i, f i = ∑ t, f (e t) := by
  rw [← Finset.sum_map Finset.univ e f]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hf
  intro t ht
  apply hi
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨t, ht⟩

def eIe (k r : ℕ) : Fin r ↪ Fin (2 * r + k + 1) :=
  ⟨eI k r, fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)⟩

def esIe (k r : ℕ) : Fin r ↪ Fin (2 * r + k + 1) :=
  ⟨esI k r, fun a b h => Fin.ext (by
    have h1 := congrArg Fin.val h
    have ha := a.isLt; have hb := b.isLt
    simp only [esI] at h1; omega)⟩

theorem eI_val (k r : ℕ) (a : Fin r) : (eI k r a).val = a.val := rfl
theorem eIe_apply (k r : ℕ) (a : Fin r) : eIe k r a = eI k r a := rfl
theorem esIe_apply (k r : ℕ) (a : Fin r) : esIe k r a = esI k r a := rfl
theorem esI_val (k r : ℕ) (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

def pX (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => x (eI k r a)

def qX (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => x (esI k r a)

def midF (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  ∑ i : Fin (2 * r + k + 1), if r ≤ i.val ∧ i.val ≤ r + k then star (y i) * (GBasic.sgn k r i * x i) else 0

theorem sig_eI (k r : ℕ) (t : Fin r) : GBasic.sig k r (eI k r t) = esI k r t := by
  have h : (eI k r t).val < r ∨ r + k < (eI k r t).val := Or.inl t.isLt
  unfold GBasic.sig
  rw [if_pos h]
  rfl

theorem sig_esI (k r : ℕ) (t : Fin r) : GBasic.sig k r (esI k r t) = eI k r t := by
  have ht := t.isLt
  have h : (esI k r t).val < r ∨ r + k < (esI k r t).val := by
    right
    show r + k < 2 * r + k - t.val
    omega
  unfold GBasic.sig
  rw [if_pos h]
  apply Fin.ext
  show 2 * r + k - (2 * r + k - t.val) = t.val
  omega

theorem herm_coords (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (qX k r y) ⬝ᵥ pX k r x + star (pX k r y) ⬝ᵥ qX k r x + midF k r x y := by
  have hmul : ∀ i, (Hpk k r *ᵥ x) i = GBasic.sgn k r i * x (GBasic.sig k r i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hsplit : ∀ i : Fin (2 * r + k + 1),
      star (y i) * (GBasic.sgn k r i * x (GBasic.sig k r i)) =
        (if i.val < r then star (y i) * x (GBasic.sig k r i) else 0) +
        (if r + k < i.val then star (y i) * x (GBasic.sig k r i) else 0) +
        (if r ≤ i.val ∧ i.val ≤ r + k then star (y i) * (GBasic.sgn k r i * x i) else 0) := by
    intro i
    by_cases h1 : i.val < r
    · have hs : GBasic.sgn k r i = 1 := by
        unfold GBasic.sgn
        rw [if_neg (show ¬ (i.val = r + k) by omega)]
      rw [if_pos h1, if_neg (show ¬ (r + k < i.val) by omega),
        if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), hs]
      ring
    · by_cases h2 : r + k < i.val
      · have hs : GBasic.sgn k r i = 1 := by
          unfold GBasic.sgn
          rw [if_neg (show ¬ (i.val = r + k) by omega)]
        rw [if_neg h1, if_pos h2, if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), hs]
        ring
      · have hs : GBasic.sig k r i = i := by
          unfold GBasic.sig
          rw [if_neg (show ¬ (i.val < r ∨ r + k < i.val) by omega)]
        rw [if_neg h1, if_neg h2, if_pos (show r ≤ i.val ∧ i.val ≤ r + k by omega), hs]
        ring
  have hA : (∑ i : Fin (2 * r + k + 1), if i.val < r then star (y i) * x (GBasic.sig k r i) else 0)
      = star (pX k r y) ⬝ᵥ qX k r x := by
    refine (sum_emb (eIe k r) _ ?_).trans ?_
    · intro i hi
      by_cases h : i.val < r
      · exact absurd (Fin.ext rfl : eIe k r ⟨i.val, h⟩ = i) (hi _)
      · rw [if_neg h]
    · simp only [dotProduct, pX, qX, Pi.star_apply, eIe_apply]
      apply Finset.sum_congr rfl
      intro t _
      have hc : (eI k r t).val < r := t.isLt
      simp [hc, sig_eI]
  have hB : (∑ i : Fin (2 * r + k + 1), if r + k < i.val then star (y i) * x (GBasic.sig k r i) else 0)
      = star (qX k r y) ⬝ᵥ pX k r x := by
    refine (sum_emb (esIe k r) _ ?_).trans ?_
    · intro i hi
      by_cases h : r + k < i.val
      · exfalso
        have hiL := i.isLt
        apply hi ⟨2 * r + k - i.val, by omega⟩
        apply Fin.ext
        rw [esIe_apply, esI_val]
        show 2 * r + k - (2 * r + k - i.val) = i.val
        omega
      · rw [if_neg h]
    · simp only [dotProduct, pX, qX, Pi.star_apply, esIe_apply]
      apply Finset.sum_congr rfl
      intro t _
      have ht := t.isLt
      have hc : r + k < (esI k r t).val := by rw [esI_val]; omega
      simp [hc, sig_esI]
  have hH : herm (Hpk k r) x y = ∑ i, star (y i) * (GBasic.sgn k r i * x (GBasic.sig k r i)) := by
    unfold herm
    simp only [dotProduct, Pi.star_apply, hmul]
  rw [hH, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB]
  unfold midF
  ring

theorem uh_of_herm {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ x y : Fin m → ℂ, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : g ∈ UH H := by
  show gᴴ * H * g = H
  have hg : ∀ v w : Fin m → ℂ, herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
    intro v w
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have e1 : ∀ (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m),
      herm M (Pi.single j 1) (Pi.single i 1) = M i j := by
    intro M i j
    have hs : star (Pi.single i 1 : Fin m → ℂ) = (Pi.single i 1 : Fin m → ℂ) := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [Pi.single_apply, hk]
    unfold herm
    rw [hs]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  rw [hg, e1, e1] at h1
  exact h1

theorem mX_eI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    mX k r vX (eI k r a) j = if h : j.val < r then vX a ⟨j.val, h⟩ else 0 := by
  unfold mX
  rw [dif_pos (show (eI k r a).val < r from a.isLt)]
  rfl

theorem mX_esI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    mX k r vX (esI k r a) j =
      if h : r + k < j.val then (vXᴴ)⁻¹ a ⟨2 * r + k - j.val, by omega⟩ else 0 := by
  have ha := a.isLt
  unfold mX
  rw [dif_neg (show ¬ ((esI k r a).val < r) by show ¬ (2 * r + k - a.val < r); omega),
    dif_pos (show r + k < (esI k r a).val by show r + k < 2 * r + k - a.val; omega)]
  by_cases hj : r + k < j.val
  · rw [dif_pos hj, dif_pos hj]
    have e : (⟨2 * r + k - (esI k r a).val, by rw [esI_val]; omega⟩ : Fin r) = a :=
      Fin.ext (by show 2 * r + k - (esI k r a).val = a.val; rw [esI_val]; omega)
    rw [e]
  · rw [dif_neg hj, dif_neg hj]

theorem mX_mid (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (i j : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : mX k r vX i j = if i = j then 1 else 0 := by
  unfold mX
  rw [dif_neg (show ¬ (i.val < r) by omega), dif_neg (show ¬ (r + k < i.val) by omega)]

theorem mX_mulVec_eI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mX k r vX *ᵥ x) (eI k r a) = (vX *ᵥ pX k r x) a := by
  simp only [Matrix.mulVec, dotProduct, mX_eI]
  refine (sum_emb (eIe k r) _ ?_).trans ?_
  · intro i hi
    by_cases h : i.val < r
    · exact absurd (Fin.ext rfl : eIe k r ⟨i.val, h⟩ = i) (hi _)
    · rw [dif_neg h, zero_mul]
  · apply Finset.sum_congr rfl
    intro t _
    have hc : ((eIe k r) t).val < r := t.isLt
    rw [dif_pos hc]
    rfl

theorem mX_mulVec_esI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mX k r vX *ᵥ x) (esI k r a) = ((vXᴴ)⁻¹ *ᵥ qX k r x) a := by
  simp only [Matrix.mulVec, dotProduct, mX_esI]
  refine (sum_emb (esIe k r) _ ?_).trans ?_
  · intro i hi
    by_cases h : r + k < i.val
    · exfalso
      have hiL := i.isLt
      apply hi ⟨2 * r + k - i.val, by omega⟩
      apply Fin.ext
      rw [esIe_apply, esI_val]
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    · rw [dif_neg h, zero_mul]
  · apply Finset.sum_congr rfl
    intro t _
    have ht := t.isLt
    have hc : r + k < ((esIe k r) t).val := by rw [esIe_apply, esI_val]; omega
    rw [dif_pos hc]
    have e : (⟨2 * r + k - ((esIe k r) t).val, by rw [esIe_apply, esI_val]; omega⟩ : Fin r) = t :=
      Fin.ext (by show 2 * r + k - ((esIe k r) t).val = t.val; rw [esIe_apply, esI_val]; omega)
    rw [e]
    try rfl

theorem mX_mulVec_mid (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : (mX k r vX *ᵥ x) i = x i := by
  simp only [Matrix.mulVec, dotProduct, mX_mid k r vX i _ h1 h2, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem pX_mX (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    pX k r (mX k r vX *ᵥ x) = vX *ᵥ pX k r x := by
  funext a
  exact mX_mulVec_eI k r vX x a

theorem qX_mX (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    qX k r (mX k r vX *ᵥ x) = (vXᴴ)⁻¹ *ᵥ qX k r x := by
  funext a
  exact mX_mulVec_esI k r vX x a

theorem midF_mX (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    midF k r (mX k r vX *ᵥ x) (mX k r vX *ᵥ y) = midF k r x y := by
  unfold midF
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [mX_mulVec_mid k r vX x i h.1 h.2, mX_mulVec_mid k r vX y i h.1 h.2]
  · rfl

end PI.PolynomialProperness.TM

namespace PI.PolynomialProperness

open TM in
theorem mxFacts : MXFacts := by
  intro k r vX hU
  have hU1 : ∀ i j, j < i → vX i j = 0 := hU.1
  have hU2 : ∀ i, vX i i = 1 := hU.2
  have hdet : vX.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hU1 i j hij)]
    simp [hU2]
  have hu : IsUnit vX.det := by rw [hdet]; exact isUnit_one
  have hu' : IsUnit vXᴴ.det := by rw [Matrix.det_conjTranspose, hdet, star_one]; exact isUnit_one
  have d1 : ∀ p q : Fin r → ℂ, star ((vXᴴ)⁻¹ *ᵥ q) ⬝ᵥ (vX *ᵥ p) = star q ⬝ᵥ p := by
    intro p q
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have d2 : ∀ p q : Fin r → ℂ, star (vX *ᵥ p) ⬝ᵥ ((vXᴴ)⁻¹ *ᵥ q) = star p ⬝ᵥ q := by
    intro p q
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu',
      Matrix.vecMul_one]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Nset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · apply uh_of_herm
      intro x y
      rw [herm_coords, herm_coords]
      simp only [pX_mX, qX_mX, midF_mX]
      rw [d1, d2]
    · intro a i hai
      unfold mX
      by_cases hi : i.val < r
      · rw [dif_pos hi, dif_pos (show (eI k r a).val < r from a.isLt)]
        by_cases hia : i = eI k r a
        · rw [if_pos hia]
          subst hia
          exact hU2 a
        · rw [if_neg hia]
          apply hU1
          have hne : i.val ≠ a.val := fun h => hia (Fin.ext h)
          show a.val < i.val
          have hai' : a.val ≤ i.val := hai
          omega
      · rw [dif_neg hi]
        have hne : i ≠ eI k r a := by
          intro h
          apply hi
          rw [h]
          exact a.isLt
        by_cases hi2 : r + k < i.val
        · have ha := a.isLt
          rw [dif_pos hi2, dif_neg (show ¬ (r + k < (eI k r a).val) by show ¬ (r + k < a.val); omega),
            if_neg hne]
        · rw [dif_neg hi2]
    · intro i j hj1 hj2 hi
      unfold mX
      rw [dif_neg (show ¬ (i.val < r) by omega)]
      by_cases hi2 : r + k < i.val
      · rw [dif_pos hi2, dif_neg (show ¬ (r + k < j.val) by omega),
          if_neg (show i ≠ j from fun h => by rw [h] at hi2; omega)]
      · rw [dif_neg hi2]
  · intro p
    funext i
    have hiL := i.isLt
    by_cases hi : i.val < r
    · have h1 := mX_mulVec_eI k r vX (xiV k r p) ⟨i.val, hi⟩
      have e : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [e] at h1
      rw [h1]
      have hp : pX k r (xiV k r p) = p := by
        funext a
        show xiV k r p (eI k r a) = p a
        unfold xiV
        rw [dif_pos (show (eI k r a).val < r from a.isLt)]
        try rfl
      rw [hp]
      unfold xiV
      rw [dif_pos hi]
    · have hz : xiV k r (vX *ᵥ p) i = 0 := by
        unfold xiV
        rw [dif_neg hi]
      rw [hz]
      by_cases hi2 : r + k < i.val
      · have h1 := mX_mulVec_esI k r vX (xiV k r p) ⟨2 * r + k - i.val, by omega⟩
        have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i :=
          Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)
        rw [e] at h1
        rw [h1]
        have hq : qX k r (xiV k r p) = 0 := by
          funext a
          have ha := a.isLt
          show xiV k r p (esI k r a) = 0
          unfold xiV
          rw [dif_neg (show ¬ ((esI k r a).val < r) by show ¬ (2 * r + k - a.val < r); omega)]
        rw [hq, Matrix.mulVec_zero, Pi.zero_apply]
      · rw [mX_mulVec_mid k r vX _ i (by omega) (by omega)]
        unfold xiV
        rw [dif_neg hi]
  · intro w hw
    funext i
    have hiL := i.isLt
    by_cases hi : i.val < r
    · have h1 := mX_mulVec_eI k r vX w ⟨i.val, hi⟩
      have e : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [e] at h1
      have hp : pX k r w = 0 := by
        funext a
        exact hw _ (Or.inl a.isLt)
      rw [h1, hp, Matrix.mulVec_zero, Pi.zero_apply, hw i (Or.inl hi)]
    · by_cases hi2 : r + k < i.val
      · have h1 := mX_mulVec_esI k r vX w ⟨2 * r + k - i.val, by omega⟩
        have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i :=
          Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)
        rw [e] at h1
        have hq : qX k r w = 0 := by
          funext a
          have ha := a.isLt
          exact hw _ (Or.inr (by show r + k < 2 * r + k - a.val; omega))
        rw [h1, hq, Matrix.mulVec_zero, Pi.zero_apply, hw i (Or.inr hi2)]
      · exact mX_mulVec_mid k r vX w i (by omega) (by omega)

end PI.PolynomialProperness
