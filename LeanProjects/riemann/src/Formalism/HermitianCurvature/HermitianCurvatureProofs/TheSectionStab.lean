import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection
import Formalism.HermitianCurvature.StatementNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.TheSecStab

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec

section block

variable {k : ℕ}

theorem zero_ne_last (hk : 1 ≤ k) : (0 : Fin (k + 1)) ≠ Fin.last k := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h'
  omega

private theorem col_lemma_2 {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {i : Fin (k + 1)}
    (hi : h *ᵥ Pi.single i 1 = Pi.single i 1) (l : Fin (k + 1)) : h l i = if l = i then 1 else 0 := by
  have e := congrFun hi l
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using e

private theorem row_lemma_3 {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hh : h ∈ UH (Hb k)) {i : Fin (k + 1)}
    (hi : h *ᵥ Pi.single i 1 = Pi.single i 1) (j : Fin (k + 1)) : h i j = if i = j then 1 else 0 := by
  have hU : hᴴ * Hb k * h = Hb k := hh
  have e := congrFun (congrFun hU i) j
  rw [Matrix.mul_apply] at e
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    col_lemma_2 hi] at e
  rw [Fintype.sum_eq_single i (by intro x hx; simp [hx])] at e
  by_cases hil : i = Fin.last k <;> by_cases hij : i = j <;> simp_all

private theorem vec_lemma_4 {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hh : h ∈ UH (Hb k))
    {i : Fin (k + 1)} (hi : h *ᵥ Pi.single i 1 = Pi.single i 1) : Pi.single i 1 ᵥ* h = Pi.single i 1 := by
  funext j
  have e : (Pi.single i 1 ᵥ* h) j = h i j := by
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [e, row_lemma_3 hh hi j]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Pi.single_apply, Ne.symm hij]

theorem commute_nu {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hh : h ∈ UH (Hb k))
    (h0 : h *ᵥ Pi.single 0 1 = Pi.single 0 1) (hl : h *ᵥ Pi.single (Fin.last k) 1 = Pi.single (Fin.last k) 1)
    (w s : ℂ) : h * nu k w s = nu k w s * h := by
  have hu : ∀ a b : ℂ, h *ᵥ (a • Pi.single 0 1 + b • Pi.single (Fin.last k) 1) =
      a • Pi.single 0 1 + b • Pi.single (Fin.last k) 1 := by
    intro a b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h0, hl]
  unfold nu
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    hu, hu, vec_lemma_4 hh h0, vec_lemma_4 hh hl]

end block

section block2

variable {k : ℕ}

private theorem nu_apply_lemma (hk : 1 ≤ k) (w s : ℂ) (l m : Fin (k + 1)) :
    nu k w s l m =
      if m = 0 then (if l = 0 then star w else if l = Fin.last k then s else 0)
      else if m = Fin.last k then (if l = 0 then s else if l = Fin.last k then w else 0)
      else (if l = m then 1 else 0) := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  unfold nu
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.add_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hm0 : m = 0
  · subst hm0
    by_cases hl0 : l = 0
    · subst hl0
      simp [h0L]
    · by_cases hlL : l = Fin.last k
      · subst hlL
        simp [h0L, h0L.symm]
      · simp [hl0, hlL, h0L]
  · by_cases hmL : m = Fin.last k
    · subst hmL
      by_cases hl0 : l = 0
      · subst hl0
        simp [h0L, h0L.symm]
      · by_cases hlL : l = Fin.last k
        · subst hlL
          simp [h0L.symm]
        · simp [hl0, hlL, h0L.symm]
    · simp [hm0, hmL]

theorem nu_last_vec (hk : 1 ≤ k) (w s : ℂ) :
    nu k w s *ᵥ Pi.single (Fin.last k) 1 = s • Pi.single 0 1 + w • Pi.single (Fin.last k) 1 := by
  have h0L := zero_ne_last hk
  funext l
  have e : (nu k w s *ᵥ Pi.single (Fin.last k) 1) l = nu k w s l (Fin.last k) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, nu_apply_lemma hk]
  by_cases hl0 : l = 0
  · subst hl0
    simp [h0L.symm, h0L]
  · by_cases hlL : l = Fin.last k
    · subst hlL
      simp [h0L.symm]
    · simp [hl0, hlL, h0L.symm]

private theorem nu_unit_lemma_5 (hk : 1 ≤ k) (w s : ℂ) (hs : star s = s)
    (hws : star w * w - s * s = 1) : (nu k w s)ᴴ * Hb k * nu k w s = Hb k := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    nu_apply_lemma hk]
  by_cases hi0 : i = 0
  · subst hi0
    rw [Fintype.sum_eq_add 0 (Fin.last k) h0L]
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
          ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
        linear_combination hws
      · by_cases hjL : j = Fin.last k
        · subst hjL
          simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
            ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
          ring
        · simp [h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]
    · intro x hx
      simp [hx.1, hx.2]
  · by_cases hiL : i = Fin.last k
    · subst hiL
      rw [Fintype.sum_eq_add 0 (Fin.last k) h0L]
      · by_cases hj0 : j = 0
        · subst hj0
          simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
            ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
          ring
        · by_cases hjL : j = Fin.last k
          · subst hjL
            simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
              ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
            linear_combination (-1 : ℂ) * hws
          · simp [h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]
      · intro x hx
        simp [hx.1, hx.2]
    · rw [Fintype.sum_eq_single i]
      · simp only [hi0, hiL, if_false, if_true, ↓reduceIte, eq_self_iff_true, star_one, one_mul]
        by_cases hj0 : j = 0
        · subst hj0
          simp [hi0, hiL]
        · by_cases hjL : j = Fin.last k
          · subst hjL
            simp [hi0, hiL]
          · by_cases hij : i = j
            · subst hij
              simp [hi0, hiL]
            · simp [hj0, hjL, hij, Ne.symm hij]
      · intro x hx
        simp [hi0, hiL, hx]

theorem nu_mem (hk : 1 ≤ k) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    nu k (wZ T T' ζ) (sZ T T' ζ) ∈ UH (Hb k) := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hsr : star (sZ T T' ζ) = sZ T T' ζ := by
    unfold sZ
    exact Complex.conj_ofReal _
  have hkey : star (wZ T T' ζ) * wZ T T' ζ - sZ T T' ζ * sZ T T' ζ = 1 := by
    have hx : 0 ≤ Complex.normSq ζ / (T * T') - 1 := by
      have h1 : 1 < Complex.normSq ζ / (T * T') := by
        rw [lt_div_iff₀ hTT, one_mul]
        exact hζ
      linarith
    have h1 : Complex.normSq (wZ T T' ζ) = Complex.normSq ζ / (T * T') := by
      unfold wZ
      rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_inv, Complex.normSq_ofReal]
      rw [show Real.sqrt T * Real.sqrt T' * (Real.sqrt T * Real.sqrt T') =
          (Real.sqrt T * Real.sqrt T) * (Real.sqrt T' * Real.sqrt T') by ring,
        Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le, div_eq_inv_mul]
    have h2 : star (wZ T T' ζ) * wZ T T' ζ = (Complex.normSq (wZ T T' ζ) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    have h3 : sZ T T' ζ * sZ T T' ζ = ((Complex.normSq ζ / (T * T') - 1 : ℝ) : ℂ) := by
      unfold sZ
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]
    rw [h2, h3, h1]
    push_cast
    ring
  exact nu_unit_lemma_5 hk _ _ hsr hkey

theorem sZ_ne {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) : sZ T T' ζ ≠ 0 := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  have h1 : 1 < Complex.normSq ζ / (T * T') := by
    rw [lt_div_iff₀ hTT, one_mul]
    exact hζ
  unfold sZ
  have hp : 0 < Real.sqrt (Complex.normSq ζ / (T * T') - 1) := Real.sqrt_pos.2 (by linarith)
  exact_mod_cast hp.ne'

theorem block_iff (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ)
    {μ μ' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) (hμ' : μ' ∈ UH (Hb k))
    (hμa : μ *ᵥ a = a) (hμb : μ' *ᵥ b = b) :
    μ * theSecB k a b T T' ζ * μ' = theSecB k a b T T' ζ ↔
      ((gA k a T)⁻¹ * μ * gA k a T) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
        gB k b T' * μ' * (gB k b T')⁻¹ = ((gA k a T)⁻¹ * μ * gA k a T)⁻¹ := by
  obtain ⟨hga1, hga2⟩ := gA_spec k hT ha
  obtain ⟨hgb1, hgb2⟩ := gB_spec k hT' hb
  set gA' := gA k a T with hgA'
  set gB' := gB k b T' with hgB'
  have hgAu : gA' ∈ UH (Hb k) := hga1
  have hgBu : gB' ∈ UH (Hb k) := hgb1
  have uA := (UHb_inv hgAu).1
  have uB := (UHb_inv hgBu).1
  set ν := nu k (wZ T T' ζ) (sZ T T' ζ) with hνdef
  have hνu : ν ∈ UH (Hb k) := nu_mem hk hT hT' hζ
  have uν := (UHb_inv hνu).1
  have hs := sZ_ne hT hT' hζ
  set e := (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) with hedef
  set e0 := (Pi.single 0 1 : Fin (k + 1) → ℂ) with he0def
  set ĥ := gA'⁻¹ * μ * gA' with hĥdef
  set ĥ' := gB' * μ' * gB'⁻¹ with hĥ'def
  have hĥu : ĥ ∈ UH (Hb k) := UHb_mul (UHb_mul (UHb_inv hgAu).2 hμ) hgAu
  have uĥ := (UHb_inv hĥu).1
  have hsT : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT).ne'
  have hsT' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'

  have hAinv : gA'⁻¹ *ᵥ a = ((Real.sqrt T : ℝ) : ℂ) • e := by
    rw [← hga2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uA, Matrix.one_mulVec]
  have hAe : gA' *ᵥ e = ((Real.sqrt T : ℝ) : ℂ)⁻¹ • a := by
    rw [← hga2, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hsT, one_smul]
  have hĥe : ĥ *ᵥ e = e := by
    rw [hĥdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAe, Matrix.mulVec_smul, hμa, Matrix.mulVec_smul,
      hAinv, smul_smul, inv_mul_cancel₀ hsT, one_smul]
  have hBinv : gB'⁻¹ *ᵥ e = ((Real.sqrt T' : ℝ) : ℂ)⁻¹ • b := by
    have : gB'⁻¹ *ᵥ (((Real.sqrt T' : ℝ) : ℂ) • e) = b := by
      rw [← hgb2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uB, Matrix.one_mulVec]
    rw [Matrix.mulVec_smul] at this
    rw [← this, smul_smul, inv_mul_cancel₀ hsT', one_smul]
  have hĥ'e : ĥ' *ᵥ e = e := by
    rw [hĥ'def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBinv, Matrix.mulVec_smul, hμb, Matrix.mulVec_smul,
      hgb2, smul_smul, inv_mul_cancel₀ hsT', one_smul]

  have hequiv : μ * theSecB k a b T T' ζ * μ' = theSecB k a b T T' ζ ↔ ĥ * ν * ĥ' = ν := by
    have hS : theSecB k a b T T' ζ = gA' * ν * gB' := rfl
    rw [hS]
    constructor
    · intro h
      calc ĥ * ν * ĥ' = gA'⁻¹ * (μ * (gA' * ν * gB') * μ') * gB'⁻¹ := by
            simp only [hĥdef, hĥ'def, Matrix.mul_assoc]
        _ = gA'⁻¹ * (gA' * ν * gB') * gB'⁻¹ := by rw [h]
        _ = ν := by
            simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ uA, Matrix.mul_nonsing_inv _ uB,
              Matrix.mul_one]
    · intro h
      calc μ * (gA' * ν * gB') * μ' = gA' * (ĥ * ν * ĥ') * gB' := by
            simp only [hĥdef, hĥ'def, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ uA,
              Matrix.nonsing_inv_mul _ uB, Matrix.mul_one]
        _ = gA' * ν * gB' := by rw [h]
  rw [hequiv]
  constructor
  · intro h

    have h1 : ĥ *ᵥ (ν *ᵥ e) = ν *ᵥ e := by
      have := congrArg (fun M => M *ᵥ e) h
      simp only [← Matrix.mulVec_mulVec, hĥ'e] at this
      exact this
    rw [hνdef, nu_last_vec hk, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hĥe] at h1
    have h0 : ĥ *ᵥ e0 = e0 := by
      have h2 : sZ T T' ζ • (ĥ *ᵥ e0) = sZ T T' ζ • e0 := add_right_cancel h1
      exact smul_right_injective _ hs h2
    refine ⟨h0, ?_⟩
    have hc := commute_nu hĥu h0 hĥe (wZ T T' ζ) (sZ T T' ζ)
    have h3 : ν * (ĥ * ĥ') = ν * 1 := by
      rw [Matrix.mul_one, ← Matrix.mul_assoc, ← hc, h]
    have h4 : ĥ * ĥ' = 1 := by
      have := congrArg (fun M => ν⁻¹ * M) h3
      simp only [Matrix.nonsing_inv_mul_cancel_left _ _ uν] at this
      exact this
    exact (Matrix.inv_eq_right_inv h4).symm
  · rintro ⟨h0, h1⟩
    have hc := commute_nu hĥu h0 hĥe (wZ T T' ζ) (sZ T T' ζ)
    rw [h1, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uĥ, Matrix.mul_one]

end block2

section full

variable {k r : ℕ}

theorem uwset_block {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : Mat k r} (hg : g ∈ UWset k r z) :
    ∃ μ ∈ UH (Hb k), g = embWb k r μ ∧ μ *ᵥ wbPart k r z = wbPart k r z := by
  obtain ⟨μ, hμ, rfl⟩ := (UWb_iff g).1 ⟨hg.1, hg.2.1⟩
  refine ⟨μ, hμ, rfl, ?_⟩
  have h1 : embWb k r μ *ᵥ z = z := hg.2.2
  rw [← jV_wbPart hz, emb_mulVec_jV] at h1
  have := congrArg (wbPart k r) h1
  rwa [wbPart_jV, wbPart_jV] at this

theorem emb_inj {μ μ' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : embWb k r μ = embWb k r μ') : μ = μ' := by
  ext a b
  have ha : a.val ≤ k := Nat.lt_succ_iff.mp a.isLt
  have hb : b.val ≤ k := Nat.lt_succ_iff.mp b.isLt
  have e := congrFun (congrFun h ⟨r + a.val, by omega⟩) ⟨r + b.val, by omega⟩
  simpa [embWb, ha, hb] using e

theorem stab_sub (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ ζ' : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    (hζ' : Tz k r z * Tz k r z' < Complex.normSq ζ') (p : Mat k r × Mat k r)
    (hp : p ∈ NF.Stab k r z z' (theSection k r z z') ζ) : p ∈ NF.Stab k r z z' (theSection k r z z') ζ' := by
  obtain ⟨h1, h2, heq⟩ := hp
  obtain ⟨μ, hμ, hp1, hμa⟩ := uwset_block hz h1
  obtain ⟨μ', hμ', hp2, hμb⟩ := uwset_block hz' h2
  refine ⟨h1, h2, ?_⟩
  have ha := herm_self k r z hz
  have hb := herm_self k r z' hz'
  have hblock : μ * theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ * μ' =
      theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ := by
    apply emb_inj (r := r)
    rw [emb_mul, emb_mul, ← hp1, ← hp2]
    exact heq
  have hc := (block_iff hk hT hT' ha hb hζ hμ hμ' hμa hμb).1 hblock
  have hblock' := (block_iff hk hT hT' ha hb hζ' hμ hμ' hμa hμb).2 hc
  show p.1 * embWb k r (theSection k r z z' ζ') * p.2 = embWb k r (theSection k r z z' ζ')
  rw [hp1, hp2, ← emb_mul, ← emb_mul]
  exact congrArg (embWb k r) hblock'

theorem theSection_csec (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') :
    IsSection k r z z' (theSection k r z z') ∧ ∀ ζ ζ' : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
      Tz k r z * Tz k r z' < Complex.normSq ζ' →
        NF.Stab k r z z' (theSection k r z z') ζ = NF.Stab k r z z' (theSection k r z z') ζ' :=
  ⟨theSection_isSection k r z z' hk hz hz' hT hT', fun ζ ζ' hζ hζ' => Set.ext fun p =>
    ⟨stab_sub hk hz hz' hT hT' hζ hζ' p, stab_sub hk hz hz' hT hT' hζ' hζ p⟩⟩

end full

end Formalism.FourierDecayAlt.P.TheSecStab

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gauge_section_exists : SecExists := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ hk
  exact ⟨Formalism.FourierDecayAlt.P.TheSec.theSection P.k P.r Bs.z Bs.z',
    Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (by omega) Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
