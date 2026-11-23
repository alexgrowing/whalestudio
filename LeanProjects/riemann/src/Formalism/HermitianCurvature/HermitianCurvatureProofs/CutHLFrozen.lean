import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

section comm

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem comm_Tm (Eu : Fin n → Fin n → A) (hG : GlRel Eu) (p a b : Fin n) (ha : a ≠ p) (hb : b ≠ p) (v : ℂ) :
    Commute (Eu p p) (Tm Eu v a b) := by
  unfold Tm
  refine Commute.add_right ?_ ?_
  · split_ifs
    · exact (Algebra.commutes v (Eu p p)).symm
    · exact Commute.zero_right _
  · have h := hG p p a b
    rw [if_neg (Ne.symm ha), if_neg hb, sub_zero] at h
    exact sub_eq_zero.mp h

theorem comm_qminor (Eu : Fin n → Fin n → A) (hG : GlRel Eu) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (p : Fin n)
    (ha : ∀ i, a i ≠ p) (hb : ∀ i, b i ≠ p) : Commute (Eu p p) (qminor Eu a b u) := by
  unfold qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ (fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact comm_Tm Eu hG p _ _ (ha _) (hb i) _

end comm

section aa

variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

theorem AAx_congr_rows (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi xi' : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (u : ℂ)
    (h : ∀ a : Fin r, a.val < m → xi a = xi' a) : C3.AAx k r Eu xi m hm u = C3.AAx k r Eu xi' m hm u := by
  unfold C3.AAx
  simp only [show ∀ a : Fin m, xi (Fin.castLE hm a) = xi' (Fin.castLE hm a) from fun a => h _ a.isLt]

theorem AAv_congr_rows (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y y' : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ℓ : ℂ)
    (h : ∀ a : Fin r, a.val < m → y a = y' a) : C3.AAv k r Eu y m hm ℓ = C3.AAv k r Eu y' m hm ℓ := by
  unfold C3.AAv
  simp only [show ∀ a : Fin m, y (Fin.castLE hm a) = y' (Fin.castLE hm a) from fun a => h _ a.isLt]

theorem comm_AAx (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel Eu)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j + 1 ≤ r) (u : ℂ)
    (h0 : ∀ a : Fin r, a.val < j → xi a (eI k r ⟨j, by omega⟩) = 0) :
    Commute (Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩)) (C3.AAx k r Eu xi j (by omega) u) := by
  unfold C3.AAx
  refine Commute.sum_right _ _ _ (fun c _ => ?_)
  split_ifs with hc
  · by_cases hp : ∃ l, c l = eI k r ⟨j, by omega⟩
    · obtain ⟨l, hl⟩ := hp
      have hdet : (of fun (a l : Fin j) => xi (Fin.castLE (by omega) a) (c l)).det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero l
        intro a
        simp only [of_apply, hl]
        exact h0 _ a.isLt
      simp only [hdet, zero_smul]
      exact Commute.zero_right _
    · push_neg at hp
      refine Commute.smul_right ?_ _
      refine comm_qminor Eu hG _ _ u _ (fun i => ?_) hp
      have := i.isLt
      simp only [C3.xR, eI, ne_eq, Fin.ext_iff, Fin.coe_castLE]
      omega
  · exact Commute.zero_right _

theorem comm_AAv (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel Eu)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j + 1 ≤ r) (ℓ : ℂ)
    (h0 : ∀ a : Fin r, a.val < j → y a (esI k r ⟨j, by omega⟩) = 0) :
    Commute (Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩)) (C3.AAv k r Eu y j (by omega) ℓ) := by
  unfold C3.AAv
  refine Commute.sum_right _ _ _ (fun c _ => ?_)
  split_ifs with hc
  · by_cases hp : ∃ l, c l = esI k r ⟨j, by omega⟩
    · obtain ⟨l, hl⟩ := hp
      have hdet : (of fun (a l : Fin j) => y (Fin.castLE (by omega) a) (c l)).det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero l
        intro a
        simp only [of_apply, hl]
        exact h0 _ a.isLt
      simp only [hdet, zero_smul]
      exact Commute.zero_right _
    · push_neg at hp
      refine Commute.smul_right ?_ _
      refine comm_qminor Eu hG _ _ _ _ hp (fun i => ?_)
      have := i.isLt
      simp only [C3.sR, esI, ne_eq, Fin.ext_iff, Fin.coe_castLE]
      omega
  · exact Commute.zero_right _

end aa

section what₂

variable {k r j : ℕ}

private theorem x0_esI_apply_eq_dite_Z {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))) (a : Fin r) (ha : a.val < j) (q : Fin (2 * r + k + 1)) :
    x0 k r j hj Z τ γ (esI k r a) q = if h : q.val < j then Z ⟨a.val, ha⟩ ⟨q.val, h⟩ else 0 := by
  simp only [x0, Dx2.Split.castM_apply, U.mMap, U.blk3, reindex_apply, submatrix_apply]
  have he : (U.eB k (j + 1) (r - (j + 1))).symm (Fin.cast (by omega) (esI k r a)) =
      Sum.inr ⟨j - a.val, by omega⟩ := by
    rw [Equiv.symm_apply_eq]
    simp [U.eB, esI, Fin.ext_iff]
    omega
  rw [he]
  rcases hq : (U.eB k (j + 1) (r - (j + 1))).symm (Fin.cast (by omega) q) with (l | l) | l
  all_goals rw [Equiv.symm_apply_eq] at hq
  all_goals have hv := congrArg Fin.val hq
  all_goals simp [U.eB] at hv
  · rw [fromBlocks_apply₂₁, fromCols_apply_inl, StandardCharacterExists.wMat_mul_apply]
    have hr : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = Fin.castAdd 1 ⟨a.val, ha⟩ := by
      ext
      simp
      omega
    rw [hr]
    simp only [zfull, U.blk2, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
    by_cases hl : l.val < j
    · have hl' : l = Fin.castAdd 1 ⟨l.val, hl⟩ := by
        ext
        simp
      rw [hl', finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, dif_pos (by omega)]
      congr 1
      ext
      simp [hv]
    · have hl' : l = Fin.natAdd j 0 := by
        ext
        simp
        omega
      rw [hl', finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂, dif_neg (by omega)]
      rfl
  · rw [fromBlocks_apply₂₁, fromCols_apply_inr, dif_neg (by omega)]
    rfl
  · rw [fromBlocks_apply₂₂, dif_neg (by omega)]
    rfl

private theorem xi0_apply_eq_esI_apply {k r : ℕ} (g : B.Mat k r) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    PBG.xi0 g a p = g (esI k r a) p := by
  have hH : ∀ s, Hpk k r (eI k r a) s = if s = esI k r a then 1 else 0 := by
    intro s
    have := a.isLt
    have := s.isLt
    simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
    have hd : 2 * r + k - (a : ℕ) + a = 2 * r + k := Nat.sub_add_cancel (by omega)
    generalize 2 * r + k - (a : ℕ) = d at *
    split_ifs <;> first | rfl | omega
  simp [PBG.xi0, herm, bvec, mulVec, dotProduct, Pi.single_apply, hH]

private theorem sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) (a : Fin r)
    (p : Fin (2 * r + k + 1)) :
    GBasic.sgn k r (GBasic.sig k r p) * PBG.y0 g a p = star (g (esI k r a) (GBasic.sig k r p)) := by
  have hs : GBasic.sig k r (GBasic.sig k r p) = p := by
    have := p.isLt
    ext
    simp only [GBasic.sig]
    split_ifs with h1 h2 h2 <;> simp only [Fin.val_mk] at * <;> omega
  have hn : GBasic.sgn k r (eI k r a) = 1 := by
    have := a.isLt
    rw [GBasic.sgn, if_neg]
    simp only [eI, Fin.val_mk]
    omega
  have he : GBasic.sig k r (eI k r a) = esI k r a := by
    have := a.isLt
    ext
    simp [GBasic.sig, eI, esI]
  have hu := B2x5.isUnit_det_GV hg
  have h1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc (gᴴ * Hpk k r), Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (GBasic.sig k r p)) (eI k r a)
  rw [C2x6.Hpk_mul_apply, C2x6.mul_Hpk_apply] at h2
  rw [hs, he, hn, mul_one, conjTranspose_apply] at h2
  have hy : PBG.y0 g a p = g⁻¹ p (eI k r a) := by
    simp [PBG.y0, bvec, mulVec, dotProduct, Pi.single_apply]
  rw [hy, h2]

theorem xi0_row_independent_of_tau (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin r) (ha : a.val < j) : PBG.xi0 (x0 k r j hj Z τ' γ) a = PBG.xi0 (x0 k r j hj Z τ γ) a := by
  funext p
  rw [xi0_apply_eq_esI_apply, xi0_apply_eq_esI_apply, x0_esI_apply_eq_dite_Z hj Z τ' γ a ha, x0_esI_apply_eq_dite_Z hj Z τ γ a ha]

theorem xi0_x0_eI_j_eq_zero (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin r) (ha : a.val < j) : PBG.xi0 (x0 k r j hj Z τ γ) a (eI k r ⟨j, by omega⟩) = 0 := by
  rw [xi0_apply_eq_esI_apply, x0_esI_apply_eq_dite_Z hj Z τ γ a ha, dif_neg]
  simp [eI]

theorem y0_row_independent_of_tau (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ τ' : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) (a : Fin r) (ha : a.val < j) :
    PBG.y0 (x0 k r j hj Z τ' γ) a = PBG.y0 (x0 k r j hj Z τ γ) a := by
  funext p
  have hs : GBasic.sgn k r (GBasic.sig k r p) ≠ 0 := by
    unfold GBasic.sgn
    split_ifs <;> norm_num
  apply mul_left_cancel₀ hs
  rw [sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ' hγ), sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ hγ),
    x0_esI_apply_eq_dite_Z hj Z τ' γ a ha, x0_esI_apply_eq_dite_Z hj Z τ γ a ha]

theorem y0_x0_esI_j_eq_zero_of_det_ne_zero (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) (a : Fin r) (ha : a.val < j) :
    PBG.y0 (x0 k r j hj Z τ γ) a (esI k r ⟨j, by omega⟩) = 0 := by
  have hs : GBasic.sgn k r (GBasic.sig k r (esI k r ⟨j, by omega⟩)) ≠ 0 := by
    unfold GBasic.sgn
    split_ifs <;> norm_num
  apply mul_left_cancel₀ hs
  rw [sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ hγ), x0_esI_apply_eq_dite_Z hj Z τ γ a ha, dif_neg, mul_zero, star_zero]
  have : j + 1 ≤ r := hj
  have hse : (GBasic.sig k r (esI k r ⟨j, by omega⟩)).val = j := by
    unfold GBasic.sig
    rw [if_pos (Or.inr (by simp only [esI]; omega))]
    simp only [esI]
    omega
  rw [hse]
  omega

end what₂

theorem frozen_X_identity : FrozenX := by
  intro A _ _ k r j hj Eu Z τ τ' u γ hG hZ hτ hτ' hγ
  exact ⟨AAx_congr_rows Eu _ _ j _ u (fun a ha => xi0_row_independent_of_tau hj Z τ τ' γ a ha),
    comm_AAx Eu hG _ j hj u (fun a ha => xi0_x0_eI_j_eq_zero hj Z τ γ a ha)⟩

theorem frozen_V_identity : FrozenV := by
  intro A _ _ k r j hj Eu Z τ τ' ℓ γ hG hZ hτ hτ' hγ
  exact ⟨AAv_congr_rows Eu _ _ j _ ℓ (fun a ha => y0_row_independent_of_tau hj hZ hτ hτ' hγ a ha),
    comm_AAv Eu hG _ j hj ℓ (fun a ha => y0_x0_esI_j_eq_zero_of_det_ne_zero hj hZ hτ hγ a ha)⟩

end Formalism.FourierDecayAlt.P.CutHL
