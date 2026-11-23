import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.Rad
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NormalEx

theorem blockIdx_mono : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i ≤ j → blockIdx bs i ≤ blockIdx bs j
  | [], _, _, _ => le_rfl
  | (_, s) :: bs, i, j, h => by
    have := blockIdx_mono bs (i - s) (j - s) (by omega)
    simp only [blockIdx]
    split_ifs <;> omega

theorem blockIdx_of_entry : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 → blockIdx bs i = blockIdx bs j
  | [], _, _, _ => rfl
  | (t, s) :: bs, i, j, h => by
    have := blockIdx_of_entry bs (i - s) (j - s)
    simp only [blockIdx, ptEntry] at h ⊢
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1.1, if_pos h1.2]
    · rw [if_neg h1] at h
      by_cases h2 : s ≤ i ∧ s ≤ j
      · rw [if_pos h2] at h
        rw [if_neg (by omega), if_neg (by omega), this h]
      · rw [if_neg h2] at h; exact absurd rfl h

theorem entry_cases (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (i j : ℕ) (h : ptEntry ((t, s) :: bs) i j ≠ 0) :
    (i < s ∧ i + j + 1 = s ∧ ptEntry ((t, s) :: bs) i j = t) ∨
      (s ≤ i ∧ s ≤ j ∧ ptEntry ((t, s) :: bs) i j = ptEntry bs (i - s) (j - s)) := by
  simp only [ptEntry] at h ⊢
  by_cases h1 : i < s ∧ j < s
  · rw [if_pos h1] at h ⊢
    by_cases h3 : i + j + 1 = s
    · exact Or.inl ⟨h1.1, h3, if_pos h3⟩
    · rw [if_neg h3] at h; exact absurd rfl h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : s ≤ i ∧ s ≤ j
    · exact Or.inr ⟨h2.1, h2.2, if_pos h2⟩
    · rw [if_neg h2] at h; exact absurd rfl h

theorem entry_same : ∀ (bs : List (ℂ × ℕ)) (i j i' j' : ℕ), ptEntry bs i j ≠ 0 → ptEntry bs i' j' ≠ 0 →
    blockIdx bs i = blockIdx bs i' → ptEntry bs i j = ptEntry bs i' j' ∧ i + j = i' + j'
  | [], _, _, _, _, h, _, _ => absurd rfl h
  | (t, s) :: bs, i, j, i', j', h, h', hb => by
    have ih := entry_same bs (i - s) (j - s) (i' - s) (j' - s)
    simp only [blockIdx] at hb
    rcases entry_cases t s bs i j h with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
      rcases entry_cases t s bs i' j' h' with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
    · exact ⟨a3.trans b3.symm, by omega⟩
    · rw [if_pos a1, if_neg (by omega)] at hb; omega
    · rw [if_pos b1, if_neg (by omega)] at hb; omega
    · rw [if_neg (by omega), if_neg (by omega)] at hb
      obtain ⟨e1, e2⟩ := ih (a3 ▸ h) (b3 ▸ h') (by omega)
      exact ⟨by rw [a3, b3, e1], by omega⟩

theorem entry_exists : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ j, j < (bs.map Prod.snd).sum →
    ∃ i, i < (bs.map Prod.snd).sum ∧ ptEntry bs i j ≠ 0
  | [], _, j, h => by simp at h
  | (t, s) :: bs, hb, j, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    by_cases h1 : j < s
    · refine ⟨s - 1 - j, by omega, ?_⟩
      simp only [ptEntry]
      rw [if_pos (by omega), if_pos (by omega)]
      exact (hb (t, s) (by simp)).1
    · obtain ⟨i, hi, he⟩ := entry_exists bs (fun b hb' => hb b (by simp [hb'])) (j - s) (by omega)
      refine ⟨s + i, by omega, ?_⟩
      simp only [ptEntry]
      rw [if_neg (by omega), if_pos (by omega)]
      simpa using he

theorem point_facts {r : ℕ} (p : Point ℂ (r + 1)) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0)
    (hn : ∀ a b : Fin r, ‖Z a b‖ = ‖ptEntry p.1 a.val b.val‖) :
    BlockAnti (fun a : Fin r => blockIdx p.1 a.val) Z ∧ (∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) ∧
      ∀ a : Fin r, ptEntry p.1 a.val r = 0 := by
  have hne : ∀ a b : Fin r, Z a b ≠ 0 → ptEntry p.1 a.val b.val ≠ 0 := fun a b h h' =>
    h (norm_eq_zero.1 (by rw [hn, h', norm_zero]))
  have hrow : ∀ a : Fin r, ∃ b : Fin r, ptEntry p.1 a.val b.val ≠ 0 := fun a => by
    by_contra hc
    push Not at hc
    exact hZ (Matrix.det_eq_zero_of_row_eq_zero a fun b => by
      by_contra h; exact hne a b h (hc b))
  have hrr : ptEntry p.1 r r ≠ 0 := by
    obtain ⟨i, hi, he⟩ := entry_exists p.1 p.2.1 r (by rw [p.2.2]; omega)
    rw [p.2.2] at hi
    by_cases h : i < r
    · obtain ⟨b, hb⟩ := hrow ⟨i, h⟩
      have := (entry_same p.1 i r i b.val he hb rfl).2
      have := b.2
      omega
    · obtain rfl : i = r := by omega
      exact he
  have hlast : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r := fun a h => by
    obtain ⟨b, hb⟩ := hrow a
    have := (entry_same p.1 a.val b.val r r hb hrr h).2
    have := a.2
    have := b.2
    omega
  refine ⟨⟨fun a b h => blockIdx_mono _ _ _ h, hZ, fun a b h => blockIdx_of_entry _ _ _ (hne a b h),
    fun a b a' b' h h' hb => ?_⟩, hlast, fun a => ?_⟩
  · obtain ⟨e1, e2⟩ := entry_same p.1 _ _ _ _ (hne a b h) (hne a' b' h') hb
    refine ⟨by rw [hn, hn, e1], fun h => Fin.ext ?_, fun h => ?_⟩
    · have := congrArg Fin.val h; omega
    · have := Fin.lt_def.1 h; exact Fin.lt_def.2 (by omega)
  · by_contra h
    exact hlast a (blockIdx_of_entry _ _ _ h)

variable {k r : ℕ}

theorem herm_split (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ a, star (w (eI k r a)) * v (esI k r a) +
      herm (Hb k) (fun j => v (wI k r j)) (fun j => w (wI k r j)) + ∑ a, star (w (esI k r a)) * v (eI k r a) := by
  rw [herm_Hb]
  simp only [herm, dotProduct, Matrix.mulVec, sum3 (k := k) (r := r)]
  simp [H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss]

theorem herm_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  rw [herm_split, herm_Hb]
  simp [bvec_apply, eI_inj, wI_ne_eI, esI_ne_eI, apply_ite (starRingEnd ℂ)]

theorem eI_herm (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) (bvec (eI k r a)) v = star (v (esI k r a)) := by
  rw [herm_split, herm_Hb]
  simp [bvec_apply, eI_inj, wI_ne_eI, esI_ne_eI, apply_ite (starRingEnd ℂ)]

theorem herm_isom {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem H_mul_H : Hpk k r * Hpk k r = 1 := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, Matrix.one_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]
  rename_i i j
  by_cases h : i = j
  · subst h; simp only [if_true, sg]; split_ifs <;> simp
  · simp [h]

theorem isUnit_det {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [← H_mul_H (k := k) (r := r)]; nth_rewrite 4 [← hg']; simp only [Matrix.mul_assoc]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem graph (v : Fin r → Fin (2 * r + k + 1) → ℂ) (hiso : ∀ a b, herm (Hpk k r) (v a) (v b) = 0)
    (hs : ∀ a b, v b (esI k r a) = if a = b then 1 else 0) :
    ∃ q : PPar k r, (∀ b, pOf k r q *ᵥ v b = bvec (esI k r b)) ∧
      ∀ z, inWb k r z → (∀ b, herm (Hpk k r) z (v b) = 0) → pOf k r q *ᵥ z = z := by
  set A : Fin r → Fin (k + 1) → ℂ := fun b j => v b (wI k r j) with hA
  set S : Matrix (Fin r) (Fin r) ℂ := fun a b => v b (eI k r a) + herm (Hb k) (A b) (A a) / 2 with hS
  have hsk : Sᴴ = -S := by
    ext a b
    have h := hiso b a
    rw [herm_split] at h
    simp [hs, apply_ite (starRingEnd ℂ)] at h
    have h2 : (starRingEnd ℂ) (herm (Hb k) (A a) (A b)) = herm (Hb k) (A b) (A a) := herm_star _ _
    show star (v a (eI k r b) + herm (Hb k) (A a) (A b) / 2) = -(v b (eI k r a) + herm (Hb k) (A b) (A a) / 2)
    simp [h2]
    simp only [hA]
    linear_combination h
  obtain ⟨⟨s, t⟩, hst, -⟩ := skewM_unique (-S) (by rw [Matrix.conjTranspose_neg, hsk])
  have hp : pOf k r (-A, s, t) = pEl k r (-A) (-S) := by rw [hst]; rfl
  refine ⟨(-A, s, t), fun b => ?_, fun z hz hzv => ?_⟩
  · have h1 : pEl k r A S *ᵥ bvec (esI k r b) = v b := by
      funext x
      rw [mulVec_bvec]
      induction x using cases3
      · rw [pEl_es]; simp [hS]
      · simp [pEl_ws, hA]
      · simp [pEl_ss, hs]
    rw [hp, ← h1, Matrix.mulVec_mulVec, ← pEl_inv,
      Matrix.nonsing_inv_mul _ (isUnit_det (pEl_mem_UH A S hsk)), Matrix.one_mulVec]
  · have h1 : ∀ a, z (eI k r a) = 0 := fun a => hz _ (Or.inl a.2)
    have h2 : ∀ a, z (esI k r a) = 0 := fun a => hz _ (Or.inr (by have := a.2; simp only [esI]; omega))
    rw [hp]
    funext x
    simp only [Matrix.mulVec, dotProduct, sum3 (k := k) (r := r)]
    induction x using cases3 with
    | h1 a =>
      have h := hzv a
      rw [herm_split, herm_Hb] at h
      simp [h1, h2] at h
      simp [pEl_ew, h1, h2, hA, mul_assoc, h]
    | h2 j => simp [pEl_ww, h1, h2]
    | h3 a => simp [pEl_sw, h1, h2]

theorem graph' (u : Fin r → Fin (2 * r + k + 1) → ℂ) (hiso : ∀ a b, herm (Hpk k r) (u a) (u b) = 0)
    (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0) (hs : ∀ a b, u b (esI k r a) = Z a b) :
    ∃ q : PPar k r, (∀ b, pOf k r q *ᵥ u b ∈ Xst k r) ∧
      ∀ z, inWb k r z → (∀ b, herm (Hpk k r) z (u b) = 0) → pOf k r q *ᵥ z = z := by
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.2 hZ
  have hr : ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), (∀ b, herm (Hpk k r) z (u b) = 0) →
      herm (Hpk k r) z (∑ b, c b • u b) = 0 := fun z c h => by
    unfold herm at h ⊢
    simp [star_sum, star_smul, sum_dotProduct, h]
  have hl : ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), (∀ b, herm (Hpk k r) (u b) z = 0) →
      herm (Hpk k r) (∑ b, c b • u b) z = 0 := fun z c h => by
    unfold herm at h ⊢
    simp [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, h]
  obtain ⟨q, h1, h2⟩ := graph (k := k) (fun c => ∑ b, Z⁻¹ b c • u b)
    (fun a b => hl _ _ fun c => hr _ _ fun d => hiso c d) (fun a b => by
      have := congrFun (congrFun (Matrix.mul_nonsing_inv Z hu) a) b
      simpa [Matrix.mul_apply, Matrix.one_apply, hs, mul_comm] using this)
  refine ⟨q, fun b => ?_, fun z hz hzu => h2 z hz fun b => hr _ _ hzu⟩
  have : u b = ∑ c, Z c b • ∑ d, Z⁻¹ d c • u d := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have e : ∀ d, ∑ c, Z c b * Z⁻¹ d c = if d = b then 1 else 0 := fun d => by
      have := congrFun (congrFun (Matrix.nonsing_inv_mul Z hu) d) b
      simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using this
    simp [e]
  rw [this, Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [Matrix.mulVec_smul, h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem pEl_eI (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    pEl k r B S *ᵥ bvec (eI k r a) = bvec (eI k r a) := ((radical k r).1 B S).1 a

theorem Zr_left (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (g : Mat k r) :
    Zr k r (pEl k r B S * g) = Zr k r g := by
  ext a b
  simp [Zr, Matrix.mul_apply, sum3, pEl_se, pEl_sw, pEl_ss]

theorem Zr_right (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (g : Mat k r) :
    Zr k r (g * pEl k r B S) = Zr k r g := by
  ext a b
  simp [Zr, Matrix.mul_apply, sum3, pEl_se, pEl_we, pEl_ee]

theorem normal_form : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (p : Point ℂ (r + 1)), TwoFl k r z z' g₀ → ZhatO k r z z' g₀ = ptMat p → ∃ p₁ p₀ : PPar k r, pOf k r p₀ *ᵥ z' = z' ∧ IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) ∧ Zr k r (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) = Zr k r g₀ ∧ ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r := by
  intro k r z z' g p ⟨_, hz', _, _, hg, _, hD⟩ hp
  have hu := isUnit_det hg
  have hf : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin r), fvec k r y a.castSucc = bvec (eI k r a) := fun y a => by
    simp [fvec]
  have hfl : fvec k r z' (Fin.last r) = z' := by simp [fvec]
  have hZ : ∀ a b : Fin r, Formalism.QuantumDeterminants.Zhat k r z z' g a.castSucc b.castSucc = Zr k r g a b := fun a b => by
    simp only [Formalism.QuantumDeterminants.Zhat, hf, herm_eI, mulVec_bvec, Zr]
  have hdet : (Zr k r g).det ≠ 0 := by
    intro h
    apply hD
    unfold Dr Dmin
    rw [norm_eq_zero, ← h]
    congr 1
    ext a b
    exact hZ a b
  have hn : ∀ a b : Fin (r + 1), ‖Formalism.QuantumDeterminants.Zhat k r z z' g a b‖ = ‖ptEntry p.1 a.val b.val‖ := fun a b => by
    have := congrArg norm (congrFun (congrFun hp a) b)
    simpa [ZhatO, ptMat] using this
  obtain ⟨hB, hlast, h0⟩ := point_facts p (Zr k r g) hdet fun a b => by
    rw [← hZ, hn]; rfl
  have hgi : ∀ v, g *ᵥ (g⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hee : ∀ a b : Fin r, herm (Hpk k r) (bvec (eI k r a)) (bvec (eI k r b)) = 0 := fun a b => by
    rw [herm_eI, bvec_apply, if_neg (esI_ne_eI _ _)]
  obtain ⟨q₁, h1, -⟩ := graph' (fun b => g *ᵥ bvec (eI k r b)) (fun a b => by rw [herm_isom hg, hee])
    (Zr k r g) hdet (fun a b => mulVec_bvec _ _ _)
  obtain ⟨q₀, h2, h3⟩ := graph' (fun b => g⁻¹ *ᵥ bvec (eI k r b))
    (fun a b => by rw [← herm_isom hg, hgi, hgi, hee]) (Zr k r g)ᴴ
    (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hdet) (fun a b => by
      refine (herm_eI _ a).symm.trans ?_
      rw [← herm_isom hg, hgi, eI_herm, mulVec_bvec]; rfl)
  have hZe : Zr k r (pOf k r q₁ * g * (pOf k r q₀)⁻¹) = Zr k r g := by
    unfold pOf
    rw [pEl_inv, Zr_right, Zr_left]
  have m₁ : pOf k r q₁ ∈ GG k r := pEl_mem_UH _ _ (skewM_skew _ _)
  have m₀ : pOf k r q₀ ∈ GG k r := pEl_mem_UH _ _ (skewM_skew _ _)
  have m₀' : (pOf k r q₀)⁻¹ ∈ GG k r := by
    unfold pOf
    rw [pEl_inv]
    exact pEl_mem_UH _ _ (by rw [Matrix.conjTranspose_neg, skewM_skew])
  have hfix : ∀ (q : PPar k r) (a : Fin r), (pOf k r q)⁻¹ *ᵥ bvec (eI k r a) = bvec (eI k r a) := fun q a => by
    unfold pOf
    rw [pEl_inv, pEl_eI]
  refine ⟨q₁, q₀, h3 z' hz' fun b => ?_, ⟨mul_mem (mul_mem m₁ hg) m₀', fun a => ⟨?_, ?_⟩, by rw [hZe]; exact hB⟩,
    hZe, hlast⟩
  · have := hn b.castSucc (Fin.last r)
    simp only [Fin.val_castSucc, Fin.val_last, h0, norm_zero, norm_eq_zero, Formalism.QuantumDeterminants.Zhat, hf, hfl] at this
    rw [← herm_isom hg, hgi, this]
  · rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det m₀),
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix]
    exact h2 a
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix]
    exact h1 a

end GlobalTheory.Amp.NormalEx
