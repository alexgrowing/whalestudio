import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace InvGrp

variable {k r : ℕ}

def isW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

theorem embWb_apply_offW (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) (hi : ¬ isW k r i) : (embWb k r γ *ᵥ v) i = v i := by
  have hrow : ∀ j, embWb k r γ i j = if i = j then 1 else 0 := by
    intro j
    unfold isW at hi
    simp only [embWb]
    rw [dif_neg (fun h => hi h.1)]
    by_cases h : i = j
    · subst h; simp [hi]
    · simp [h]
  simp [Matrix.mulVec, dotProduct, hrow]

theorem embWb_mulVec_eq_zero_on_isW (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ j, isW k r j → v j = 0) (i : Fin (2 * r + k + 1)) (hi : isW k r i) :
    (embWb k r γ *ᵥ v) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : isW k r j
  · rw [hv j hj, mul_zero]
  · have h0 : embWb k r γ i j = 0 := by
      unfold isW at hi hj
      simp only [embWb]
      rw [dif_neg (fun h => hj h.2), if_neg (fun h => h.2 hi)]
    rw [h0, zero_mul]

theorem measurable_invM : Measurable (invM : Mt k r → Mt k r) := by
  have hd : Continuous fun x : Mt k r => (Matrix.of x).det :=
    Continuous.matrix_det (continuous_id : Continuous fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => x)
  have ha : Continuous fun x : Mt k r => (Matrix.of x).adjugate :=
    Continuous.matrix_adjugate (continuous_id : Continuous fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => x)
  have h : (invM : Mt k r → Mt k r) = fun x i j => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by
    funext x i j
    simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact hd.measurable.inv.mul ((continuous_apply j).comp ((continuous_apply i).comp ha)).measurable

section cc

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

def cc (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  embWb k r γ *ᵥ (fun i => conj (((embWb k r γ)⁻¹ *ᵥ v) i))

theorem map_conj_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    A.map (starRingEnd ℂ) *ᵥ (fun i => conj (u i)) = fun i => conj ((A *ᵥ u) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem col_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : (M *ᵥ bvec j) i = M i j := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem conj_bvec {n : ℕ} (j : Fin n) : (fun i => conj (bvec j i)) = bvec j := by
  funext i
  simp [bvec, Pi.single_apply, apply_ite]

theorem embWb_fix_offW (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ j, isW k r j → v j = 0) :
    embWb k r γ *ᵥ v = v := by
  funext i
  by_cases hi : isW k r i
  · rw [embWb_mulVec_eq_zero_on_isW γ v hv i hi, hv i hi]
  · exact embWb_apply_offW γ v i hi

variable {γ}
variable (hE : IsUnit (embWb k r γ).det)
include hE

theorem embWb_inv_fix_offW (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ j, isW k r j → v j = 0) :
    (embWb k r γ)⁻¹ *ᵥ v = v := by
  have h := congrArg ((embWb k r γ)⁻¹ *ᵥ ·) (embWb_fix_offW γ v hv)
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec] at h
  exact h.symm

theorem embWb_inv_supW (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ j, ¬ isW k r j → v j = 0) :
    ∀ j, ¬ isW k r j → ((embWb k r γ)⁻¹ *ᵥ v) j = 0 := by
  intro j hj
  have h1 : embWb k r γ *ᵥ ((embWb k r γ)⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, Matrix.one_mulVec]
  have h2 := embWb_apply_offW γ ((embWb k r γ)⁻¹ *ᵥ v) j hj
  rw [h1] at h2
  rw [← h2]
  exact hv j hj

theorem cc_supW (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ j, ¬ isW k r j → v j = 0) :
    ∀ j, ¬ isW k r j → cc γ v j = 0 := by
  intro j hj
  unfold cc
  rw [embWb_apply_offW γ _ j hj]
  try dsimp only
  rw [embWb_inv_supW hE v hv j hj, map_zero]

theorem cc_offW (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ j, isW k r j → v j = 0) :
    cc γ v = fun i => conj (v i) := by
  unfold cc
  rw [embWb_inv_fix_offW hE v hv]
  exact embWb_fix_offW γ _ (fun j hj => by simp [hv j hj])

theorem cc_cc (v : Fin (2 * r + k + 1) → ℂ) : cc γ (cc γ v) = v := by
  have h1 : ∀ w, (embWb k r γ)⁻¹ *ᵥ (embWb k r γ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec]
  unfold cc
  rw [h1]
  have h3 : (fun i => conj (conj (((embWb k r γ)⁻¹ *ᵥ v) i))) = (embWb k r γ)⁻¹ *ᵥ v := by
    funext i; simp
  try dsimp only
  rw [h3, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, Matrix.one_mulVec]

theorem cc_add (u v : Fin (2 * r + k + 1) → ℂ) : cc γ (u + v) = cc γ u + cc γ v := by
  unfold cc
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [Matrix.mulVec_add]

theorem cc_smul (s : ℂ) (v : Fin (2 * r + k + 1) → ℂ) : cc γ (s • v) = conj s • cc γ v := by
  unfold cc
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [Matrix.mulVec_smul]

theorem gbar_mulVec_cc (g : Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    gbar k r γ g *ᵥ cc γ v = cc γ (g *ᵥ v) := by
  have h1 : ∀ w, (embWb k r γ)⁻¹ *ᵥ (embWb k r γ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec]
  have h2 : ∀ w, embWb k r γ *ᵥ ((embWb k r γ)⁻¹ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, Matrix.one_mulVec]
  unfold gbar cc
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, map_conj_mulVec _ ((embWb k r γ)⁻¹ *ᵥ v),
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]

theorem gbar_mul (g g' : Mat k r) : gbar k r γ (g * g') = gbar k r γ g * gbar k r γ g' := by
  unfold gbar
  have h : (embWb k r γ)⁻¹ * (g * g') * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * g' * embWb k r γ) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE]
  rw [h, Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE]

theorem gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  unfold gbar
  have h : (embWb k r γ)⁻¹ * (embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) *
      (embWb k r γ)⁻¹) * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE, Matrix.nonsing_inv_mul _ hE,
      Matrix.mul_one]
  have hc : ∀ M : Mat k r, (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := fun M => by
    ext i j; simp
  rw [h, hc]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hE, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hE]

theorem gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hE, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hE]

theorem gbar_inv (A : Mat k r) (hA : IsUnit A.det) : gbar k r γ A⁻¹ = (gbar k r γ A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← gbar_mul hE, Matrix.mul_nonsing_inv _ hA, gbar_one hE]

end cc

section mem

theorem bvec_offW (j : Fin (2 * r + k + 1)) (hj : ¬ isW k r j) : ∀ l, isW k r l → bvec j l = 0 := by
  intro l hl
  have h : l ≠ j := fun h => hj (h ▸ hl)
  simp [bvec, Pi.single_apply, h]

theorem bvec_supW (j : Fin (2 * r + k + 1)) (hj : isW k r j) : ∀ l, ¬ isW k r l → bvec j l = 0 := by
  intro l hl
  have h : l ≠ j := fun h => hl (h ▸ hj)
  simp [bvec, Pi.single_apply, h]

theorem not_isW_eI (a : Fin r) : ¬ isW k r (eI k r a) := by
  show ¬ (r ≤ a.val ∧ a.val ≤ r + k)
  have := a.isLt
  omega

theorem not_isW_esI (a : Fin r) : ¬ isW k r (esI k r a) := by
  show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val ≤ r + k)
  have := a.isLt
  omega

theorem Hpk_map_conj : (Hpk k r).map (starRingEnd ℂ) = Hpk k r := by
  ext i j
  simp only [Matrix.map_apply, Hpk]
  split_ifs <;> simp

theorem conj_mem_GV (A : Mat k r) (hA : A ∈ GV k r) : A.map (starRingEnd ℂ) ∈ GV k r := by
  have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
  change (A.map (starRingEnd ℂ))ᴴ * Hpk k r * A.map (starRingEnd ℂ) = Hpk k r
  have h1 : (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [h1, ← Hpk_map_conj, ← Matrix.map_mul, ← Matrix.map_mul, hA']

variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
variable (hG : IsClosedSubgroup (GV k r)) (hEG : embWb k r γ ∈ GV k r)
include hG hEG

theorem gbar_mem_GV (g : Mat k r) (hg : g ∈ GV k r) : gbar k r γ g ∈ GV k r := by
  unfold gbar
  have hEi := hG.inv_mem _ hEG
  exact hG.mul_mem _ (hG.mul_mem _ hEG _ (conj_mem_GV _ (hG.mul_mem _ (hG.mul_mem _ hEi _ hg) _ hEG))) _ hEi

theorem gbar_fix (g : Mat k r) (v : Fin (2 * r + k + 1) → ℂ) (hv : cc γ v = v) (hgv : g *ᵥ v = v) :
    gbar k r γ g *ᵥ v = v := by
  have hE := hG.unit _ hEG
  have h := gbar_mulVec_cc hE g v
  rw [hv, hgv, hv] at h
  exact h

theorem cc_bvec_offW (j : Fin (2 * r + k + 1)) (hj : ¬ isW k r j) : cc γ (bvec j) = bvec j := by
  rw [cc_offW (hG.unit _ hEG) _ (bvec_offW j hj)]
  exact conj_bvec j

theorem cc_embWb_bvec (j : Fin (k + 1)) :
    cc γ (embWb k r γ *ᵥ bvec (wI k r j)) = embWb k r γ *ᵥ bvec (wI k r j) := by
  have hE := hG.unit _ hEG
  unfold cc
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec, conj_bvec]

theorem gbar_mem_N (g : Mat k r) (hg : g ∈ Nset k r) : gbar k r γ g ∈ Nset k r := by
  have hE := hG.unit _ hEG
  simp only [Nset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have key1 : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      (g *ᵥ bvec (eI k r a)) i = bvec (eI k r a) i := by
    intro a i hai
    rw [col_apply, hg2 a i hai]
    simp [bvec, Pi.single_apply]
  have key2 : ∀ y : Fin (2 * r + k + 1) → ℂ, (∀ l, ¬ isW k r l → y l = 0) →
      ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (g *ᵥ y) i = y i := by
    intro y hy i hi
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hiW : isW k r i
      · obtain ⟨h1, h2⟩ : r ≤ i.val ∧ i.val ≤ r + k := hiW
        rw [hg3 i i h1 h2 hi, if_pos rfl, one_mul]
      · rw [hy i hiW, mul_zero]
    · intro l _ hli
      by_cases hl : isW k r l
      · obtain ⟨h1, h2⟩ : r ≤ l.val ∧ l.val ≤ r + k := hl
        rw [hg3 i l h1 h2 hi, if_neg (Ne.symm hli), zero_mul]
      · rw [hy l hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine ⟨gbar_mem_GV hG hEG g hg1, ?_, ?_⟩
  · intro a i hai
    rw [show gbar k r γ g i (eI k r a) = (gbar k r γ g *ᵥ bvec (eI k r a)) i from (col_apply _ _ _).symm]
    rw [← cc_bvec_offW hG hEG (eI k r a) (not_isW_eI a), gbar_mulVec_cc hE]
    have hd : ∀ l, isW k r l → (g *ᵥ bvec (eI k r a) - bvec (eI k r a)) l = 0 := by
      intro l hl
      obtain ⟨h1, _⟩ : r ≤ l.val ∧ l.val ≤ r + k := hl
      rw [Pi.sub_apply, key1 a l (by have := a.isLt; omega), sub_self]
    have hc : g *ᵥ bvec (eI k r a) = bvec (eI k r a) + (g *ᵥ bvec (eI k r a) - bvec (eI k r a)) := by
      abel
    rw [hc, cc_add hE, cc_bvec_offW hG hEG (eI k r a) (not_isW_eI a), cc_offW hE _ hd]
    simp only [Pi.add_apply, Pi.sub_apply, key1 a i hai, sub_self, map_zero, add_zero]
    simp [bvec, Pi.single_apply]
  · intro i j hj1 hj2 hi
    have hjW : isW k r j := show r ≤ j.val ∧ j.val ≤ r + k from ⟨hj1, hj2⟩
    rw [show gbar k r γ g i j = (gbar k r γ g *ᵥ bvec j) i from (col_apply _ _ _).symm]
    rw [← cc_cc hE (bvec j), gbar_mulVec_cc hE]
    have hy : ∀ l, ¬ isW k r l → cc γ (bvec j) l = 0 := cc_supW hE _ (bvec_supW j hjW)
    have hd : ∀ l, isW k r l → (g *ᵥ cc γ (bvec j) - cc γ (bvec j)) l = 0 := by
      intro l hl
      obtain ⟨h1, _⟩ : r ≤ l.val ∧ l.val ≤ r + k := hl
      rw [Pi.sub_apply, key2 _ hy l h1, sub_self]
    have hc : g *ᵥ cc γ (bvec j) = cc γ (bvec j) + (g *ᵥ cc γ (bvec j) - cc γ (bvec j)) := by
      abel
    rw [hc, cc_add hE, cc_cc hE, cc_offW hE _ hd]
    simp only [Pi.add_apply, Pi.sub_apply, key2 _ hy i hi, sub_self, map_zero, add_zero]
    simp [bvec, Pi.single_apply]

theorem gbar_mem_UW (z : Fin (2 * r + k + 1) → ℂ) (hz : cc γ z = z) (g : Mat k r) (hg : g ∈ UWset k r z) :
    gbar k r γ g ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hg1, hg2, hg3⟩ := hg
  refine ⟨gbar_mem_GV hG hEG g hg1, fun a => ⟨?_, ?_⟩, gbar_fix hG hEG g z hz hg3⟩
  · exact gbar_fix hG hEG g _ (cc_bvec_offW hG hEG _ (not_isW_eI a)) (hg2 a).1
  · exact gbar_fix hG hEG g _ (cc_bvec_offW hG hEG _ (not_isW_esI a)) (hg2 a).2

theorem frame_conjugation_fixes_point (z : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z)
    (hfr : embWb k r γ *ᵥ bvec (wI k r (Fin.last k)) = (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) :
    cc γ z = z := by
  have hE := hG.unit _ hEG
  have hz : z = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • (embWb k r γ *ᵥ bvec (wI k r (Fin.last k))) := by
    rw [hfr, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hT).ne', Complex.ofReal_one,
      one_smul]
  rw [hz, cc_smul hE, cc_embWb_bvec hG hEG, Complex.conj_ofReal]

theorem gbar_mem_UU (z : Fin (2 * r + k + 1) → ℂ) (hz : cc γ z = z) (u : Mat k r) (hu : u ∈ UUset k r z γ) :
    gbar k r γ u ∈ UUset k r z γ := by
  simp only [UUset, Set.mem_setOf_eq] at hu ⊢
  obtain ⟨hu1, hu2⟩ := hu
  have hw : cc γ (w1 k r γ) = w1 k r γ := by
    unfold w1; exact cc_embWb_bvec hG hEG 0
  exact ⟨gbar_mem_UW hG hEG z hz u hu1, gbar_fix hG hEG u _ hw hu2⟩

end mem

end InvGrp

end ReciprocityTheory.ChartRestriction.DS.Mult1
