import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

namespace GlobalTheory.ConstLat.MinorQuot

variable {K : Type} [Field K] (w : AbsoluteValue K ℝ) {n g : ℕ} (H : Matrix (Fin n) (Fin g) K)

theorem colMinor_nonneg (S : Finset (Fin g)) : 0 ≤ colMinor w H S :=
  Real.iSup_nonneg fun _ => w.nonneg _

theorem det_reindex {k : ℕ} {S : Finset (Fin g)} (e : Fin k ≃ S) (σ : S → Fin n) :
    (H.submatrix σ Subtype.val).det = (H.submatrix (σ ∘ e) (fun j => (e j).1)).det := by
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem le_colMinor {k : ℕ} {S : Finset (Fin g)} (e : Fin k ≃ S) (τ : Fin k → Fin n) :
    w (H.submatrix τ (fun j => (e j).1)).det ≤ colMinor w H S := by
  have h := le_ciSup (f := fun σ : S → Fin n => w (H.submatrix σ Subtype.val).det)
    (Set.finite_range _).bddAbove (τ ∘ e.symm)
  have h2 : (τ ∘ e.symm) ∘ e = τ := by ext j; simp
  have h3 := det_reindex H e (τ ∘ e.symm)
  rw [h2] at h3
  rw [← h3]
  exact h

theorem colMinor_le {k : ℕ} {S : Finset (Fin g)} (e : Fin k ≃ S) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ τ : Fin k → Fin n, w (H.submatrix τ (fun j => (e j).1)).det ≤ r) : colMinor w H S ≤ r := by
  refine Real.iSup_le (fun σ => ?_) hr
  rw [det_reindex H e]
  exact h _

theorem exists_eq_colMinor {k : ℕ} {S : Finset (Fin g)} (e : Fin k ≃ S) (h : 0 < colMinor w H S) :
    ∃ τ : Fin k → Fin n, w (H.submatrix τ (fun j => (e j).1)).det = colMinor w H S := by
  rcases isEmpty_or_nonempty (S → Fin n) with h0 | h0
  · unfold colMinor at h
    rw [Real.iSup_of_isEmpty] at h
    exact absurd h (lt_irrefl _)
  · obtain ⟨σ, hσ⟩ := exists_eq_ciSup_of_finite (f := fun σ : S → Fin n => w (H.submatrix σ Subtype.val).det)
    exact ⟨σ ∘ e, by rw [← det_reindex H e]; exact hσ⟩

theorem exists_equiv_insert {k : ℕ} {S : Finset (Fin g)} (e : Fin k ≃ S) {i : Fin g} (hi : i ∉ S) :
    ∃ e' : Fin (k + 1) ≃ (insert i S : Finset (Fin g)), (e' 0).1 = i ∧ ∀ j, (e' j.succ).1 = (e j).1 := by
  let f : Fin (k + 1) → (insert i S : Finset (Fin g)) :=
    Fin.cons ⟨i, Finset.mem_insert_self _ _⟩ fun j => ⟨(e j).1, Finset.mem_insert_of_mem (e j).2⟩
  have hf : Function.Bijective f := by
    constructor
    · refine Fin.cons_injective_iff.2 ⟨?_, ?_⟩
      · rintro ⟨j, hj⟩
        have : (e j).1 = i := congrArg Subtype.val hj
        exact hi (this ▸ (e j).2)
      · intro a b hab
        have : (e a).1 = (e b).1 := congrArg (fun x : (insert i S : Finset (Fin g)) => x.1) hab
        exact e.injective (Subtype.ext this)
    · rintro ⟨x, hx⟩
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact ⟨0, rfl⟩
      · refine ⟨(e.symm ⟨x, hx'⟩).succ, Subtype.ext ?_⟩
        simp [f]
  exact ⟨Equiv.ofBijective f hf, rfl, fun j => rfl⟩

theorem mulVec_eq_sum {k : ℕ} {S : Finset (Fin g)} (e : Fin k ≃ S) (u : Fin g → K) (hu : ∀ l, l ∉ S → u l = 0)
    (r : Fin n) : H.mulVec u r = ∑ j, u (e j).1 * H r (e j).1 := by
  rw [Equiv.sum_comp e (fun s : S => u s.1 * H r s.1), Finset.sum_coe_sort S (fun s => u s * H r s)]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => by rw [hu l hl, mul_zero])]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem det_expand {k : ℕ} {S : Finset (Fin g)} {i : Fin g} (e : Fin k ≃ S)
    (e' : Fin (k + 1) ≃ (insert i S : Finset (Fin g))) (h0 : (e' 0).1 = i) (hs : ∀ j, (e' j.succ).1 = (e j).1)
    (u : Fin g → K) (hu1 : u i = 1) (hu : ∀ l, l ∉ S → l ≠ i → u l = 0) (τ : Fin (k + 1) → Fin n) :
    (H.submatrix τ (fun j => (e' j).1)).det =
      ∑ r : Fin (k + 1), (-1) ^ (r : ℕ) * H.mulVec u (τ r) *
        (H.submatrix (τ ∘ r.succAbove) (fun j => (e j).1)).det := by
  have h := Matrix.det_updateCol_sum (H.submatrix τ (fun j => (e' j).1)) 0 (fun j => u (e' j).1)
  rw [h0, hu1, one_smul] at h
  rw [← h, Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 2
  · rw [Matrix.updateCol_self, mulVec_eq_sum H e' u (fun l hl => by
      rw [Finset.mem_insert, not_or] at hl
      exact hu l hl.2 hl.1)]
    simp
  · ext a b
    simp [Matrix.updateCol_ne (Fin.succ_ne_zero b), hs]

theorem apply_sum_le (hw : IsNonarchimedean w) {ι : Type} (s : Finset ι) (f : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ a ∈ s, w (f a) ≤ r) : w (∑ a ∈ s, f a) ≤ r := by
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans (max_le (h a (Finset.mem_insert_self _ _))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb)))

theorem colMinor_insert_le (hw : IsNonarchimedean w) (S : Finset (Fin g)) {i : Fin g} (hi : i ∉ S)
    (u : Fin g → K) (hu1 : u i = 1) (hu : ∀ l, l ∉ S → l ≠ i → u l = 0) :
    colMinor w H (insert i S) ≤ colMinor w H S * supN w (H.mulVec u) := by
  let e := S.equivFin.symm
  obtain ⟨e', h0, hs⟩ := exists_equiv_insert e hi
  have hr : 0 ≤ colMinor w H S * supN w (H.mulVec u) := mul_nonneg (colMinor_nonneg w H S) (supN_nonneg w _)
  refine colMinor_le w H e' hr fun τ => ?_
  rw [det_expand H e e' h0 hs u hu1 hu]
  refine apply_sum_le w hw _ _ hr fun r _ => ?_
  rw [map_mul, map_mul, map_pow, w.map_neg, map_one, one_pow, one_mul, mul_comm]
  exact mul_le_mul (le_colMinor w H e _) (le_supN w _ _) (w.nonneg _) (colMinor_nonneg w H S)

theorem exists_le_colMinor_insert (S : Finset (Fin g)) {i : Fin g} (hi : i ∉ S) (hS : 0 < colMinor w H S) :
    ∃ u : Fin g → K, u i = 1 ∧ (∀ l, l ∉ S → l ≠ i → u l = 0) ∧
      colMinor w H S * supN w (H.mulVec u) ≤ colMinor w H (insert i S) := by
  let e := S.equivFin.symm
  obtain ⟨e', h0, hs⟩ := exists_equiv_insert e hi
  obtain ⟨σ, hσ⟩ := exists_eq_colMinor w H e hS
  have hd : (H.submatrix σ (fun j => (e j).1)).det ≠ 0 := by
    intro h
    rw [h, map_zero] at hσ
    exact hS.ne hσ
  obtain ⟨a, ha⟩ := (Matrix.mulVec_surjective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 hd.isUnit)) (fun j => -H (σ j) i)
  let u : Fin g → K := fun l => if h : l ∈ S then a (e.symm ⟨l, h⟩) else if l = i then 1 else 0
  have hu1 : u i = 1 := by simp [u, hi]
  have hu : ∀ l, l ∉ S → l ≠ i → u l = 0 := fun l h1 h2 => by simp [u, h1, h2]
  have hue : ∀ j, u (e j).1 = a j := fun j => by simp [u]
  have hz : ∀ j, H.mulVec u (σ j) = 0 := by
    intro j
    rw [mulVec_eq_sum H e' u (fun l hl => by
      rw [Finset.mem_insert, not_or] at hl
      exact hu l hl.2 hl.1), Fin.sum_univ_succ]
    simp only [h0, hs, hu1, hue, one_mul]
    have := congrFun ha j
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at this
    simp only [mul_comm (a _)]
    rw [this, add_neg_cancel]
  refine ⟨u, hu1, hu, ?_⟩
  rw [mul_comm, ← le_div_iff₀ hS]
  refine supN_le w (div_nonneg (colMinor_nonneg w H _) hS.le) fun m => ?_
  rw [le_div_iff₀ hS]
  have h := le_colMinor w H e' (Fin.cons m σ)
  rw [det_expand H e e' h0 hs u hu1 hu, Fin.sum_univ_succ] at h
  simp only [Fin.cons_succ, hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.cons_zero, Fin.val_zero,
    pow_zero, one_mul, map_mul] at h
  rw [← hσ]
  exact h

theorem colMinor_pos (hH : Function.Injective H.mulVec) (S : Finset (Fin g)) : 0 < colMinor w H S := by
  induction S using Finset.induction_on with
  | empty => rw [colMinor_empty]; exact one_pos
  | insert i S hi ih =>
    obtain ⟨u, hu1, -, h⟩ := exists_le_colMinor_insert w H S hi ih
    refine lt_of_lt_of_le (mul_pos ih ?_) h
    have hne : H.mulVec u ≠ 0 := by
      intro h0
      have : u = 0 := hH (by rw [h0, Matrix.mulVec_zero])
      rw [this] at hu1
      exact zero_ne_one hu1
    obtain ⟨r, hr⟩ := Function.ne_iff.1 hne
    exact (w.pos hr).trans_le (le_supN w _ r)

theorem injective_of_colMinor_pos (h : 0 < colMinor w H Finset.univ) : Function.Injective H.mulVec := by
  let e := (Finset.univ : Finset (Fin g)).equivFin.symm
  obtain ⟨σ, hσ⟩ := exists_eq_colMinor w H e h
  have hd : (H.submatrix σ (fun j => (e j).1)).det ≠ 0 := by
    intro h'
    rw [h', map_zero] at hσ
    exact h.ne hσ
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hd.isUnit)
  intro u v huv
  have : (fun j => u (e j).1) = fun j => v (e j).1 := by
    apply hinj
    ext r
    have h1 := congrFun huv (σ r)
    rw [mulVec_eq_sum H e u (by simp), mulVec_eq_sum H e v (by simp)] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    simpa only [mul_comm] using h1
  ext l
  have h2 := congrFun this (e.symm ⟨l, Finset.mem_univ l⟩)
  simp only [Equiv.apply_symm_apply] at h2
  exact h2

theorem colMinor_pos_and_quotient : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ {n g : ℕ} (H : Matrix (Fin n) (Fin g) K),
    (0 < colMinor w H Finset.univ ↔ Function.Injective H.mulVec) ∧
    (Function.Injective H.mulVec → (∀ S, 0 < colMinor w H S) ∧ ∀ (S : Finset (Fin g)) (i : Fin g), i ∉ S →
      (∀ u : Fin g → K, u i = 1 → (∀ l, l ∉ S → l ≠ i → u l = 0) →
        colMinor w H (insert i S) ≤ colMinor w H S * supN w (H.mulVec u)) ∧
      ∃ u : Fin g → K, u i = 1 ∧ (∀ l, l ∉ S → l ≠ i → u l = 0) ∧
        colMinor w H (insert i S) = colMinor w H S * supN w (H.mulVec u)) := by
  intro K _ w hw n g H
  refine ⟨⟨injective_of_colMinor_pos w H, fun h => colMinor_pos w H h _⟩, fun h =>
    ⟨colMinor_pos w H h, fun S i hi => ⟨colMinor_insert_le w H hw S hi, ?_⟩⟩⟩
  obtain ⟨u, h1, h2, h3⟩ := exists_le_colMinor_insert w H S hi (colMinor_pos w H h S)
  exact ⟨u, h1, h2, le_antisymm (colMinor_insert_le w H hw S hi u h1 h2) h3⟩

end GlobalTheory.ConstLat.MinorQuot
