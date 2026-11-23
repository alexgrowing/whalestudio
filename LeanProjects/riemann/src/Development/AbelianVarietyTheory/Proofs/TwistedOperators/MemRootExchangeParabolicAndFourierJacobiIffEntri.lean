import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ParabolicEntries

open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def Par (L : ℕ) (b : Fin c → ℕ) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Prop :=
  ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r →
    M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s

omit [Fintype n] in
theorem Par.blockTri {L : ℕ} {b : Fin c → ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M) :
    M.BlockTriangular (Sum.elim (fun _ => L) b) := by
  intro r s hrs
  have hne : r ≠ s := by
    rintro rfl
    exact lt_irrefl _ hrs
  rw [h r s _ hrs.le, Matrix.one_apply_ne hne]
  rcases r with r | r <;> rcases s with s | s <;> simp_all

theorem Par.mul_left {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hr : r.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M * M') r s = M' r s := by
  have : (M * M') r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b t) (Sum.elim (fun _ => L) b r) with ht | ht
    · rw [h r t (Or.inl hr) ht]
    · rw [h' (lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul]

theorem Par.mul_right {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hs : s.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M' * M) r s = M' r s := by
  have : (M' * M) r s = (M' * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b s) (Sum.elim (fun _ => L) b t) with ht | ht
    · rw [h t s (Or.inr hs) ht]
    · rw [h' (lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [this, Matrix.mul_one]

theorem Par.blockTri_inv {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (h : Par L b g.val) :
    (g⁻¹).val.BlockTriangular (Sum.elim (fun _ => L) b) := by
  letI : Invertible g.val := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri

def parGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (L : ℕ) (b : Fin c → ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Par L b g.val}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh r s hor hrs
    rw [Units.val_mul]
    rcases hor with hr | hs
    · rw [Par.mul_left hg (Par.blockTri hh) hr hrs, hh r s (Or.inl hr) hrs]
    · rw [Par.mul_right hh (Par.blockTri hg) hs hrs, hg r s (Or.inr hs) hrs]
  inv_mem' := by
    intro g hg r s hor hrs
    rcases hor with hr | hs
    · rw [← Par.mul_left hg (Par.blockTri_inv hg) hr hrs, Units.mul_inv]
    · rw [← Par.mul_right hg (Par.blockTri_inv hg) hs hrs, Units.inv_mul]

theorem embX_mem (L : ℕ) (b : Fin c → ℕ) (x : GL n k) : embX c x ∈ parGroup k n L b := by
  intro r s hor _
  rw [embX_val]
  rcases r with r | r <;> rcases s with s | s <;> simp_all [Matrix.one_apply]

theorem toBlocks₁₁_mul {L : ℕ} {b : Fin c → ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b)
    (hh : h ∈ parGroup k n L b) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  ext r s
  simp only [Units.val_mul, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [add_eq_left]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases le_total (b t) L with ht | ht
  · rw [hg (Sum.inl r) (Sum.inr t) (by simp) ht, Matrix.one_apply_ne (by simp), zero_mul]
  · rw [hh (Sum.inr t) (Sum.inl s) (by simp) ht, Matrix.one_apply_ne (by simp), mul_zero]

theorem exists_eq_embX_mul {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b) :
    ∃ (x : GL n k) (u : GL (n ⊕ Fin c) k), Uni (Sum.elim (fun _ => L) b) u.val ∧ g = embX c x * u := by
  have h1 : ((1 : GL (n ⊕ Fin c) k)).val.toBlocks₁₁ = 1 := by
    ext r s
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  let x : GL n k := ⟨g.val.toBlocks₁₁, (g⁻¹).val.toBlocks₁₁,
    by rw [← toBlocks₁₁_mul hg (inv_mem hg), mul_inv_cancel, h1],
    by rw [← toBlocks₁₁_mul (inv_mem hg) hg, inv_mul_cancel, h1]⟩
  refine ⟨x, embX c x⁻¹ * g, ?_, by rw [map_inv, mul_inv_cancel_left]⟩
  have hm : embX c x⁻¹ * g ∈ parGroup k n L b := mul_mem (embX_mem L b _) hg
  have h11 : (embX c x⁻¹ * g).val.toBlocks₁₁ = 1 := by
    rw [toBlocks₁₁_mul (embX_mem L b _) hg, embX_val, Matrix.toBlocks_fromBlocks₁₁]
    exact x.inv_mul
  intro r s hrs
  by_cases hor : r.isRight ∨ s.isRight
  · exact hm r s hor hrs
  · rcases r with r | r <;> rcases s with s | s
    · have := congrFun (congrFun h11 r) s
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at this
      rw [this]
      simp [Matrix.one_apply]
    all_goals simp at hor

theorem embX_mem_R (p : ℕ) (x : GL n k) : embX c x ∈ R k n c p :=
  Subgroup.mem_sup_left ⟨x, rfl⟩

theorem R_le {L p : ℕ} {b : Fin c → ℕ} (h : N k n c p ≤ parGroup k n L b) : R k n c p ≤ parGroup k n L b := by
  refine sup_le ?_ h
  rintro _ ⟨x, rfl⟩
  exact embX_mem L b x

theorem mem_R_iff_and_mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  intro k _ n _ _ c ρ
  refine ⟨fun g => ⟨fun hg => ?_, fun hg => ?_⟩, fun h1 hc g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · exact R_le (L := ρ) (b := fun i : Fin c => i.val + 1)
      (fun u hu r s _ hrs => (mem_N_iff u).1 hu r s hrs) hg
  · obtain ⟨x, u, hu, rfl⟩ := exists_eq_embX_mul (L := ρ) (b := fun i : Fin c => i.val + 1) hg
    exact mul_mem (embX_mem_R ρ x) (Subgroup.mem_sup_right ((mem_N_iff u).2 hu))
  · have hN : NFJ k n c ρ ≤ parGroup k n (2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) :=
      fun u hu r s _ hrs => ((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).1 hu r s hrs
    exact sup_le (R_le (le_sup_left.trans hN)) (R_le (le_sup_right.trans hN)) hg
  · obtain ⟨x, u, hu, rfl⟩ :=
      exists_eq_embX_mul (L := 2 * ρ + 1) (b := fun i : Fin c => 2 * (i.val + 1)) hg
    have hN : NFJ k n c ρ ≤ RFJ k n c ρ := sup_le_sup le_sup_right le_sup_right
    exact mul_mem (Subgroup.mem_sup_left (embX_mem_R ρ x))
      (hN (((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).2 hu))

end GlobalTheory.RootEx.ParabolicEntries
