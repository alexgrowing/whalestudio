import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentTerms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms

variable {k : Type} [Field k] [ValuativeRel k]

section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_act {g : GL ι k} {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g M ↔ ∃ w ∈ M, g.val *ᵥ w = v := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv {g : GL ι k} {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g M ↔ (g⁻¹).val *ᵥ v ∈ M := by
  rw [_root_.GlobalTheory.RootEx.UnfoldShape.mem_act]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro hv
    refine ⟨_, hv, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.act_one (M : Submodule 𝒪[k] (ι → k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act (1 : GL ι k) M = M := by
  ext v
  simp [_root_.GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.act_mul (g h : GL ι k) (M : Submodule 𝒪[k] (ι → k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act (g * h) M = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act h M) := by
  ext v
  simp only [_root_.GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
omit [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_smul_iff {ϖ : 𝒪[k]} {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ ϖ • M ↔ ∃ w ∈ M, (ϖ : k) • w = v := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem mem_smul_iff_inv {ϖ : 𝒪[k]} (h : (ϖ : k) ≠ 0) {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ ϖ • M ↔ (ϖ : k)⁻¹ • v ∈ M := by
  rw [mem_smul_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [inv_smul_smul₀ h]
  · intro hv
    exact ⟨_, hv, smul_inv_smul₀ h v⟩

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
omit [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_stdLat {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat k ι ↔ ∀ i, v i ∈ 𝒪[k] := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
    Submodule.mem_one]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨v i, h⟩, rfl⟩⟩
  rintro ⟨a, ha⟩
  rw [← ha]
  exact a.2

end

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] in
theorem inX_apply (v : n → k) : inX k n c v = Sum.elim v 0 := rfl

omit [Fintype n] [DecidableEq n] in
theorem mem_Yle {i : ℕ} {v : n ⊕ Fin c → k} :
    v ∈ Yle k n c i ↔ ∀ l : Fin c, i < l.val + 1 → v (Sum.inr l) = 0 := Iff.rfl

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [Fintype n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)} {v : n ⊕ Fin c → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L ↔
      (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, ∃ a : 𝒪[k], v (Sum.inr i) = a * (ϖ : k) ^ (i.val + 1) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    refine ⟨?_, fun i => ⟨a i, ?_⟩⟩
    · simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply] using hw
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply, Subring.smul_def]
  · rintro ⟨hL, ha⟩
    choose a ha using ha
    refine ⟨_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX k n c (fun r => v (Sum.inl r)),
      Submodule.mem_map_of_mem hL,
      ∑ i, a i • ((ϖ : k) ^ (i.val + 1) • _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux k n i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    funext r
    rcases r with r | i
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply]
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply, Subring.smul_def, ha i]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [Fintype n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.inX_mem_chainLat {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)} {v : n → k} :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX k n c v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L ↔ v ∈ L := by
  rw [_root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i => ⟨0, by simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX]⟩⟩⟩

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [Fintype n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.scaled_basis_mem_chainLattice (ϖ : 𝒪[k]) (L : Submodule 𝒪[k] (n → k)) (i : Fin c) :
    (ϖ : k) ^ (i.val + 1) • _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux k n i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

def colMat (n' : Type) (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => Sum.elim (fun _ => 0) (fun j : Fin (c + 1) => Fin.cases 0 (fun i => y i r) j) s

open Classical in

def col (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) : n ⊕ Fin c → k :=
  fun r => if h : Free (n' := n') 1 (r, Sum.inr i.succ) then e ⟨_, h⟩ else 0

def uncol (n' : Type) (y : Fin c → (n ⊕ Fin c → k)) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k := fun rs => colMat n' y rs.1.1 rs.1.2

section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem pt_eq (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) : pt x₀ y = basePt c x₀ + colMat n' y := rfl

theorem colMat_add (y z : Fin c → (n ⊕ Fin c → k)) : colMat n' (y + z) = colMat n' y + colMat n' z := by
  ext r (s | s)
  · simp [colMat]
  · refine Fin.cases ?_ (fun i => ?_) s <;> simp [colMat]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.colMat_smul (a : k) (y : Fin c → (n ⊕ Fin c → k)) :
    _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' (a • y) = a • _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y := by
  ext r (s | j)
  · simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
  · refine Fin.cases ?_ (fun i => ?_) j <;> simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]

theorem pt_add (x₀ : Matrix n n' k) (y z : Fin c → (n ⊕ Fin c → k)) :
    pt x₀ (y + z) = pt x₀ y + colMat n' z := by
  rw [pt_eq, pt_eq, colMat_add, add_assoc]

theorem pt_add_base (x₀ x₁ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) :
    pt (x₀ + x₁) y = pt x₀ y + fromBlocks x₁ 0 0 0 := by
  ext (r | r) (s | s) <;> simp [pt_eq, basePt, colMat]

theorem col_add (e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    col (e + e') = col e + col e' := by
  ext i r
  simp only [col, Pi.add_apply]
  split_ifs <;> simp

theorem col_smul (a : k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    col (a • e) = a • col e := by
  ext i r
  simp only [col, Pi.smul_apply]
  split_ifs <;> simp

theorem colMat_col (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (r s) :
    colMat n' (col e) r s = open Classical in if h : Free 1 (r, s) then e ⟨(r, s), h⟩ else 0 := by
  rcases s with s | s
  · rw [dif_neg]
    · simp [colMat]
    · rcases r with r | r <;> simp [Free]
  · refine Fin.cases ?_ (fun i => ?_) s
    · rw [dif_neg]
      · simp [colMat]
      · rcases r with r | r <;> simp [Free]
    · simp [colMat, col]

theorem affPt_eq_pt (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    affPt 1 x₀ e = pt x₀ (col e) := by
  ext r s
  simp only [affPt, pt_eq, Matrix.add_apply, Matrix.of_apply, colMat_col]

theorem ch_pt (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) : ch (pt x₀ y) = ∑ i, y i (Sum.inr i) := by
  simp [ch, pt_eq, basePt, colMat]

end

section
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem col_mem_Yle (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    col e i ∈ Yle k n c (i.val + 1) := by
  intro l hl
  rw [col, dif_neg]
  simp only [Free, Fin.val_succ]
  omega

theorem col_uncol {y : Fin c → (n ⊕ Fin c → k)} (hy : ∀ i, y i ∈ Yle k n c (i.val + 1)) :
    col (uncol n' y) = y := by
  ext i r
  rw [col]
  split_ifs with h
  · simp [uncol, colMat]
  · rcases r with r | r
    · simp [Free] at h
    · simp only [Free, Fin.val_succ] at h
      exact (hy i r (by omega)).symm

end

section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [DecidableEq n']

theorem colMat_mulVec (y : Fin c → (n ⊕ Fin c → k)) (v : n' ⊕ Fin (c + 1) → k) :
    colMat n' y *ᵥ v = ∑ i, v (Sum.inr i.succ) • y i := by
  ext r
  simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Finset.sum_apply, mul_comm]

theorem basePt_mulVec (x₀ : Matrix n n' k) (v : n' ⊕ Fin (c + 1) → k) :
    basePt c x₀ *ᵥ v = Sum.elim (x₀ *ᵥ fun s => v (Sum.inl s)) fun l => v (Sum.inr l.castSucc) := by
  ext (r | r)
  · simp [basePt, Matrix.mulVec, dotProduct]
  · simp only [basePt, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.of_apply, Sum.elim_inr]
    rw [Finset.sum_eq_single r.castSucc]
    · simp
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro h
      exact hj (Fin.ext (by simp [h]))
    · simp

end

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem pt_mulVec_inX (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) (v : n' → k) :
    pt x₀ y *ᵥ inX k n' (c + 1) v = inX k n c (x₀ *ᵥ v) := by
  rw [pt_eq, Matrix.add_mulVec, colMat_mulVec, basePt_mulVec]
  ext (r | r) <;> simp [inX_apply]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
omit [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mapsInto_colMat {ϖ : 𝒪[k]} {L' : Submodule 𝒪[k] (n' → k)}
    {Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)} {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, (ϖ : k) ^ (i.val + 2) • y i ∈ Λ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.MapsInto (_root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ (c + 1) L') Λ := by
  intro v hv
  obtain ⟨-, ha⟩ := _root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat.1 hv
  choose a ha using ha
  have hsum : _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y *ᵥ v = ∑ i : Fin c, a i.succ • ((ϖ : k) ^ (i.val + 2) • y i) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, _root_.GlobalTheory.RootEx.UnfoldShape.colMat, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Subring.smul_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i.succ, Fin.val_succ]
    ring
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hy i)

omit [Fintype n] in
theorem mapsInto_basePt {ϖ : 𝒪[k]} {L' : Submodule 𝒪[k] (n' → k)} {L : Submodule 𝒪[k] (n → k)}
    {x₀ : Matrix n n' k} (h : MapsInto x₀ L' L) :
    MapsInto (basePt c x₀) (chainLat ϖ (c + 1) L') (chainLat ϖ c L) := by
  intro v hv
  rw [basePt_mulVec, mem_chainLat]
  obtain ⟨h1, h2⟩ := mem_chainLat.1 hv
  exact ⟨h _ h1, fun i => h2 i.castSucc⟩

variable [MeasurableSpace k] [BorelSpace k]

open Classical in
theorem opE_one_eq (ψ : AddChar k Circle) (ν : Measure k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x₀ : Matrix n n' k) :
    opE ψ ν 1 Ψ x₀ = ∫ e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k,
      Ψ (pt x₀ (col e)) * (ψ (-∑ i, col e i (Sum.inr i)) : ℂ) ∂(Measure.pi fun _ => ν) := by
  simp only [opE, affPt_eq_pt, ch_pt]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem affPt_eq_pt_col (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) :
    _root_.GlobalTheory.RootEx.affPt 1 x₀ e = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt x₀ (_root_.GlobalTheory.RootEx.UnfoldShape.col e) := by
  unfold _root_.GlobalTheory.RootEx.affPt _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt
  congr 1
  ext r s
  rcases s with s | j
  · rcases r with r | l <;> simp [_root_.GlobalTheory.RootEx.Free]
  · refine Fin.cases ?_ (fun i => ?_) j
    · rcases r with r | l <;> simp [_root_.GlobalTheory.RootEx.Free]
    · by_cases h : _root_.GlobalTheory.RootEx.Free (n' := n') 1 (r, Sum.inr i.succ) <;>
        simp [_root_.GlobalTheory.RootEx.UnfoldShape.col, h]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem col_mem_Yle' [ValuativeRel k]
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) (i : Fin c) :
    _root_.GlobalTheory.RootEx.UnfoldShape.col e i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1) := by
  intro l hl
  simp only [_root_.GlobalTheory.RootEx.UnfoldShape.col]
  rw [dif_neg]
  simp only [_root_.GlobalTheory.RootEx.Free, Fin.val_succ]
  omega

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable [MeasurableSpace k] [BorelSpace k] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.exists_pt_ne_zero {ψ : AddChar k Circle} {ν : Measure k}
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ y : Fin c → (n ⊕ Fin c → k), (∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) ∧
      Ψ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt x₀ y) ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply h
  have hzero : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt 1 x₀ e) = 0 := fun e => by
    rw [affPt_eq_pt_col]
    exact hne _ fun i => col_mem_Yle' e i
  unfold _root_.GlobalTheory.RootEx.opE
  simp [hzero]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem colMat_eq_zero_of_not_free [ValuativeRel k] {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : ¬ _root_.GlobalTheory.RootEx.Free 1 (r, s)) : _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y r s = 0 := by
  rcases s with s | j
  · simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
  · induction j using Fin.cases with
    | zero => simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
    | succ i =>
      simp only [_root_.GlobalTheory.RootEx.UnfoldShape.colMat, Matrix.of_apply, Sum.elim_inr, Fin.cases_succ]
      rcases r with r | l
      · exact absurd (by simp [_root_.GlobalTheory.RootEx.Free]) h
      · apply hy i l
        simp only [_root_.GlobalTheory.RootEx.Free, Fin.val_succ] at h
        omega

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem affPt_add_uncol [ValuativeRel k] (x₀ : Matrix n n' k) {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1))
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) :
    _root_.GlobalTheory.RootEx.affPt 1 x₀ (e + _root_.GlobalTheory.RootEx.UnfoldShape.uncol n' y) =
      _root_.GlobalTheory.RootEx.affPt 1 x₀ e + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y := by
  unfold _root_.GlobalTheory.RootEx.affPt
  rw [add_assoc]
  congr 1
  ext r s
  by_cases h : _root_.GlobalTheory.RootEx.Free 1 (r, s)
  · simp [h, _root_.GlobalTheory.RootEx.UnfoldShape.uncol]
  · simp [h, colMat_eq_zero_of_not_free hy h]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem ch_add_colMat (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : Fin c → (n ⊕ Fin c → k)) :
    _root_.GlobalTheory.RootEx.ch (x + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) =
      _root_.GlobalTheory.RootEx.ch x + ∑ i, y i (Sum.inr i) := by
  simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib, _root_.GlobalTheory.RootEx.UnfoldShape.colMat]

open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable [MeasurableSpace k] [BorelSpace k] in

theorem _root_.GlobalTheory.RootEx.UnfoldShape.opE_translate (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) (hΨ : ∀ x, Ψ (x + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) = Ψ x)
    (x₀ : Matrix n n' k) :
    _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ = (ψ (-∑ i, y i (Sum.inr i)) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  unfold _root_.GlobalTheory.RootEx.opE
  conv_lhs => rw [← integral_add_right_eq_self _ (_root_.GlobalTheory.RootEx.UnfoldShape.uncol n' y)]
  rw [← integral_const_mul]
  congr 1
  funext e
  rw [affPt_add_uncol x₀ hy, hΨ, ch_add_colMat, neg_add, AddChar.map_add_eq_mul,
    Circle.coe_mul]
  ring

open Classical in

def volFree (ν : Measure k) (n n' : Type) [Fintype n] [Fintype n'] (c : ℕ) :
    Measure ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) := Measure.pi fun _ => ν

theorem opE_one_eq_volFree (ψ : AddChar k Circle) (ν : Measure k)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν 1 Ψ x₀ = ∫ e, Ψ (pt x₀ (col e)) * (ψ (-∑ i, col e i (Sum.inr i)) : ℂ) ∂(volFree ν n n' c) :=
  opE_one_eq ψ ν Ψ x₀

omit [MeasurableSpace k] [BorelSpace k] in

def perLat (ϖ : 𝒪[k]) (n' : Type) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) :
    AddSubgroup ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) where
  carrier := {e | ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) • col e i ∈ chainLat ϖ c L}
  add_mem' he he' i := by
    rw [col_add, Pi.add_apply, smul_add]
    exact add_mem (he i) (he' i)
  zero_mem' i := by
    have : col (0 : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) i = 0 := by
      ext r
      simp [col]
    rw [this, smul_zero]
    exact zero_mem _
  neg_mem' {e} he i := by
    rw [← neg_one_smul k e, col_smul, neg_one_smul, Pi.neg_apply, smul_neg]
    exact neg_mem (he i)

omit [MeasurableSpace k] [BorelSpace k] in
theorem mem_perLat {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)}
    {e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k} :
    e ∈ perLat ϖ n' c L ↔ ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) • col e i ∈ chainLat ϖ c L := Iff.rfl

end GlobalTheory.RootEx.UnfoldShape
