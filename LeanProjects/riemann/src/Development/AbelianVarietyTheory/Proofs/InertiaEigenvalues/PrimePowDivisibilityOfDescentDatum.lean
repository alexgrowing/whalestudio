import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem l_pow_eq (n : ℕ) : ((l : K⟦X⟧)) ^ n =
    E K l e ^ n - (X : K⟦X⟧) ^ e * ∑ i ∈ Finset.range n, (l : K⟦X⟧) ^ i * E K l e ^ (n - 1 - i) := by
  have h := (Commute.all ((l : K⟦X⟧)) (E K l e)).geom_sum₂_mul n
  have hE : (l : K⟦X⟧) - E K l e = -((X : K⟦X⟧) ^ e) := by simp [E]
  rw [hE] at h
  linear_combination -h

theorem l_pow_smul (n : ℕ) (y : Vec K a ι) : (l : K) ^ n • y =
    E K l e ^ n • y - (X : K⟦X⟧) ^ e • ∑ i ∈ Finset.range n, ((l ^ i : ℕ)) • (E K l e ^ (n - 1 - i) • y : Vec K a ι) := by
  have h1 : (l : K) ^ n • y = ((l : K⟦X⟧)) ^ n • y := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h1, l_pow_eq (e := e), sub_smul, mul_smul, Finset.sum_smul]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

variable (D : BKDat O K l e a ι η H)

theorem E_pow_smul_mem_M (j : ℕ) {m : Vec K a ι} (hm : m ∈ D.M) : E K l e ^ j • m ∈ D.M := by
  have := D.M.smul_mem (EIn l e (A O K) ^ j) hm
  simpa [Subalgebra.smul_def] using this

theorem E_pow_smul_mem_EM (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η) : E K l e ^ j • y ∈ D.EM η := by
  rw [mem_divE] at hy ⊢
  rw [smul_comm]
  exact E_pow_smul_mem_M D j hy

theorem E_pow_smul_mem_Y (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.Y) : E K l e ^ j • y ∈ D.Y := by
  rw [BKDat.Y, Descent.mem_invOf] at hy ⊢
  exact ⟨E_pow_smul_mem_EM D j hy.1, fun g => by rw [Descent.act_E_pow_smul, hy.2 g]⟩

theorem cls_E_pow_smul_mem_Z (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η)
    (h : ∀ g, D.desc.actPol g (D.cls y) = D.cls y) : D.cls (E K l e ^ j • y) ∈ D.Z := by
  refine ⟨⟨_, E_pow_smul_mem_EM D j hy, rfl⟩, fun g => ?_⟩
  have h' := congrArg (D.mulPol ⟨_, pow_mem (E_mem l e (Rpi O K l e)) j⟩) (h g)
  rw [Descent.actPol_cls] at h'
  change D.desc.actPol g (D.cls (E K l e ^ j • y)) = D.cls (E K l e ^ j • y)
  rw [Descent.actPol_cls, Descent.act_E_pow_smul]
  exact h'

end GlobalTheory.NgalDivisible

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  (D : BKDat O K l e a ι η H)

theorem l_pow_smul_Z {w : D.Pol} (hw : w ∈ D.Z) : ∃ z ∈ D.Z, (l : K) ^ η • w = D.vPol z := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := D.desc.mem_Z.1 hw
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsZ : D.cls s ∈ D.Z := by
    rw [hs, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (cls_E_pow_smul_mem_Z D _ hy h)
  refine ⟨-D.cls s, neg_mem hsZ, ?_⟩
  have h0 : D.cls (E K l e ^ η • y) = 0 := D.cls_eq_zero_iff.2 (D.M_le_Man hy)
  rw [← map_smul, l_pow_smul (e := e) η y, ← hs, map_sub, h0, zero_sub, map_neg, PhiMod.vPol_cls]

theorem l_pow_smul_Y {y : Vec K a ι} (hy : y ∈ D.Y) : (l : K) ^ η • y ∈ D.Y' ⊔ D.Minv := by
  have hy' := hy
  rw [BKDat.Y, Descent.mem_invOf] at hy'
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsY : s ∈ D.Y := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (E_pow_smul_mem_Y D _ hy)
  have h1 : -((X : K⟦X⟧) ^ e • s) ∈ D.Y' :=
    D.desc.mem_Y'.2 ⟨-s, neg_mem hsY, smul_neg _ _⟩
  have h2 : E K l e ^ η • y ∈ D.Minv := by
    rw [BKDat.Minv, Descent.mem_invOf]
    exact ⟨hy'.1, fun g => by rw [Descent.act_E_pow_smul, hy'.2 g]⟩
  rw [l_pow_smul (e := e) η y, ← hs, sub_eq_neg_add]
  exact Submodule.add_mem_sup h1 h2

end GlobalTheory.NgalDivisible

theorem GlobalTheory.divisible_of_BKDat : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨fun _ hw => NgalDivisible.l_pow_smul_Z D hw, fun _ hy => NgalDivisible.l_pow_smul_Y D hy⟩
