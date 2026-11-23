import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colMat_mem_ball {s : kˣ} {n : ℕ} {v : Fin n → k} (hv : ∀ a, v a ∈ GlobalTheory.SplitWeil.cball s)
    (a b : Fin (n + 1)) : colMat k n v a b ∈ GlobalTheory.SplitWeil.cball s := by
  have h0 : (0 : k) ∈ GlobalTheory.SplitWeil.cball s := by simp [GlobalTheory.SplitWeil.cball]
  by_cases hb : b = Fin.last n
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [GlobalTheory.BZMir.colMat] using h0
    | cast a => simpa [GlobalTheory.BZMir.colMat] using hv a
  · simpa [GlobalTheory.BZMir.colMat, hb] using h0

theorem unip_mem_congGL {s : kˣ} (hs : ValuativeRel.valuation k (s : k) ≤ 1) {n : ℕ} {v : Fin n → k}
    (hv : ∀ a, v a ∈ GlobalTheory.SplitWeil.cball s) :
    unip k n (Multiplicative.ofAdd v) ∈ congGL k s hs (n + 1) := by
  have h1 : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (1 + GlobalTheory.BZMir.colMat k n v) := by
    intro a b
    rw [Matrix.add_apply, add_sub_cancel_left]
    exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mem_ball hv a b
  have h2 : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (1 - GlobalTheory.BZMir.colMat k n v) := by
    intro a b
    rw [Matrix.sub_apply, sub_sub_cancel_left]
    exact GlobalTheory.SplitWeil.neg_mem_cball (GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mem_ball hv a b)
  exact And.intro h1 h2

theorem colMat_mul_apply {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [GlobalTheory.BZMir.colMat]
  · intro j _ hj
    simp [GlobalTheory.BZMir.colMat, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ball_of_unip_eq_mul {s : kˣ} (hs : ValuativeRel.valuation k (s : k) ≤ 1) {n : ℕ} {v : Fin n → k}
    {h κ : GL (Fin (n + 1)) k} (heq : unip k n (Multiplicative.ofAdd v) = h * κ)
    (hκ : κ ∈ congGL k s hs (n + 1)) (a : Fin n)
    (h0 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0)
    (h1 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1) :
    v a ∈ GlobalTheory.SplitWeil.cball s := by
  have hinv : κ⁻¹ = (GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v))⁻¹ * h := by
    rw [heq, _root_.mul_inv_rev, inv_mul_cancel_right]
  have hmat : ((κ⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (1 - GlobalTheory.BZMir.colMat k n v) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    rw [hinv, Units.val_mul]
    rfl
  have hc := (show _ ∧ GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((κ⁻¹ : GL (Fin (n + 1)) k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k) from hκ).2 (Fin.castSucc a) (Fin.last n)
  rw [hmat, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mul_apply, h0, h1,
    Matrix.one_apply_ne (Fin.castSucc_ne_last a)] at hc
  simp only [zero_sub, mul_one, sub_zero] at hc
  have hneg := GlobalTheory.SplitWeil.neg_mem_cball hc
  rwa [neg_neg] at hneg

theorem Mir_last_last {n : ℕ} (g : Mir k n) :
    ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (n + 1)) k)).1 g.2
  have hentry := congrFun hrow (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using hentry

theorem ePG_true_natAdd (i t : ℕ) (j : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, j⟩ = Fin.castSucc (Fin.natAdd (i + 1) j) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (ext; simp [GlobalTheory.BZMir.Leib.ePG])

theorem HPG_entry_zero {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (j : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k) : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) j)) (Fin.last ((i + 1) + (t + 1))) = 0 := by
  have hh' : (h : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈
      GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1)) := hh
  have hz := GlobalTheory.SmGL.mem_parab_iff.1 hh' true false j (Fin.last (i + 1)) (by decide)
  rwa [GlobalTheory.CompanionTheory.BZPhiPG.Onto.ePG_true_natAdd, GlobalTheory.BZMir.Leib.ePG_false_last] at hz

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem GlobalTheory.CompanionTheory.BZPhiPG.Onto.dEmb_mem_congM_and_ball : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (d : Fin (t + 1) → k),
  ((∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → dEmb k i t d ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1)) ∧
  ∀ (h : Mir k ((i + 1) + t + 1)), h ∈ HPG k (i + 1) (t + 1) → ∀ κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1),
    dEmb k i t d = h * κ → ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s := by
  intro k _ _ _ _ i t s hs d
  refine ⟨fun hd => ?_, fun h hh κ hκ he j => ?_⟩
  · have hv : ∀ a, Fin.append (0 : Fin (i + 1) → k) d a ∈ GlobalTheory.SplitWeil.cball s := by
      intro a
      refine Fin.addCases (fun a => ?_) (fun b => ?_) a
      · rw [Fin.append_left]
        simp [GlobalTheory.SplitWeil.cball]
      · rw [Fin.append_right]
        exact hd b
    first
      | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.unip_mem_congGL hs hv
      | exact Subgroup.mem_comap.2 (GlobalTheory.CompanionTheory.BZPhiPG.Onto.unip_mem_congGL hs hv)
  · have he' : GlobalTheory.BZMir.unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) d)) =
        (h : GL (Fin ((i + 1) + (t + 1) + 1)) k) * (κ : GL (Fin ((i + 1) + (t + 1) + 1)) k) :=
      congrArg Subtype.val he
    have hmem := GlobalTheory.CompanionTheory.BZPhiPG.Onto.ball_of_unip_eq_mul hs he' hκ (Fin.natAdd (i + 1) j)
      (GlobalTheory.CompanionTheory.BZPhiPG.Onto.HPG_entry_zero h hh j)
      (GlobalTheory.CompanionTheory.BZPhiPG.Onto.Mir_last_last h)
    rwa [Fin.append_right] at hmem

end
