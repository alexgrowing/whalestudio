import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProj
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open ValuativeRel Topology GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem uM_levi_mul_uM_levi (n : ℕ) (y y' : Fin n → k) (b b' : GL (Fin n) k) :
    uM k n y * levi k n b * (uM k n y' * levi k n b') =
      uM k n (y + (b : Matrix (Fin n) (Fin n) k).mulVec y') * levi k n (b * b') := by
  rw [mul_assoc, ← mul_assoc (GlobalTheory.BZMir.levi k n b), GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add, map_mul]
  simp only [mul_assoc]

theorem mirProj_levi_eq (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi n g

theorem mirProj_uM (n : ℕ) (y : Fin n → k) : mirabolicProjection k n (uM k n y) = 1 :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_uv n y

theorem uM_injective (n : ℕ) : Function.Injective (uM k n) := by
  intro y y' h
  funext a
  have entry : ∀ z : Fin n → k, ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n z : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = z a := by
    intro z
    change (1 + GlobalTheory.BZMir.colMat k n z) (Fin.castSucc a) (Fin.last n) = z a
    simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  rw [← entry y, ← entry y', h]

theorem uM_levi_inj (n : ℕ) {y y' : Fin n → k} {g g' : GL (Fin n) k}
    (h : uM k n y * levi k n g = uM k n y' * levi k n g') : y = y' ∧ g = g' := by
  have hg : g = g' := by
    have hp := congrArg (GlobalTheory.BZMir.mirabolicProjection k n) h
    simpa only [map_mul, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_uM, one_mul] using hp
  subst hg
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_injective n (mul_right_cancel h), rfl⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def latt (n : ℕ) (c : kˣ) : AddSubgroup (Fin n → k) where
  carrier := {y | ∀ j, y j ∈ cball c}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' j := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_latt {n : ℕ} {c : kˣ} {y : Fin n → k} : y ∈ latt n c ↔ ∀ j, y j ∈ cball c :=
  Iff.rfl

theorem latt_eq_pi (n : ℕ) (c : kˣ) : (latt n c : Set (Fin n → k)) = Set.univ.pi fun _ => cball c := by
  ext y
  simp only [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt, Set.mem_univ_pi]

theorem isOpen_latt (n : ℕ) (c : kˣ) : IsOpen (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_cball c

theorem isCompact_latt (n : ℕ) (c : kˣ) : IsCompact (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball c

theorem isClosed_latt (n : ℕ) (c : kˣ) : IsClosed (latt n c : Set (Fin n → k)) :=
  AddSubgroup.isClosed_of_isOpen _ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c)

theorem exists_latt_subset {n : ℕ} {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ c : kˣ, (latt n c : Set (Fin n → k)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hmem : (⋂ j, t j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 fun j => by simpa using ht j
  obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_cball_subset hmem
  refine ⟨c, fun y hy => hsub (Set.mem_pi.2 fun j _ => ?_)⟩
  exact Set.mem_iInter.1 (hc (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt.1 hy j)) j

theorem mulVec_mem_latt {n : ℕ} {c : kˣ} {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) {y : Fin n → k}
    (hy : y ∈ latt n c) : (κ : Matrix (Fin n) (Fin n) k).mulVec y ∈ latt n c := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt] at hy ⊢
  have hint := ((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1
  intro j
  change valuation k ((κ : Matrix (Fin n) (Fin n) k).mulVec y j) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro i _
  rw [map_mul]
  calc valuation k ((κ : Matrix (Fin n) (Fin n) k) j i) * valuation k (y i)
      ≤ 1 * valuation k (c : k) :=
        mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hint j i)) (hy i)
    _ = valuation k (c : k) := one_mul _

def Bgrp (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) : Subgroup (Mir k n) where
  carrier := {p | ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b}
  mul_mem' := by
    rintro _ _ ⟨y, hy, b, hb, rfl⟩ ⟨y', hy', b', hb', rfl⟩
    exact ⟨_, add_mem hy (mulVec_mem_latt (h hb) hy'), _, mul_mem hb hb', uM_levi_mul_uM_levi n y y' b b'⟩
  one_mem' := ⟨0, zero_mem _, 1, one_mem _, by rw [uM_zero, map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨y, hy, b, hb, rfl⟩
    refine ⟨_, mulVec_mem_latt (h (inv_mem hb)) (neg_mem hy), b⁻¹, inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev, ← map_inv, GlobalTheory.CompanionTheory.BZPsiPG.Cont.uM_inv, levi_mul_uM]

theorem mem_Bgrp {n : ℕ} {c : kˣ} {K₁ : Subgroup (GL (Fin n) k)} {h : K₁ ≤ KO k (Fin n)} {p : Mir k n} :
    p ∈ Bgrp n c K₁ h ↔ ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b :=
  Iff.rfl

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
