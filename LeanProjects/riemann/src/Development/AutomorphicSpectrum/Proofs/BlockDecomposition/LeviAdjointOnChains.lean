import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChainAdj

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def ip (x z : Cq n V) : ℂ := ∑ A, ⟪x A, z A⟫_ℂ

theorem sgL_conj (i : Lt n) (A : Finset (Lt n)) : (starRingEnd ℂ) (sgL i A) = sgL i A := by
  simp [PositivityTheory.RgBcC.RealD.sgL]

theorem sgL_erase_self (i : Lt n) {A : Finset (Lt n)} (h : i ∈ A) : sgL i (A.erase i) = sgL i A := by
  rw [GlobalTheory.CompanionTheory.LvChain.sgL_erase i h, GlobalTheory.CompanionTheory.LvChain.twL_self, one_mul]

theorem ip_creL (i : Lt n) (x z : Cq n V) : ip (creL i x) z = ip x (annL i z) := by
  classical
  have hL : GlobalTheory.CompanionTheory.LvChainAdj.ip (PositivityTheory.RgBcC.RealD.creL i x) z =
      ∑ A ∈ Finset.univ.filter (fun A => i ∈ A),
        PositivityTheory.RgBcC.RealD.sgL i A * ⟪x (A.erase i), z A⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.creL_apply]
    split_ifs <;> simp [inner_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.sgL_conj] <;> ring
  have hR : GlobalTheory.CompanionTheory.LvChainAdj.ip x (PositivityTheory.RgBcC.RealD.annL i z) =
      ∑ B ∈ Finset.univ.filter (fun B => i ∉ B),
        PositivityTheory.RgBcC.RealD.sgL i B * ⟪x B, z (insert i B)⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.annL_apply]
    split_ifs <;> simp [inner_smul_right]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun A => A.erase i) (fun B => insert i B) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact Finset.insert_erase hA
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    exact Finset.erase_insert hB
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rw [GlobalTheory.CompanionTheory.LvChainAdj.sgL_erase_self i hA, Finset.insert_erase hA]

theorem ip_conj (x z : Cq n V) : (starRingEnd ℂ) (ip x z) = ip z x := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => inner_conj_symm (z A) (x A)

theorem ip_annL (i : Lt n) (x z : Cq n V) : ip (annL i x) z = ip x (creL i z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.ip_conj z (PositivityTheory.RgBcC.RealD.annL i x), ← GlobalTheory.CompanionTheory.LvChainAdj.ip_creL i z x,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_conj]

theorem ip_creL_annL (i k : Lt n) (x z : Cq n V) :
    ip ((creL k * annL i : Module.End ℂ (Cq n V)) x) z = ip x ((creL i * annL k : Module.End ℂ (Cq n V)) z) := by
  rw [Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_creL,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_annL]

theorem ip_add_left (x y z : Cq n V) : ip (x + y) z = ip x z + ip y z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_left]; rfl

theorem ip_add_right (x y z : Cq n V) : ip x (y + z) = ip x y + ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_right]; rfl

theorem ip_smul_left (c : ℂ) (x z : Cq n V) : ip (c • x) z = (starRingEnd ℂ) c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_left]; rfl

theorem ip_smul_right (c : ℂ) (x z : Cq n V) : ip x (c • z) = c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_right]; rfl

theorem ip_zero_left (z : Cq n V) : ip (0 : Cq n V) z = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_left]

theorem ip_zero_right (x : Cq n V) : ip x (0 : Cq n V) = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_right]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Cq n V) (z : Cq n V) :
    ip (∑ a ∈ s, f a) z = ∑ a ∈ s, ip (f a) z := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left, ih]

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Cq n V) (f : ι → Cq n V) :
    ip x (∑ a ∈ s, f a) = ∑ a ∈ s, ip x (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, ih]

theorem adCL_conj (p q : Fin n) (l k : Lt n) : (starRingEnd ℂ) (adCL false p q l k) = adCL false p q l k := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  split_ifs <;> simp

theorem adCL_swap (p q : Fin n) (l k : Lt n) : adCL false p q l k = adCL false q p k l := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  simp only [Bool.false_xor, Bool.false_bne, Prod.ext_iff]
  congr 1
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩⟩ rfl rfl
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩⟩ rfl rfl

theorem inUU_iff_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) : inUU lev l ↔ inUU lev k := by
  unfold PositivityTheory.RgBcC.RealD.adCL at hc
  unfold PositivityTheory.RgBcC.RealD.inUU
  split_ifs at hc with h1 h2 h2
  · exact absurd (sub_self _) hc
  · obtain ⟨hq, -, hk⟩ := h1
    simp [hk, h, hq]
  · obtain ⟨hp, -, hk⟩ := h2
    simp [hk, hp, h]
  · exact absurd (sub_self _) hc

theorem ip_term {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (l k : Lt n) (x z : Cq n V) :
    ip ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 : Module.End ℂ (Cq n V)) x) z =
      ip x ((if inUU lev k then adCL false q p k l • (creL l * annL k) else 0 : Module.End ℂ (Cq n V)) z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.adCL_swap p q l k]
  by_cases hc : PositivityTheory.RgBcC.RealD.adCL false p q l k = 0
  · simp only [hc, zero_smul, ite_self, LinearMap.zero_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left,
      GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · have hiff := GlobalTheory.CompanionTheory.LvChainAdj.inUU_iff_of_adCL h hc
    by_cases hl : PositivityTheory.RgBcC.RealD.inUU lev l
    · rw [if_pos hl, if_pos (hiff.mp hl), LinearMap.smul_apply, LinearMap.smul_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_right, GlobalTheory.CompanionTheory.LvChainAdj.adCL_conj,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_creL_annL]
    · rw [if_neg hl, if_neg (mt hiff.mpr hl), LinearMap.zero_apply, LinearMap.zero_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]

theorem ip_adLL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (x z : Cq n V) :
    ip (adLL lev false p q x) z = ip x (adLL lev false q p z) := by
  unfold PositivityTheory.RgBcC.RealD.adLL
  simp only [LinearMap.sum_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_right]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact GlobalTheory.CompanionTheory.LvChainAdj.ip_term h l k x z

theorem ip_liftL {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hU : ∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) (p q : Fin n) (x z : Cq n V) :
    ip (liftL n (kA E1 E2 p q) x) z = ip x (liftL n (kA E1 E2 q p) z) := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_congr rfl fun A _ => hU p q (x A) (z A)

theorem Lv_adjoint : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    (∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) → ∀ p q : Fin n, lev p = lev q → ∀ x z : Cq n V,
      ∑ A, ⟪Lv lev E1 E2 p q x A, z A⟫_ℂ = ∑ A, ⟪x A, Lv lev E1 E2 q p z A⟫_ℂ := by
  intro n lev V _ _ E1 E2 hU p q h x z
  show GlobalTheory.CompanionTheory.LvChainAdj.ip _ _ = GlobalTheory.CompanionTheory.LvChainAdj.ip _ _
  unfold GlobalTheory.CompanionTheory.LvChain.Lv
  rw [LinearMap.add_apply, LinearMap.add_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, GlobalTheory.CompanionTheory.LvChainAdj.ip_liftL hU,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_adLL h]

end GlobalTheory.CompanionTheory.LvChainAdj
