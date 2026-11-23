import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.BigTop.Fun
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem rankGapBound_alt : _root_.GlobalTheory.BigTop.Fun.RankGapBound' := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps heps heps1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH hF _ => ?_⟩⟩⟩
  intro _
  refine ⟨1, fun C hC => ?_⟩
  obtain ⟨-, heP, hcTO, -, -, -, -, -, hfix⟩ := hF.1
  have hW : PageWin Fm := hF.2.1
  obtain ⟨x2, hx21, hx2⟩ := mul_pow_le_exp_rpow heps (6 * (⌈|Fm.Ct|⌉₊ + 1)) 25
  refine ⟨max (max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps))) (max (max x2 20480) ((2 * C) ^ 2)),
    fun x hx hx0 i p _ d _ => ?_⟩
  have hxa : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have hx8 : (8 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have hxb : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx0
  have hxc : 20480 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx0
  have hxC : (2 * C) ^ 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  have hx1 : 1 < x := by linarith
  have hx0' : (0 : ℝ) < x := by linarith
  have h8 : (8 : ℝ) ≤ x ^ (8 * eps) := by
    have e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]
    have e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (by positivity) hx8 heps.le
    have e3 : x ^ eps ≤ x ^ (8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, ⟨-, hk⟩⟩ := hW x hx i
  have hδ : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      (by linarith [(Fm.L x i).sc.eps_pos])
  have hδ0 : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ) := by
    have hs := Real.sq_sqrt (mul_nonneg hx0'.le hδ0)
    have hs0 := Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)
    have hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by positivity
    have hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x := by nlinarith
    have hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2 := by nlinarith
    have hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps) := by
      rw [Real.rpow_add hx0', Real.rpow_two]
    have hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by
      unfold Ranks.f
      push_cast
      ring
    rw [hf]
    have hx2' : 0 ≤ x ^ 2 := by positivity
    nlinarith
  have hH1 : leafHypothesesConst d.O := ⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4,
    (Fm.D x i).R.f_le_k⟩
  have hH7 : LatticeConstantBound d.O p.Z.b := by
    show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b
    exact (Lc_le_of_cloud_le d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le
      (fun τ j => cloud_mem_Icc_Sc (Fm.L x i) τ j)).trans (Sc_le_scale_b (Fm.params x hx i))
  have hb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [Fm.L_x x i hx, Fm.L_eps x i]
  have hT : (Fm.parT x hx i).TO ≤ (Fm.D x i).R.t := by
    have a1 := (Fm.parT x hx i).split
    have a2 := (Fm.parT x hx i).nP_eq
    have a3 := (Fm.parT x hx i).nW_lo.1
    have hf : 1 ≤ (Fm.D x i).R.f := by
      have : 0 < (Fm.D x i).R.ord := (Fm.D x i).R.ord_pos
      unfold Ranks.f Ranks.n; omega
    have hr : 1 ≤ (Fm.D x i).R.r := by
      have := (Fm.D x i).R.m_add_three_le_k
      unfold Ranks.r; omega
    have a4 : 1 ≤ (Fm.parT x hx i).nWn :=
      le_trans (Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)) a3
    have a5 : (Fm.parT x hx i).TO * 1 ≤ (Fm.parT x hx i).TO * (Fm.parT x hx i).nWn := Nat.mul_le_mul_left _ a4
    have a6 : 1 * (Fm.D x i).R.r ≤ 8 * (Fm.D x i).R.f * (Fm.D x i).R.r := Nat.mul_le_mul_right _ (by omega)
    omega
  have hto : x ^ 377 ≤ ((Fm.D x i).R.t : ℝ) := by
    have e1 : Fm.cTO = ((377 : ℕ) : ℝ) := by rw [hcTO, heP]; norm_num
    have e2 := (hfix x hx i).2.2.2.2.2.2.2
    have e3 : x ^ Fm.cTO ≤ ((Fm.parT x hx i).TO : ℝ) := by rw [e2]; exact Nat.le_ceil _
    rw [e1, Real.rpow_natCast] at e3
    exact e3.trans (by exact_mod_cast hT)
  have htc : ((Fm.D x i).R.t : ℝ) ≤ x ^ (⌈|Fm.Ct|⌉₊ + 1) := by
    have e1 := (Fm.L x i).t_win.2
    rw [Fm.Ct_eq x i, Fm.L_x x i hx] at e1
    refine e1.trans ?_
    have e2 : x ^ Fm.Ct ≤ x ^ (((⌈|Fm.Ct|⌉₊ + 1 : ℕ)) : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
      push_cast
      linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
    rwa [Real.rpow_natCast] at e2
  have hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := by
    have := (Fm.D x i).R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hkt : (Fm.D x i).R.k + (Fm.D x i).R.m + 4 ≤ (Fm.D x i).R.t := by
    have := (Fm.D x i).R.rank_add_five_le
    have := (Fm.D x i).R.m_add_three_le_k
    omega
  have hB := hx2 x hxb
  obtain ⟨l1, l2⟩ := design_lines_of_ranks x eps (Real.exp (x ^ eps)) (⌈|Fm.Ct|⌉₊ + 1) (Fm.D x i).R.k (Fm.D x i).R.m
    (Fm.D x i).R.f (Fm.D x i).R.t hxc heps1 (Fm.D x i).R.two_le_m hmf (Fm.D x i).R.f_le_k hkt htc hto hk hB
  have hL : 2 * Real.log (2 * C) ≤ Real.log p.Z.b := by
    rw [hb, Real.log_exp]
    have e1 : x ≤ x ^ (6 * (⌈|Fm.Ct|⌉₊ + 1)) := le_self_pow₀ hx1.le (by omega)
    have e2 : x ≤ Real.exp (x ^ eps) := by
      have : 0 ≤ x ^ (6 * (⌈|Fm.Ct|⌉₊ + 1)) := by positivity
      linarith
    have e3 : Real.log x ≤ x ^ eps := by
      rw [Real.log_le_iff_le_exp hx0']; exact e2
    have e4 : 2 * Real.log (2 * C) = Real.log ((2 * C) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have e5 : Real.log ((2 * C) ^ 2) ≤ Real.log x := Real.log_le_log (by positivity) hxC
    linarith
  refine GlobalTheory.SizeLeafCheck.tree_leaf_parameter_arithmetic_of_bounds d.O C p.Z.b hC hH1 hH7 ?_ ?_ hL
  · rw [hb]
    exact l1
  · exact l2
end GlobalTheory.BigTop.Fun
end
end
