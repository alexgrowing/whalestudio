import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombExpand
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace TopNPoly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem orbitRep_orbitRep (z : (Σ k, ι k) → ℂ) : orbitRep (orbitRep z) = orbitRep z := by
  simp only [orbitRep, Quotient.out_eq]

theorem orbitRep_blocks {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, -, hzc⟩ := exists_eq_smul_orbitRep z
  intro k
  obtain ⟨i, hi⟩ := hz k
  refine ⟨i, fun h => hi ?_⟩
  rw [hzc]
  simp [torusSmul, h]

theorem hermOfFun_h_orbitRep {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h (orbitRep z) = F (orbitRep z) := by
  have hR := refNorm_pos a (orbitRep_blocks hz)
  simp only [hermOfFun]
  rw [orbitRep_orbitRep, Real.exp_log (div_pos hF hR), mul_div_cancel₀ _ hR.ne']

theorem hermOfFun_h_smul {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (hzc : z = torusSmul c (orbitRep z)) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h z = (∏ k, ‖c k‖ ^ a k) * F (orbitRep z) := by
  have h1 := hermOfFun_h_orbitRep (a := a) hz hF
  conv_lhs => rw [hzc]
  exact ((hermOfFun ι a F).smul c (orbitRep z) hc).trans (by rw [h1]; rfl)

theorem prod_norm_zpow_add {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a b : K → ℤ) (q : ℕ) :
    (∏ k, ‖c k‖ ^ ((q : ℤ) • a + ((1 : ℕ) : ℤ) • b) k) = (∏ k, ‖c k‖ ^ a k) ^ q * ∏ k, ‖c k‖ ^ b k := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
  rw [zpow_add₀ h0, show (q : ℤ) * a k = a k * q by ring, zpow_mul, zpow_natCast]

theorem smoothRep_smooth_of {P : Ideal (MRing ι)} {A Z : HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRep P A) := by
  classical
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact absurd ⟨Z, ha, hZ, hh⟩ h

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

omit [DecidableEq Ψ] in

theorem NbarQ_h_eq (hV : VertFactorPos.Statement) (X : ComponentSetting D O Lt) (B q : ℕ) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (X.NbarQ B 1 q t).h z = (muReg X.H X.S B t).h z ^ q * D.A'.h z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hz0 := hz.1
  have hw0 := orbitRep_blocks hz0
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hvf : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_pos fun p' hp' => hV II Ψ K ι Ω E D p' (Finset.mem_filter.1 hp').1 _ hwP
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz0 hG0
  have hM : (muReg X.H X.S B t).h z = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) *
      ((X.S.regLine t).h (orbitRep z) * ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) := by
    unfold muReg
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0 (by rw [hreg]; exact mul_pos hG0 hvf)
  have hN : (X.NbarQ B 1 q t).h z = (∏ k, ‖c k‖ ^ ((q : ℤ) • muTwDeg X.H B + ((1 : ℕ) : ℤ) • D.a') k) *
      ((X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) ^ q * D.A'.h (orbitRep z) ^ 1) := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0
      (mul_pos (mul_pos (pow_pos hG0 _) (pow_pos hvf _)) (pow_pos (D.A'.pos _ hw0) _))
  have hA : D.A'.h z = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h (orbitRep z) := by
    conv_lhs => rw [hzc]
    exact (D.A'.smul c (orbitRep z) hc).trans (by rw [D.A'_deg])
  rw [hN, hM, hA, hreg, prod_norm_zpow_add hc]
  ring

end TopNPoly

open TopNPoly in

theorem TopNPoly.proof (hIso : HilbertSamuel.IsomInvariance.Statement) (hV : VertFactorPos.Statement)
    (hS : MuRegSmooth.Statement) : TopNPoly.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII _
  have hP : IsArithVar (mCoordIdeal D.y) (D.n + 1) := D.arith
  have hA : IsSmoothHerm D.A' := D.A'_pos.1
  refine ⟨fun i t => if i = 0 then arLimFun X.H X.S B t else ((D.n + 1).choose i : ℝ) *
      II K ι (mCoordIdeal D.y) (D.n + 1)
        (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - i then muReg X.H X.S B t else D.A'),
    by funext t; simp, fun q hq => ?_⟩
  filter_upwards [hS II Ψ K ι Ω E D O Lt X B] with t ht
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set Z := HilbertSamuel.HermLine.zcomb (muReg X.H X.S B t) D.A' (q : ℤ) ((1 : ℕ) : ℤ) with hZdef
  have hZ : IsSmoothHerm Z := HilbertSamuel.ZCombLimit.isSmoothHerm_zcomb_int ht hA _ _
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z = (X.NbarQ B 1 q t).h z := by
    intro z hz
    rw [NbarQ_h_eq hV X B q t hz]
    show (muReg X.H X.S B t).h z ^ (q : ℤ) * D.A'.h z ^ ((1 : ℕ) : ℤ) = _
    simp
  have hdeg : Z.a = (X.NbarQ B 1 q t).a := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_a]
    show (q : ℤ) • (muReg X.H X.S B t).a + ((1 : ℕ) : ℤ) • D.A'.a = _
    rw [muReg, smoothRep_a, D.A'_deg]
    rfl
  have hN : IsSmoothHerm (X.NbarQ B 1 q t) := by
    unfold ComponentSetting.NbarQ
    refine smoothRep_smooth_of (Z := Z) ?_ hZ fun z hz => ?_
    · rw [hdeg]; unfold ComponentSetting.NbarQ; rw [smoothRep_a]
    · rw [hagree z hz]; unfold ComponentSetting.NbarQ; rw [smoothRep_h _ hz]
  have hne : (1 : MRing ι) ∉ mCoordIdeal D.y := fun h =>
    hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hiso : ∀ j : Fin (D.n + 1), HilbertSamuel.IsIsometricOn (mCoordIdeal D.y)
      ((fun _ => X.NbarQ B 1 q t) j) ((fun _ => Z) j) := fun _ =>
    ⟨1, 1, 0, 0, by simpa using isMultiHomog_C_zero (ι := ι) 1, by simpa using isMultiHomog_C_zero (ι := ι) 1,
      hne, hne, fun k => by simp [hdeg], rfl, fun z hz => by simp [hagree z hz]⟩
  have hI := hIso K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) (fun _ => Z) hP
    (fun _ => hN) (fun _ => hZ) hiso
  have hE := (HilbertSamuel.ZCombExpand.proof K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1)
    (muReg X.H X.S B t) D.A' q 1 hP ht hA).1
  show II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) / (q : ℝ) ^ (D.n + 1) = _
  rw [hI, hE, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ D.n + 1 := by simp at hi; omega
  have hpow : (q : ℝ) ^ (D.n + 1) = (q : ℝ) ^ (D.n + 1 - i) * (q : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  split_ifs with h0
  · subst h0
    have hall : (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - 0 then muReg X.H X.S B t else D.A') =
        fun _ => muReg X.H X.S B t := by
      funext j; simp [j.isLt]
    rw [hall]
    simp only [arLimFun, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.sub_zero, pow_zero]
    field_simp
  · rw [hpow, Nat.cast_one, one_pow, mul_one, one_div, inv_pow]
    field_simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
