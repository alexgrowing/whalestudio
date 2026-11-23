import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem d_hsNormSq_eq (A : V →L[ℂ] W) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem d_hsNormSq_nonneg (A : V →L[ℂ] W) : 0 ≤ hsNormSq A := by
  rw [d_hsNormSq_eq]; positivity

theorem d_norm_hsInner_le (A B : V →L[ℂ] W) :
    ‖hsInner A B‖ ≤ Real.sqrt (hsNormSq A) * Real.sqrt (hsNormSq B) := by
  rw [d_hsNormSq_eq, d_hsNormSq_eq]
  unfold hsInner
  calc ‖∑ i, ⟪B (stdOrthonormalBasis ℂ V i), A (stdOrthonormalBasis ℂ V i)⟫_ℂ‖
      ≤ ∑ i, ‖⟪B (stdOrthonormalBasis ℂ V i), A (stdOrthonormalBasis ℂ V i)⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ * ‖B (stdOrthonormalBasis ℂ V i)‖ :=
        Finset.sum_le_sum fun i _ => by rw [mul_comm]; exact norm_inner_le_norm _ _
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem d_sum_norm_sq_basis [FiniteDimensional ℂ W] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (c : OrthonormalBasis κ ℂ W) (A : V →L[ℂ] W) :
    haveI := FiniteDimensional.complete ℂ V
    haveI := FiniteDimensional.complete ℂ W
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ j, ‖(ContinuousLinearMap.adjoint A) (c j)‖ ^ 2 := by
  have := FiniteDimensional.complete ℂ V
  have := FiniteDimensional.complete ℂ W
  calc ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ∑ j, ‖⟪c j, A (b i)⟫_ℂ‖ ^ 2 := by
        simp_rw [c.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪c j, A (b i)⟫_ℂ‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, ‖⟪(ContinuousLinearMap.adjoint A) (c j), b i⟫_ℂ‖ ^ 2 := by
        simp_rw [ContinuousLinearMap.adjoint_inner_left]
    _ = _ := by simp_rw [b.sum_sq_norm_inner_left]

theorem d_hsNormSq_comp_isom [FiniteDimensional ℂ W] (A : V →L[ℂ] W) (U : V →L[ℂ] V)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : hsNormSq (A.comp U) = hsNormSq A := by
  let li : V →ₗᵢ[ℂ] V := ⟨U.toLinearMap, hU⟩
  let e : V ≃ₗᵢ[ℂ] V := li.toLinearIsometryEquiv rfl
  have he : ∀ x, e x = U x := fun x => rfl
  rw [d_hsNormSq_eq, d_hsNormSq_eq]
  have h1 := d_sum_norm_sq_basis ((stdOrthonormalBasis ℂ V).map e) (stdOrthonormalBasis ℂ W) A
  have h2 := d_sum_norm_sq_basis (stdOrthonormalBasis ℂ V) (stdOrthonormalBasis ℂ W) A
  rw [h2, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [he]

end HS

section Pair

variable {D : D7}

def aT (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : ℝ := Real.sqrt (hsNormSq (X.Jt t))

theorem aT_nonneg (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : 0 ≤ aT X t := Real.sqrt_nonneg _

def wP (X : TermTie D) {u u' : D.what₂.Word} (p : D.s.Pair u u') : ℝ :=
  X.wRow p * (aT X (D.s.pfst p) * aT X (D.s.psnd p))

theorem placeWeight_nonneg (X : TermTie D) {u u' : D.what₂.Word} (p : D.s.Pair u u') : 0 ≤ wP X p :=
  mul_nonneg (X.wRow_pos p).le (mul_nonneg (aT_nonneg _ _) (aT_nonneg _ _))

theorem norm_pval_le (X : TermTie D) {u u' : D.what₂.Word} (p : D.s.Pair u u') : ‖D.s.pval p‖ ≤ wP X p := by
  rw [X.pval_eq p, norm_mul, norm_mul, X.chi_norm p, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (X.wRow_pos p)]
  unfold wP aT
  refine mul_le_mul_of_nonneg_left ?_ (X.wRow_pos p).le
  have h := d_norm_hsInner_le ((X.Jt (D.s.pfst p)).comp (X.piB p)) (X.Jt (D.s.psnd p))
  rwa [d_hsNormSq_comp_isom _ _ (X.piB_unit p)] at h

theorem gaG_nonneg (D : D7) : 0 ≤ gaG D := by
  unfold gaG
  refine finprod_nonneg fun p => finprod_nonneg fun _ => Finset.prod_nonneg fun i _ => ?_
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm p.asIdeal : ℝ) := by
    have : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  linarith [one_le_pow₀ h1 (n := i)]

end Pair

section Rows

open Classical

variable {D : D7} {large₂ : SizeData₂ D} (X : TermTie D) {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def RowBound (Q : D.s.Pair u u' → Prop) (B : ℝ) : Prop :=
  ∀ S : Finset (D.s.Pair u u'), (∀ p ∈ S, Q p) →
    ∑ p ∈ S, wP X p ≤ massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u * B

theorem gaG_sum_le (hF : UnitaryVolumeMass.FormAt D u) {Q : D.s.Pair u u' → Prop} {B : ℝ} (h : RowBound X Y Q B)
    (S : Finset (D.s.Pair u u')) (hS : ∀ p ∈ S, Q p) :
    gaG D * ∑ p ∈ S, ‖D.s.pval p‖ ≤ (D.duS u : ℝ) * B := by
  have h1 : ∑ p ∈ S, ‖D.s.pval p‖ ≤ ∑ p ∈ S, wP X p := Finset.sum_le_sum fun p _ => norm_pval_le X p
  have h2 := hF Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero Y.what₂ Y.isRows
  calc gaG D * ∑ p ∈ S, ‖D.s.pval p‖ ≤ gaG D * (massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u * B) :=
        mul_le_mul_of_nonneg_left (h1.trans (h S hS)) (gaG_nonneg D)
    _ = (D.duS u : ℝ) * B := by rw [← h2]; ring

def ndP (p : D.s.Pair u u') : Prop :=
  BNondeg (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p)

def clsND (s : ℕ) (p : D.s.Pair u u') : Prop :=
  D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧ D.s.s0 p = s ∧ ndP X p

def clsDeg (s : ℕ) (p : D.s.Pair u u') : Prop :=
  D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧ D.s.s0 p = s ∧ ¬ ndP X p

def clsOne (p : D.s.Pair u u') : Prop :=
  D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧
    D.s.generic (D.s.pfst p) ∧ D.s.generic (D.s.psnd p) ∧ D.s.s0 p = 1 ∧ ¬ D.s.scalarPair p

theorem pair_index_le_rank (X : TermTie D) (p : D.s.Pair u u') : D.s.s0 p ≤ D.R.k := by
  rw [X.s0_eq p]; unfold Lat.s0; exact Nat.sub_le _ _

theorem rowBound_loop {Bn Bd : ℕ → ℝ} {B1 : ℝ}
    (hn : ∀ s, 2 ≤ s → s ≤ D.R.k → RowBound X Y (clsND X s) (Bn s))
    (hd : ∀ s, 2 ≤ s → s ≤ D.R.k → RowBound X Y (clsDeg X s) (Bd s))
    (h1 : RowBound X Y clsOne B1) :
    RowBound X Y (loopP D.s) ((∑ s ∈ Finset.Icc 2 D.R.k, Bn s) + (∑ s ∈ Finset.Icc 2 D.R.k, Bd s) + B1) := by
  intro S hS
  set M := massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u with hM
  have key : ∀ p ∈ S, wP X p ≤
      (∑ s ∈ Finset.Icc 2 D.R.k, if clsND X s p then wP X p else 0) +
      (∑ s ∈ Finset.Icc 2 D.R.k, if clsDeg X s p then wP X p else 0) +
      (if clsOne p then wP X p else 0) := by
    intro p hp
    have h0 := placeWeight_nonneg X p
    have n1 : 0 ≤ ∑ s ∈ Finset.Icc 2 D.R.k, (if clsND X s p then wP X p else 0) :=
      Finset.sum_nonneg fun s _ => by split_ifs <;> simp [h0]
    have n2 : 0 ≤ ∑ s ∈ Finset.Icc 2 D.R.k, (if clsDeg X s p then wP X p else 0) :=
      Finset.sum_nonneg fun s _ => by split_ifs <;> simp [h0]
    have n3 : 0 ≤ (if clsOne p then wP X p else 0) := by split_ifs <;> simp [h0]
    obtain ⟨g1, g2, hc⟩ := hS p hp
    rcases hc with hc | ⟨a, b, c, d⟩
    · have hmem : D.s.s0 p ∈ Finset.Icc 2 D.R.k := Finset.mem_Icc.2 ⟨hc, pair_index_le_rank X p⟩
      by_cases hnd : ndP X p
      · have := Finset.single_le_sum (f := fun s => if clsND X s p then wP X p else 0)
          (fun s _ => by split_ifs <;> simp [h0]) hmem
        have hc1 : clsND X (D.s.s0 p) p := ⟨g1, g2, rfl, hnd⟩
        rw [if_pos hc1] at this
        linarith
      · have := Finset.single_le_sum (f := fun s => if clsDeg X s p then wP X p else 0)
          (fun s _ => by split_ifs <;> simp [h0]) hmem
        have hc1 : clsDeg X (D.s.s0 p) p := ⟨g1, g2, rfl, hnd⟩
        rw [if_pos hc1] at this
        linarith
    · have hc1 : clsOne p := ⟨g1, g2, a, b, c, d⟩
      rw [if_pos hc1]
      linarith
  calc ∑ p ∈ S, wP X p ≤ ∑ p ∈ S, ((∑ s ∈ Finset.Icc 2 D.R.k, if clsND X s p then wP X p else 0) +
      (∑ s ∈ Finset.Icc 2 D.R.k, if clsDeg X s p then wP X p else 0) +
      (if clsOne p then wP X p else 0)) := Finset.sum_le_sum key
    _ = (∑ s ∈ Finset.Icc 2 D.R.k, ∑ p ∈ S.filter (clsND X s), wP X p) +
        (∑ s ∈ Finset.Icc 2 D.R.k, ∑ p ∈ S.filter (clsDeg X s), wP X p) +
        ∑ p ∈ S.filter clsOne, wP X p := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm,
        Finset.sum_comm (s := S) (t := Finset.Icc 2 D.R.k)]
      simp only [Finset.sum_filter]
    _ ≤ (∑ s ∈ Finset.Icc 2 D.R.k, M * Bn s) + (∑ s ∈ Finset.Icc 2 D.R.k, M * Bd s) + M * B1 := by
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact Finset.sum_le_sum fun s hs => hn s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2 _
          (fun p hp => (Finset.mem_filter.1 hp).2)
      · exact Finset.sum_le_sum fun s hs => hd s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2 _
          (fun p hp => (Finset.mem_filter.1 hp).2)
      · exact h1 _ (fun p hp => (Finset.mem_filter.1 hp).2)
    _ = M * ((∑ s ∈ Finset.Icc 2 D.R.k, Bn s) + (∑ s ∈ Finset.Icc 2 D.R.k, Bd s) + B1) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]; ring

end Rows

section Num

variable (D : D7) (large₂ : SizeData₂ D)

theorem d_one_le_L : 1 ≤ large₂.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le

theorem d_log_b : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Scale.b; exact Real.log_exp _

theorem d_two_le_b : 2 ≤ large₂.sc.b := by
  have h1 := d_one_le_L D large₂
  have h2 := Real.add_one_le_exp large₂.sc.L
  unfold Scale.b
  linarith

theorem d_m_eq : D.R.m = 2 * D.R.rS + 2 := by
  have h := dimS_eq D.R
  have h2 := D.R.two_le_m
  unfold Ranks.r at h
  omega

theorem d_Dstar_pos : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos

theorem d_GamP_eq (u : D.what₂.Word) : (D.mem u).A.GamP = GamS D large₂ := by
  unfold GamS
  rw [← large₂.Gam_eq u, Real.exp_log (lt_trans one_pos (D.mem u).A.one_lt_gammaP)]

theorem parameters_of_hypotheses {C' Cl Cg cb Cu cT CT C0 C K₀ : ℝ} (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (u : D.what₂.Word) (hm : 4 ≤ D.R.m) (hCl : 1 ≤ Cl) (hCT : CT ≤ C) (hG : large₂.CGam ≤ C)
    (hK : K₀ * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k) :
    LatticeSumBounds.Params C K₀ D.R.k D.R.m D.R.f large₂.sc.b (gg D) D.host.v (NT D u) (GamS D large₂) := by
  obtain ⟨_, _, _, h4, _, _, _, _, _, _, h11, h12, _, h14, _, _, _, _, h19, _, _, _, h23, _, _⟩ := h.1
  have h4' : D.R.f ≤ D.R.k := h4
  have h11' : Real.log D.host.rdE ≤ large₂.sc.L / Cl := h11
  have h12' : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := h12
  have h14' : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 1 : ℝ) := h14
  have h19' : 1 ≤ D.host.v := h19
  have h23' : Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (h23 u).2
  have hL := d_one_le_L D large₂
  have hb := d_two_le_b D large₂
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (1 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hkb8 : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := one_le_pow₀ hkb
  have hT1 : (1 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  refine ⟨hm, ?_, h4', hb, ?_, ?_, h19', ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ranks.f Ranks.n; exact D.R.m_le_f
  · unfold gg; nlinarith
  · rw [d_log_b]; exact hK
  · have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
    have hrd0 : 0 < D.host.rdE := by rw [hrd]; linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := h11'.trans (div_le_self (by linarith) hCl)
    have h2 : D.host.rdE ≤ large₂.sc.b := by
      unfold Scale.b
      rw [← Real.exp_log hrd0]; exact Real.exp_le_exp.2 h1
    linarith
  · unfold NT; exact one_le_pow₀ hT1
  · unfold NT
    have h1 : ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ)) :=
      h23'.trans (Real.rpow_le_rpow_of_exponent_le hb1 (by gcongr))
    calc ((D.mem u).A.T : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ))) ^ D.R.f := by gcongr
      _ = large₂.sc.b ^ (C * (D.R.m : ℝ) * D.R.f) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  · unfold GamS
    have := large₂.CGam_pos
    exact Real.one_le_exp (by positivity)
  · unfold GamS
    rw [d_log_b]
    exact Real.exp_le_exp.2 (by gcongr)

def XiB (u : D.what₂.Word) (C : ℝ) (s : ℕ) : ℝ :=
  XiS D u (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ))) C s

theorem d_mass_nonneg {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : 0 ≤ Formalism.HermitianLatticesTheory.mass h L := by
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs
  · exact Finset.sum_nonneg fun M _ => by positivity
  · exact le_refl _

theorem xiHyp_of_stX {u u' : D.what₂.Word} {C' Cl Cg cb Cu cT CT C0 A CX cX C : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hX : UnitaryVolumeMass.stX D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CX cX)
    (hC : |CX| * max 1 |cX| ≤ C) (hC1 : 1 ≤ C) :
    LatticeSumBounds.XiHyp C D.R.k D.R.m D.R.f large₂.sc.b D.host.v (NT D u) (XiB D large₂ u C) := by
  have hb := d_two_le_b D large₂
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hv : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkv : 0 < (D.R.k : ℝ) * D.host.v := by positivity
  have hCX : 0 ≤ |CX| := abs_nonneg _
  have hcX : 0 ≤ |cX| := abs_nonneg _
  have hCXC : |CX| ≤ C := le_trans (le_mul_of_one_le_right hCX (le_max_left _ _)) hC
  have ev1 : Even (D.R.k * D.R.f) := D.R.k_even.mul_right _
  constructor
  · intro s hs2 hsk
    have hsk' : s ≤ D.R.k - 2 := by omega
    have e1 : ∀ HH Cc : ℝ, XiS D u HH Cc s = massS D s * massS D (D.R.k - s) / massS D D.R.k := by
      intro HH Cc
      unfold XiS Xi
      rw [if_pos ⟨hs2, hsk'⟩]
    refine ⟨?_, ?_⟩
    · unfold XiB; rw [e1]
      unfold massS massU
      exact div_nonneg (mul_nonneg (d_mass_nonneg _ _) (d_mass_nonneg _ _)) (d_mass_nonneg _ _)
    · have h := (hX hH).2 s hs2 hsk' 0
      rw [e1] at h
      unfold XiB; rw [e1]
      have h2 : ((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) *
          (Hb large₂.sc.b CX D.R.m D.R.f ^ CX * CX ^ (s * D.R.k * D.R.f) *
            (cX / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f)) =
          Hb large₂.sc.b CX D.R.m D.R.f ^ CX * (CX ^ (s * D.R.k * D.R.f) * cX ^ (D.R.k * D.R.f)) := by
        rw [div_pow]; field_simp
      calc ((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * (massS D s * massS D (D.R.k - s) / massS D D.R.k)
          ≤ ((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) *
            (Hb large₂.sc.b CX D.R.m D.R.f ^ CX * CX ^ (s * D.R.k * D.R.f) *
              (cX / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f)) := by gcongr
        _ = Hb large₂.sc.b CX D.R.m D.R.f ^ CX * (CX ^ (s * D.R.k * D.R.f) * cX ^ (D.R.k * D.R.f)) := h2
        _ = Hb large₂.sc.b CX D.R.m D.R.f ^ CX * (|CX| ^ (s * D.R.k * D.R.f) * |cX| ^ (D.R.k * D.R.f)) := by
          rw [ev1.pow_abs, ((D.R.k_even.mul_left s).mul_right D.R.f).pow_abs]
        _ ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ C * C ^ (s * D.R.k * D.R.f) := by
          have a1 : Hb large₂.sc.b CX D.R.m D.R.f ^ CX ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ C := by
            unfold Hb LatticeSumBounds.bigH
            rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
            apply Real.rpow_le_rpow_of_exponent_le hb1
            have : CX * CX ≤ C * C := by
              rw [← abs_mul_abs_self CX]; nlinarith
            have hmf : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f := by positivity
            nlinarith
          have a2 : |CX| ^ (s * D.R.k * D.R.f) * |cX| ^ (D.R.k * D.R.f) ≤ C ^ (s * D.R.k * D.R.f) := by
            have m1 : (1 : ℝ) ≤ max 1 |cX| := le_max_left _ _
            have b1 : |cX| ^ (D.R.k * D.R.f) ≤ (max 1 |cX|) ^ (s * D.R.k * D.R.f) := by
              calc |cX| ^ (D.R.k * D.R.f) ≤ (max 1 |cX|) ^ (D.R.k * D.R.f) := by
                    gcongr; exact le_max_right _ _
                _ ≤ (max 1 |cX|) ^ (s * D.R.k * D.R.f) := by
                    apply pow_le_pow_right₀ m1
                    rw [mul_assoc]
                    exact Nat.le_mul_of_pos_left _ (by omega)
            calc |CX| ^ (s * D.R.k * D.R.f) * |cX| ^ (D.R.k * D.R.f)
                ≤ |CX| ^ (s * D.R.k * D.R.f) * (max 1 |cX|) ^ (s * D.R.k * D.R.f) := by gcongr
              _ = (|CX| * max 1 |cX|) ^ (s * D.R.k * D.R.f) := (mul_pow _ _ _).symm
              _ ≤ C ^ (s * D.R.k * D.R.f) := by
                  have : 0 ≤ |CX| * max 1 |cX| := by positivity
                  gcongr
          have a3 : 0 ≤ |CX| ^ (s * D.R.k * D.R.f) * |cX| ^ (D.R.k * D.R.f) := by positivity
          have a4 : 0 ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ C := by
            unfold LatticeSumBounds.bigH; positivity
          exact mul_le_mul a1 a2 a3 a4
  · intro s hs
    have hk5 := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hn : ¬ (2 ≤ s ∧ s ≤ D.R.k - 2) := by omega
    have hy : s = D.R.k - 1 ∨ s = D.R.k := by omega
    have e : XiB D large₂ u C s = (C * D.R.k) ^ (D.R.k * D.R.f) *
        (LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * (D.R.m : ℝ)) * NT D u) ^ (C * (D.R.k : ℝ)) := by
      unfold XiB XiS Xi
      rw [if_neg hn, if_pos hy]
      rfl
    rw [e]
    refine ⟨?_, le_refl _⟩
    have : 0 ≤ NT D u := by unfold NT; positivity
    have h2 : 0 ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * (D.R.m : ℝ)) := by unfold LatticeSumBounds.bigH; positivity
    positivity

end Num

section Main

def rDD (D : D7) (u' : D.what₂.Word) : ℝ := (D.duS u' : ℝ) / D.what₂.Dstar

def oneB (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : ℝ :=
  C ^ D.R.f * LatticeSumBounds.bigH C (2 * D.R.rS + 2) D.R.f large₂.sc.b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) * GamS D large₂ *
    Real.exp (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
    Real.sqrt ((C * (gg D)⁻¹ ^ (2 * D.R.rS + 1) * ((D.R.k : ℝ) ^ D.R.rS)⁻¹) ^ (D.R.k * D.R.f))

variable {D : D7} {large₂ : SizeData₂ D} (X : TermTie D) {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def RowsND (C : ℝ) : Prop :=
  ∀ s, 2 ≤ s → s ≤ D.R.k → RowBound X Y (clsND X s)
    (LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) * rDD D u')

def RowsDeg (C : ℝ) : Prop :=
  ∀ s, 2 ≤ s → s ≤ D.R.k → RowBound X Y (clsDeg X s)
    (LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C))

def RowsOne (C : ℝ) : Prop := RowBound X Y clsOne (oneB D large₂ C * rDD D u')

end Main

theorem row_bound_of_rows_hypotheses (C : ℝ) (hC : 1 ≤ C) : ∃ K₀ : ℝ, ∀ {D : D7} {large₂ : SizeData₂ D} (X : TermTie D) {u u' : D.what₂.Word}
    {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1) {C' Cl Cg cb Cu cT CT C0 A : ℝ},
    Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → 4 ≤ D.R.m → 1 ≤ Cl → CT ≤ C → large₂.CGam ≤ C →
    K₀ * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k →
    6 * Real.log (3 * C0) ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k →
    UnitaryVolumeMass.FormAt D u → LatticeSumBounds.XiHyp C D.R.k D.R.m D.R.f large₂.sc.b D.host.v (NT D u) (XiB D large₂ u C) →
    RowsND X Y C → RowsDeg X Y C → RowsOne X Y C → ∀ c : ℝ, c ≤ 1 / 3 → UnitaryVolumeMass.LoopPairSumBound D u u' c := by
  obtain ⟨K1, H1⟩ := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe C hC
  obtain ⟨K2, H2⟩ := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe C hC
  obtain ⟨K3, H3⟩ := Formalism.HermitianLatticeCounting.P.singleRowBound C hC
  refine ⟨max K1 (max K2 K3), ?_⟩
  intro D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A hH hm hCl hCT hG hK hx hF hXi hn hd h1 c hc S hS
  have hL := d_one_le_L D large₂
  have hmfL : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
  have hKi : ∀ K : ℝ, K ≤ max K1 (max K2 K3) → K * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
    intro K hKle
    refine le_trans ?_ hK
    have := mul_le_mul_of_nonneg_right hKle hmfL
    nlinarith
  have P1 := parameters_of_hypotheses D large₂ hH.1 u hm hCl hCT hG (hKi K1 (le_max_left _ _))
  have P2 := parameters_of_hypotheses D large₂ hH.1 u hm hCl hCT hG (hKi K2 (le_trans (le_max_left _ _) (le_max_right _ _)))
  have P3 := parameters_of_hypotheses D large₂ hH.1 u hm hCl hCT hG (hKi K3 (le_trans (le_max_right _ _) (le_max_right _ _)))
  have E1 := H1 _ _ _ _ _ _ _ _ _ P1 hXi
  have E2 := H2 _ _ _ _ _ _ _ _ _ P2 hXi
  have e := d_m_eq D
  rw [e] at P3
  have E3 := H3 _ _ _ _ _ _ _ _ P3
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hb := d_two_le_b D large₂
  have E1' := Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp D.R.k D.R.f large₂.sc.b (gg D) hk1 (by linarith) P1.2.2.2.2.1

  obtain ⟨_, _, _, _, _, _, _, _, _, h10, _⟩ := hH.1.2.1
  have hC0 : 1 ≤ C0 := hH.1.2.2
  have hD := d_Dstar_pos D
  have hw : (GamS D large₂ ^ 2)⁻¹ ≤ C0 * rDD D u' := by
    have h := (h10 u').1
    rw [d_GamP_eq D large₂ u'] at h
    have e2 : GamS D large₂ ^ (-2 : ℤ) = (GamS D large₂ ^ 2)⁻¹ := by
      rw [zpow_neg]; norm_cast
    rw [e2, div_le_iff₀ (by linarith)] at h
    unfold rDD
    rw [mul_div_assoc', le_div_iff₀ hD]
    linarith
  have hr : 0 ≤ rDD D u' := by unfold rDD; positivity
  have tot := gaG_sum_le X Y hF (rowBound_loop X Y hn hd h1) S hS
  rw [← Finset.sum_mul] at tot
  set x : ℝ := (D.R.k : ℝ) * D.R.f * Real.log D.R.k with hxdef
  have hx0 : 0 ≤ x := by
    have : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
    positivity
  have T := Formalism.HermitianLatticeCounting.P.expSumLe' C0 x hC0 hx
  have B : (∑ s ∈ Finset.Icc 2 D.R.k,
        LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C)) * rDD D u' +
      (∑ s ∈ Finset.Icc 2 D.R.k,
        LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C)) +
      oneB D large₂ C * rDD D u' ≤ Real.exp (-x / 3) * rDD D u' := by
    have a1 := mul_le_mul_of_nonneg_right (E1.trans E1') hr
    have a2 : (∑ s ∈ Finset.Icc 2 D.R.k,
        LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C)) ≤
        Real.exp (-x / 2) * (C0 * rDD D u') :=
      E2.trans (mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le)
    have a3 : oneB D large₂ C * rDD D u' ≤ Real.exp (-x) * rDD D u' := mul_le_mul_of_nonneg_right E3 hr
    have T' := mul_le_mul_of_nonneg_right T hr
    have p1 : 0 ≤ Real.exp (-4 * x) * rDD D u' := mul_nonneg (Real.exp_pos _).le hr
    have p3 : 0 ≤ Real.exp (-x) * rDD D u' := mul_nonneg (Real.exp_pos _).le hr
    nlinarith
  have hdu : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
  calc gaG D * ∑ p ∈ S, ‖D.s.pval p‖ ≤ (D.duS u : ℝ) * (Real.exp (-x / 3) * rDD D u') :=
        tot.trans (mul_le_mul_of_nonneg_left B hdu)
    _ ≤ (D.duS u : ℝ) * (Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) * rDD D u') := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hr) hdu
        have : c * x ≤ 1 / 3 * x := mul_le_mul_of_nonneg_right hc hx0
        rw [hxdef] at this ⊢
        nlinarith
    _ = _ := by unfold rDD; ring

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

def RowsF : Prop :=
  ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A →
      RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧
        RowsOne (X x hx i) (Y x hx i u u') C

theorem d_CkLow_pos : 0 < Fm.CkLow := by
  obtain ⟨x, -, hx1, -, ⟨i⟩⟩ := Fm.toFamCore.exists_pt 0
  have h := (Fm.params x hx1 i).CkLow_pos
  rwa [Fm.params_CkLow] at h

theorem ev_kLow (K : ℝ) : ∃ x0 : ℝ, Fm.x1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x,
    K * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L ≤ (Fm.D x i).R.k := by
  obtain ⟨x0, h0, H⟩ := ev_L Fm (K / Fm.CkLow)
  refine ⟨x0, h0, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le h0 hx
  have h := (Fm.params x hx1 i).k_low
  rw [Fm.params_CkLow] at h
  have hL : K ≤ Fm.CkLow * (Fm.L x i).sc.L := by
    have := H x hx i
    rwa [div_le_iff₀ (d_CkLow_pos Fm), mul_comm] at this
  have hL1 := d_one_le_L (Fm.D x i) (Fm.L x i)
  have e : (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps = (Fm.L x i).sc.L := rfl
  rw [e] at h
  have hp : 0 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by positivity
  have h2 := mul_le_mul_of_nonneg_right hL hp
  have e5 : ((Fm.D x i).R.m : ℝ) ^ LevelStarExponents.jG = ((Fm.D x i).R.m : ℝ) ^ 5 := rfl
  rw [e5] at h
  nlinarith

theorem family_conclusion_of_row_bounds (hCl : 1 ≤ sCl Fm)
    (h8 : ∀ Cg cb Cu cT CT C0 A : ℝ, VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A)
    (h16 : ∀ Cg cb Cu cT CT C0 A : ℝ, VanishingOnXAndXPlus.FamilySixteenthHypothesis Fm Cg cb Cu cT CT C0 A)
    (hR : RowsF Fm C1 X Y) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 3) : VanishingOnXAndXPlus.OrbitValuationBound Fm c := by
  refine ⟨hc0, fun Cg cb Cu cT CT C0 A => ?_⟩
  obtain ⟨x8, H8⟩ := h8 Cg cb Cu cT CT C0 A
  obtain ⟨CX, cX, x16, CyclotomicCharacterContinuous⟩ := h16 Cg cb Cu cT CT C0 A
  obtain ⟨C₀, HR⟩ := hR Cg cb Cu cT CT C0 A
  set C : ℝ := max (max C₀ 1) (max (max CT Fm.CGam) (|CX| * max 1 |cX|)) with hCdef
  have c1 : C₀ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have c2 : 1 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have c3 : CT ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have c4 : Fm.CGam ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have c5 : |CX| * max 1 |cX| ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨xR, HRr⟩ := HR C c1
  obtain ⟨K₀, HB⟩ := row_bound_of_rows_hypotheses C c2
  obtain ⟨xm, _, Hm⟩ := ev_m Fm 4
  obtain ⟨xk, _, Hk⟩ := ev_k Fm (max 3 (6 * Real.log (3 * C0)))
  obtain ⟨xl, _, Hl⟩ := ev_kLow Fm K₀
  refine ownEv_intro Fm (max (max x8 x16) (max (max xR xm) (max xk xl))) fun x hx hx1 i u u' => ?_
  have g8 : x8 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have g16 : x16 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have gR : xR ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have gm : xm ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have gk : xk ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have gl : xl ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  intro hH
  have hm4 : 4 ≤ (Fm.D x i).R.m := by exact_mod_cast Hm x gm i
  have hk := Hk x gk i
  have hk3 : (3 : ℝ) ≤ (Fm.D x i).R.k := le_trans (le_max_left _ _) hk
  have hlog : 1 ≤ Real.log ((Fm.D x i).R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have : 1 ≤ (Fm.D x i).R.f := by
      have h1 : (Fm.D x i).R.f = 2 * (Fm.D x i).R.ord := rfl
      have := (Fm.D x i).R.ord_pos
      omega
    exact_mod_cast this
  have hx6 : 6 * Real.log (3 * C0) ≤ ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.f * Real.log (Fm.D x i).R.k := by
    have h1 : 6 * Real.log (3 * C0) ≤ ((Fm.D x i).R.k : ℝ) := le_trans (le_max_right _ _) hk
    have h2 : ((Fm.D x i).R.k : ℝ) ≤ ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.f := le_mul_of_one_le_right (by linarith) hf1
    have h3 : ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.f ≤
        ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.f * Real.log (Fm.D x i).R.k :=
      le_mul_of_one_le_right (by positivity) hlog
    linarith
  obtain ⟨r1, r2, r3⟩ := HRr x gR i hx1 u u' hH
  exact HB (X x hx1 i) (Y x hx1 i u u') hH hm4 hCl c3 (by rw [Fm.CGam_eq]; exact c4) (Hl x gl i) hx6
    ((H8 x g8 i u u') hH) (xiHyp_of_stX _ _ hH (CyclotomicCharacterContinuous x g16 i u u') c5 c2) r1 r2 r3 c hc

theorem family_packet_of_row_bounds (hCl : 1 ≤ sCl Fm) (hR : RowsF Fm C1 X Y) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 3) :
    VanishingOnXAndXPlus.KudlaFamilyStatement Fm C1 X Y c := by
  intro hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hA'⟩ := hA
  exact family_conclusion_of_row_bounds Fm C1 X Y hCl
    (fun Cg cb Cu cT CT C0 A => (hA' Cg cb Cu cT CT C0 A).2.2.2.2.2.2.2.2.2.2.1)
    (fun Cg cb Cu cT CT C0 A => (hA' Cg cb Cu cT CT C0 A).2.2.2.2.2.2.2.2.2.2.2.2.2.1) hR hc0 hc

end Fam

section Dict

open Matrix

theorem d_frameExp_cast (r : ℕ) : ∀ l : ℕ, l ≤ r + 1 → (frameExp r l : ℝ) = ∑ a : Fin l, ((r : ℝ) - (a : ℕ))
  | 0, _ => by simp [frameExp]
  | l + 1, h => by
    have ih := d_frameExp_cast r l (by omega)
    have e : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1)) := by
      unfold frameExp
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [e, Fin.sum_univ_castSucc]
    push_cast
    rw [ih, Nat.cast_sub (by omega)]
    simp

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem d_minor_eq (t : D.s.Term u u') (τ : D.what₂.Tau) (l : ℕ) (h : l ≤ D.R.rS + 1) :
    ((Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (Y.γ t τ)).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (((∏ a : Fin l, rhoF D (Fin.castLE h a)) ^ 2 : ℝ) : ℂ) *
        embS D τ ((ZhatL (X.fl t) (X.fl' t)).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  set v : Fin l → ℂ := fun a => ((rhoF D (Fin.castLE h a) : ℝ) : ℂ) with hv
  have e : (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (Y.γ t τ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.of (fun i j => v j * (Matrix.of (fun i j => v i *
        ((embS D τ).mapMatrix ((ZhatL (X.fl t) (X.fl' t)).submatrix (Fin.castLE h) (Fin.castLE h))) i j)) i j) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Y.gram, hv]
    push_cast
    ring
  rw [e, Matrix.det_mul_row, Matrix.det_mul_column, ← RingHom.map_det]
  simp only [hv]
  push_cast
  ring

theorem d_prod_rho (hrd : 0 < D.host.rdE) (l : ℕ) (h : l ≤ D.R.rS + 1) :
    (∏ a : Fin l, rhoF D (Fin.castLE h a)) ^ 2 = D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) := by
  have e1 : ∏ a : Fin l, rhoF D (Fin.castLE h a) = D.host.rdE ^ (-(frameExp D.R.rS l : ℝ)) := by
    rw [d_frameExp_cast _ l h, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hrd]
    refine Finset.prod_congr rfl fun a _ => ?_
    unfold rhoF
    simp
  rw [e1, ← Real.rpow_natCast, ← Real.rpow_mul hrd.le]
  congr 1
  push_cast
  ring

theorem d_norm_Dmin (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) (l : ℕ) (h : l ≤ D.R.rS + 1) :
    ‖DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) l‖ = absDl D (ZhatL (X.fl t) (X.fl' t)) l τ := by
  unfold DminN absDl absReal leadMinorE Formalism.QuantumDeterminants.Dmin
  rw [dif_pos (by omega : l < D.R.rS + 2), dif_pos h]
  rw [d_minor_eq Y t τ l h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    d_prod_rho hrd l h, mul_comm]

theorem d_Gf_eq (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (Y.γ t τ) =
      Gz D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ := by
  have h1 := d_norm_Dmin Y hrd t τ (D.R.rS + 1) le_rfl
  have h2 := d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)
  unfold DminN at h1 h2
  rw [dif_pos (by omega)] at h1 h2
  obtain ⟨_, _, _, _, hz, hz', _⟩ := Y.goodW τ
  unfold Formalism.QuantumDeterminants.Gf Gz
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hz, hz', ← h1, ← h2]
  rfl

theorem d_nV_eq (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) :
    normalizedLocalScale D u * Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ^ D.R.k =
      nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ := by
  rw [d_Gf_eq Y hrd t τ]
  unfold normalizedLocalScale nV
  rw [← mul_pow]
  congr 1
  have e : gg D = (gS D : ℝ) := by unfold gg gS; push_cast; ring
  have e2 : Tr D u = ((Tu D u : ℕ) : ℝ) := rfl
  rw [e, e2]
  ring

end Dict

section Term

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem d_rdE_pos {C' Cl Cg cb Cu cT CT C0 : ℝ} (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : 0 < D.host.rdE := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.1
  have h19' : 1 ≤ D.host.v := h19
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  rw [hrd]; linarith

theorem d_hypTT (h : Cnt.Stand D u u') : HypTT D u u' := by
  obtain ⟨_, p1, p2, t1, t2, _, _, _, _, _, _, _, hm⟩ := h
  exact ⟨p1, p2, t1, t2, (Int.natCast_modEq_iff).2 hm⟩

theorem d_dims {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (ha : VanishingOnXAndXPlus.PlaneWaveLetters D) (hb : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0) :
    ∏ τ, (Module.finrank ℂ (Y.W τ).Wp : ℝ) = dimPi (hc := D.hcW) u := by
  unfold dimPi
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [ha τ u _ (Y.W τ).z (Y.W τ).π (Y.goodW τ).1]
  exact (hb hH u τ).symm

theorem term_L2 {C' Cl Cg cb Cu cT CT C0 A C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hL2 : VanishingOnXAndXPlus.L2HilbertSchmidtPointwise D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C) (ha : VanishingOnXAndXPlus.PlaneWaveLetters D)
    (hb : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) :
    (∏ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ) * aT X t ^ 2 / dimPi (hc := D.hcW) u ≤
      Y.volR t ^ 2 * (∏ τ, lossV large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ)) *
        (∏ τ, tvPr D τ u' ^ D.R.k)⁻¹ := by
  have hrd := d_rdE_pos hH.1
  have hTT := d_hypTT hH.2.1
  have each : ∀ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) / (Module.finrank ℂ (Y.W τ).Wp : ℝ) ≤
      lossV large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) * (tvPr D τ u' ^ D.R.k)⁻¹ := by
    intro τ
    obtain ⟨r1, r2, r3⟩ := Y.rel t hG hrel τ
    rw [← d_nV_eq Y hrd t τ]
    exact hL2 τ u u' hTT Y.θ Y.θ_win (Y.W τ) (Y.goodW τ) (Y.A τ) (Y.goodS τ) (Y.deg_eq τ) (Y.γ t τ) (Y.pt t τ) r1
      (Y.θR t τ) r2 (Y.νR t τ) r3 hH
  have nn : ∀ τ, 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) / (Module.finrank ℂ (Y.W τ).Wp : ℝ) := by
    intro τ
    have h1 : 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ := by
      unfold nV; exact D.R.k_even.pow_nonneg _
    exact div_nonneg (mul_nonneg h1 (d_hsNormSq_nonneg _)) (Nat.cast_nonneg _)
  have P := Finset.prod_le_prod (s := Finset.univ) (fun τ _ => nn τ) (fun τ _ => each τ)
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    d_dims Y hH.1 ha hb] at P
  have e : aT X t ^ 2 = Y.volR t ^ 2 * ∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) := by
    unfold aT
    rw [Real.sq_sqrt (d_hsNormSq_nonneg _), Y.J_norm t hG hrel]
  have hv : 0 ≤ Y.volR t ^ 2 := by positivity
  have Q := mul_le_mul_of_nonneg_left P hv
  calc _ = Y.volR t ^ 2 * ((∏ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ) *
        (∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ))) / dimPi (hc := D.hcW) u) := by rw [e]; ring
    _ ≤ _ := by rw [mul_assoc]; exact Q

theorem aT_irr (Y : LoopTie D large₂ X u u' C1) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : ¬ D.s.relevant t) : aT X t = 0 := by
  unfold aT
  rw [Y.J_irr t hG hrel]
  have : hsNormSq (0 : X.Hpi u' →L[ℂ] X.Hpi u) = 0 := by rw [d_hsNormSq_eq]; simp
  rw [this, Real.sqrt_zero]

theorem d_tprod_inv {C' Cl Cg cb Cu cT CT C0 δ : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (h6 : VanishingOnXAndXPlus.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ) (hδ : 0 ≤ δ) (w : D.what₂.Word) :
    (∏ τ, tvPr D τ w ^ D.R.k)⁻¹ ≤ (1 + δ) * rDD D w := by
  have h := abs_le.1 (h6 hH w)
  have hD := d_Dstar_pos D
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, _⟩ := hH.2.1
  have hd : 0 < (D.duS w : ℝ) := by
    refine lt_of_lt_of_le ?_ (h10 w).1
    have hg : 0 < (D.mem w).A.GamP := lt_trans one_pos (D.mem w).A.one_lt_gammaP
    have hC0 : 0 < C0 := lt_of_lt_of_le one_pos hH.2.2
    positivity
  set P : ℝ := ∏ τ, (Tcrit D w τ / Tr D w) ^ D.R.k with hP
  have e : ∏ τ, tvPr D τ w ^ D.R.k = P := rfl
  rw [e]
  have h1 : D.what₂.Dstar / (D.duS w : ℝ) ≤ (1 + δ) * P := by linarith [h.2]
  have hq : 0 < D.what₂.Dstar / (D.duS w : ℝ) := div_pos hD hd
  have hP0 : 0 < P := by
    by_contra hn
    have : (1 + δ) * P ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hn)
    linarith
  unfold rDD
  rw [inv_le_iff_one_le_mul₀ hP0]
  have h2 : 1 ≤ (1 + δ) * P * ((D.duS w : ℝ) / D.what₂.Dstar) := by
    have := mul_le_mul_of_nonneg_right h1 (div_pos hd hD).le
    rwa [div_mul_div_comm, mul_comm D.what₂.Dstar, div_self (by positivity)] at this
  linarith

theorem d_nProduct {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (Z : GramM D) :
    ∏ τ, nV D (Tu D u) (Tu D u') Z τ =
      LatticeSumBounds.nTot D.R.k D.R.f D.host.v ((∏ τ, Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)) (NT D u) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, h14, _, _, _, _, h19, _⟩ := hH.1
  have h19' : 1 ≤ D.host.v := h19
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hT : (0 : ℝ) < ((Tu D u : ℕ) : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hg : (0 : ℝ) < (gS D : ℝ) := by
    have h0 : 0 < D.host.g 0 := by
      have hb := d_two_le_b D large₂
      have : (0 : ℝ) < (D.host.g 0 : ℝ) := lt_of_lt_of_le (by positivity) (h12 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ _)
      exact_mod_cast this
    have h1 : 0 < D.host.g 1 := by
      have hb := d_two_le_b D large₂
      have : (0 : ℝ) < (D.host.g 1 : ℝ) := lt_of_lt_of_le (by positivity) (h14 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ _)
      exact_mod_cast this
    unfold gS
    exact_mod_cast Nat.mul_pos h0 h1
  have N := Formalism.HermitianLatticeCounting.P.prodVolumeFactor D.what₂.Tau D.R.k D.R.rS (fun τ => Gz D (Tu D u) (Tu D u') Z τ)
    (fun _ => D.host.v) (Tu D u) (gS D) D.host.v hk1 hT hg (fun _ => by linarith) (by simp)
  rw [D.what₂.card_Tau] at N
  have e : ∀ τ, nV D (Tu D u) (Tu D u') Z τ =
      LatticeSumBounds.nv D.R.k D.R.rS (Gz D (Tu D u) (Tu D u') Z τ) (Tu D u) (gS D) D.host.v := by
    intro τ
    unfold nV LatticeSumBounds.nv
    rw [Real.rpow_neg hg.le, Real.rpow_natCast, ← d_m_eq D, inv_pow]
  simp_rw [e]
  rw [N]
  unfold LatticeSumBounds.nTot NT
  rw [← d_m_eq D]
  rfl

end Term

section Missing

variable {D : D7} {large₂ : SizeData₂ D} (X : TermTie D) {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def TermPtsTie : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    TermPts D u u' (fun τ => (Y.W τ).z) (fun τ => (Y.W τ).z') (Y.γ t) (Y.pt t)

def LatticeDeterminantFactorization : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 →
    G0 (X.abelian₂ t) (gS D) (X.fl t) (X.fl' t) =
      (∏ τ, Gz D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)

variable {X}

theorem term_L2_global {C' Cl Cg cb Cu cT CT C0 A C C2 Ch CV δ : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hL2 : VanishingOnXAndXPlus.L2HilbertSchmidtPointwise D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C) (ha : VanishingOnXAndXPlus.PlaneWaveLetters D)
    (hb : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0)
    (hp : VanishingOnXAndXPlus.L2LossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch)
    (h6 : VanishingOnXAndXPlus.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ) (hδ : 0 ≤ δ)
    (hV : VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV) (hT : TermPtsTie X Y)
    (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) :
    (∏ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ) * aT X t ^ 2 / dimPi (hc := D.hcW) u ≤
      (HHZ D large₂.sc.b CV (ZhatL (X.fl t) (X.fl' t)) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 *
        (GamS D large₂ * (∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) ^ (C2 * (D.R.m : ℝ) ^ 2)) *
        ((1 + δ) * rDD D u') := by
  have h1 := term_L2 Y hH hL2 ha hb t hG hrel
  have h2 := hp u u' _ _ _ _ (hT t hG hrel) hH Finset.univ
  have h3 := d_tprod_inv hH.1 h6 hδ u'
  have h4 := hV hH t hG hrel
  have v0 := (Y.volR_pos t).le
  have i0 : 0 ≤ (∏ τ, tvPr D τ u' ^ D.R.k)⁻¹ :=
    inv_nonneg.2 (Finset.prod_nonneg fun τ _ => D.R.k_even.pow_nonneg _)
  have s0 : 0 ≤ ∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) :=
    Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun l _ => le_trans zero_le_one (le_max_left _ _)
  have L0 : 0 ≤ GamS D large₂ * (∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) ^ (C2 * (D.R.m : ℝ) ^ 2) :=
    mul_nonneg (by unfold GamS; exact (Real.exp_pos _).le) (Real.rpow_nonneg s0 _)
  have v2 : Y.volR t ^ 2 ≤ (HHZ D large₂.sc.b CV (ZhatL (X.fl t) (X.fl' t)) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ v0 h4 2
  refine h1.trans ?_
  calc Y.volR t ^ 2 * (∏ τ, lossV large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ)) *
        (∏ τ, tvPr D τ u' ^ D.R.k)⁻¹
      ≤ Y.volR t ^ 2 * (GamS D large₂ * (∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) ^
          (C2 * (D.R.m : ℝ) ^ 2)) * (∏ τ, tvPr D τ u' ^ D.R.k)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) i0
    _ ≤ (HHZ D large₂.sc.b CV (ZhatL (X.fl t) (X.fl' t)) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 *
          (GamS D large₂ * (∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) ^
          (C2 * (D.R.m : ℝ) ^ 2)) * (∏ τ, tvPr D τ u' ^ D.R.k)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right v2 L0) i0
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg (by positivity) L0)

end Missing

section Size

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem d_size_eq (hrd : 0 < D.host.rdE) {Ch : ℝ} (hCh : 0 ≤ Ch) (t : D.s.Term u u') :
    ∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) =
      sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) := by
  unfold sizeZ
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hH2 : 1 ≤ scalePowQuadraticExponent D large₂ Ch := by
    unfold scalePowQuadraticExponent
    exact Real.one_le_rpow (by linarith [d_two_le_b D large₂]) (by positivity)
  set F : ℕ → ℝ := fun l => max 1 (‖DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) l‖ / scalePowQuadraticExponent D large₂ Ch) with hF
  have e1 : sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) = ∏ l : Fin (D.R.rS + 2), F l := by
    unfold sizeV
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [hF]
    unfold DminN
    rw [dif_pos l.isLt]
  have e0 : F 0 = 1 := by
    simp only [hF]
    rw [d_norm_Dmin Y hrd t τ 0 (Nat.zero_le _)]
    have : absDl D (ZhatL (X.fl t) (X.fl' t)) 0 τ = 1 := by
      simp [absDl, absReal, leadMinorE, frameExp]
    rw [this]
    exact max_eq_left (by rw [div_le_one (by linarith)]; exact hH2)
  have e2 : Finset.Icc 1 (D.R.rS + 1) = Finset.Ico 1 (D.R.rS + 2) := by
    ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e1, Fin.prod_univ_eq_prod_range F, Finset.prod_range_succ', e0, mul_one, e2, Finset.prod_Ico_eq_prod_range]
  refine Finset.prod_congr (by simp) fun i hi => ?_
  simp only [hF]
  rw [d_norm_Dmin Y hrd t τ (i + 1) (by have := Finset.mem_range.1 hi; omega), add_comm 1 i]
  rfl

open Classical in

theorem rowBound_relevant {Q : D.s.Pair u u' → Prop}
    (hQ : ∀ p, Q p → D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0) {B : ℝ}
    (h : RowBound X Y (fun p => Q p ∧ D.s.relevant (D.s.pfst p) ∧ D.s.relevant (D.s.psnd p)) B) :
    RowBound X Y Q B := by
  intro S hS
  have e : ∑ p ∈ S.filter (fun p => D.s.relevant (D.s.pfst p) ∧ D.s.relevant (D.s.psnd p)), wP X p =
      ∑ p ∈ S, wP X p := by
    refine Finset.sum_filter_of_ne fun p hp hne => ?_
    by_contra hn
    apply hne
    unfold wP
    by_cases h1 : D.s.relevant (D.s.pfst p)
    · have h2 : ¬ D.s.relevant (D.s.psnd p) := fun h2 => hn ⟨h1, h2⟩
      rw [aT_irr Y _ (hQ p (hS p hp)).2 h2]; ring
    · rw [aT_irr Y _ (hQ p (hS p hp)).1 h1]; ring
  rw [← e]
  exact h _ fun p hp => ⟨hS p (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2⟩

end Size

section AuxiliaryNormPrimes

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

theorem family_statement_of_equivalent_packet {c : ℝ} (h : VanishingOnXAndXPlus.OrbitValuationBound Fm c) : AuxiliaryNormPrimes.KudlaFamilyStatement Fm C1 X Y c := fun _ => h

theorem family_packet_of_equivalent_statement {c : ℝ} (h : AuxiliaryNormPrimes.OrbitValuationBound Fm c) : VanishingOnXAndXPlus.KudlaFamilyStatement Fm C1 X Y c := fun _ => h

theorem family_statement_of_row_bounds (hCl : 1 ≤ sCl Fm)
    (h16 : ∀ Cg cb Cu cT CT C0 A : ℝ, VanishingOnXAndXPlus.FamilySixteenthHypothesis Fm Cg cb Cu cT CT C0 A)
    (hR : RowsF Fm C1 X Y) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 3) : AuxiliaryNormPrimes.KudlaFamilyStatement Fm C1 X Y c := by
  intro hA
  obtain ⟨_, _, _, _, _, _, _, hA'⟩ := hA
  exact family_conclusion_of_row_bounds Fm C1 X Y hCl (fun Cg cb Cu cT CT C0 A => (hA' Cg cb Cu cT CT C0 A).2.2.1) h16 hR hc0 hc

end AuxiliaryNormPrimes

end Formalism.MainNotions.BridgeLemma

end
