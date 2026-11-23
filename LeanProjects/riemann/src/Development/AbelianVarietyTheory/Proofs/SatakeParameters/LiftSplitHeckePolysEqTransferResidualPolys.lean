import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperatorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualPolyTwistedHeckePolyEqContragredientStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Link

theorem dualPoly_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (s : K) (p : K[X]) :
    (dualPoly s p).map φ = dualPoly (φ s) (p.map φ) := by
  have h : (p.map φ).reverse = p.reverse.map φ := by
    rw [Polynomial.reverse, Polynomial.reverse, natDegree_map, reflect_map]
  rw [dualPoly, dualPoly, h, Polynomial.map_mul, map_C, Polynomial.map_comp, Polynomial.map_mul, map_C, map_X,
    leadingCoeff_map, map_inv₀]

theorem heckePolyOf_congr {L : Type} [Field L] (n q : ℕ) {a b : ℕ → L} (h : ∀ k, k ≤ n → a k = b k) :
    Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

theorem blockPoly_ne_zero {L : Type} [Field L] (ν : L) (q t : ℕ) : Formalism.L2.Col.blockPoly ν q t ≠ 0 := by
  unfold Formalism.L2.Col.blockPoly
  refine Finset.prod_ne_zero_iff.2 fun c _ h => ?_
  have := congrArg (fun f => Polynomial.coeff f 0) h
  simp at this

variable {D : D7}

def rt (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun F h => F (h * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F h; simp
  map_mul' g g' := by ext F h; simp [mul_assoc]

theorem opOf_rt (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) : opOf (rt V) P c = hk V P c := by
  unfold opOf hk
  refine Finsupp.sum_congr fun d _ => ?_
  congr 1
  ext F h
  simp [heckeLin, rt, LinearMap.sum_apply, Finset.sum_apply]

theorem isLab_split (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (j : ℕ) (hj : j ≤ V.rank) :
    IsLab V P (splitLab V.rank j) := by
  refine (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing V P _).2 ⟨?_, ?_, fun h => absurd h hP⟩
  · simp [splitLab]; omega
  · simp [splitLab, List.pairwise_append, List.pairwise_replicate]

theorem evC_single (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]

theorem evC_splitC (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (a : List ℤ → ℂ) (z : ℕ → ℂ) :
    evC V P a (splitC V.rank z) = ∑ j ∈ Finset.range (V.rank + 1), z j * a (splitLab V.rank j) := by
  unfold evC splitC
  rw [← Finsupp.sum_finset_sum_index (by simp) (by intro d x y; split_ifs <;> simp [add_mul])]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finsupp.sum_single_index (by simp), if_pos (isLab_split V P hP j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))]

theorem eig_rel (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (u : GA D V → ℂ) (hu : u ≠ 0)
    (hfix : ∀ k ∈ hyp V P, ∀ h, u (h * k) = u h) (c : List ℤ → ℂ)
    (hc : ∀ d, IsLab V P d → hk V P (Finsupp.single d 1) u = c d • u) :
    c (splitLab V.rank 0) = 1 ∧
      ∀ j, j ≤ V.rank → c (dualLab (splitLab V.rank j)) * c (splitLab V.rank V.rank) = c (splitLab V.rank (V.rank - j)) := by
  have hfix' : ∀ k ∈ hyp V P, rt V k u = u := fun k hk => funext (hfix k hk)
  obtain ⟨-, -, ⟨h0, h1⟩, hd, -⟩ := GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P
  refine ⟨?_, fun j hj => ?_⟩
  · have e : splitLab V.rank 0 = List.replicate V.rank 0 := by simp [splitLab]
    have := h1 _ (rt V) u hfix'
    rw [opOf_rt, hc _ h0] at this
    rw [e]
    exact smul_left_injective ℂ hu (this.trans (one_smul ℂ u).symm)
  · have := GlobalTheory.T.dualSplitLabel_operator_mul_scalar_operator V P hP j hj _ (rt V) u hfix'
    rw [opOf_rt, opOf_rt, opOf_rt, hc _ (isLab_split V P hP _ le_rfl), map_smul,
      hc _ ((hd _).1.1 (isLab_split V P hP j hj)), hc _ (isLab_split V P hP _ (Nat.sub_le _ _)), smul_smul, mul_comm] at this
    exact smul_left_injective ℂ hu this

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (U : MMap M) (hU : U ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, U v (g * k) = χ k * U v g := by
  intro v k hk g
  induction hU using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, mul_add]
  | smul a x _ hx => simp [hx, mul_left_comm]

set_option maxHeartbeats 400000 in

theorem hasRes_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i c (p : Pl0 → D.what₂.LL[X]) (sX : A.ok A.μ0 × ℕ → D.what₂.LL) (sV : A.ok A.μ0 × ℕ → D.what₂.LL), (A.fam.R A.μ0).HasRes p sX → ∀ hX hV, IsOpsX R A.μ0 hX → IsOpsV R i A.μ0 hV → ∀ w ∈ EEc R SF c, LinearMap.adjoint (R.Th A.μ0) w ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ D.sp.X'.rank → hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A.μ0) w) = D.what₂.embLL (sX (P, k)) • LinearMap.adjoint (R.Th A.μ0) w) → ∀ y, R.thG i A.μ0 y ∈ Wcc R SF i c → R.thG i A.μ0 y ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ (Vc D i).rank → hV (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) y = D.what₂.embLL (sV (P, k)) • y) → (A.fam.L i A.μ0).HasRes (A.fam.tr i p) sV := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS hX0 SF hSF i c p sX sV hp hX hV hXo hVo w hw hw0 heX y hy hy0 heV P
  change A.ok A.μ0 at P
  obtain ⟨hG, hcj, hq⟩ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.2.2 hC.fam A.μ0 P.1 P.2
  have hq0 : (A.q P : ℂ) ≠ 0 := by
    rw [hq, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact (R.pl P).ne_bot
  obtain ⟨_, _, _, htie⟩ := hC.fam.tie
  obtain ⟨-, hr, ht⟩ := htie.ranks
  have hrX : D.sp.X'.rank = A.r + D.R.m * A.t := by rw [D.sp.X'_rank, hr, ht]; rfl
  have hrV : (Vc D i).rank = A.r + A.t := by rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2, hr, ht]; rfl
  have hrW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hrY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
  have hr0 : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega

  obtain ⟨zE, hmE, hpE⟩ := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R F hI hC hS A.μ0 P
  have hE : (p P).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun j => c (R.pl P) (dualLab (splitLab D.R.r j))).comp
        (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) := by
    have h1 := hpE fun j => c (R.pl P) (dualLab (splitLab (Yc D 0).rank j))
    have h2 : (Formalism.L2.Col.heckePolyOf (A.r + D.R.m * A.t) (A.q P) fun k => sX (P, k)) =
        p P * (A.fam.R A.μ0).blockProd P := hp P
    have h3 := congrArg (Polynomial.map D.what₂.embLL) h2
    rw [Formalism.L2.Col.map_heckePolyOf, Polynomial.map_mul, ← hrX] at h3
    rw [heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (sX (P, k))) ?_, h3, hrY] at h1
    · refine mul_right_cancel₀ ?_ h1
      rw [Ne, Polynomial.map_eq_zero]
      unfold BlockDat.blockProd
      refine List.prod_ne_zero fun h => ?_
      obtain ⟨ν, -, hν⟩ := List.mem_map.1 h
      exact blockPoly_ne_zero _ _ _ hν
    · intro k hk
      have h4 := (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R F hC hS SF hSF A.μ0 (R.pl P) hG _ _ (hmE k hk) hX hXo).2 c w hw
      have h5 := smul_left_injective ℂ hw0 ((heX P k hk).symm.trans h4)
      exact ((h5.trans (evC_splitC (Yc D 0) (R.pl P) hcj _ _))).symm

  obtain ⟨zW, hmW, hpW⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F hC hS i A.μ0 P
  obtain ⟨h, hWo, -, -, -, -, hev, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hX0 SF hSF i
  have hW : (Formalism.L2.Col.heckePolyOf (A.r + A.t) (A.q P) fun k => sV (P, k)).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun j => c (R.pl P) (splitLab D.R.r j)).comp
        (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) *
        ((A.fam.L i A.μ0).blockProd P).map D.what₂.embLL := by
    have h1 := hpW fun j => c (R.pl P) (splitLab (Wc D i).rank j)
    rw [heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (sV (P, k))) ?_, hrW] at h1
    · rw [Formalism.L2.Col.map_heckePolyOf, ← hrV, h1]
    · intro k hk
      have h4 := (GlobalTheory.T.theta_intertwines_matched_operators R F hC hS hX0 SF hSF i A.μ0 (R.pl P) hG _ _ (hmW k hk) hV hVo).1 h hWo y
      have h5 := ((congrArg (R.thG i A.μ0) (heV P k hk)).trans (map_smul _ _ _)).symm.trans (h4.trans (hev c _ hG _ _ hy))
      exact ((smul_left_injective ℂ hy0 h5).trans (evC_splitC (Wc D i) (R.pl P) hcj _ _)).symm

  have hne : (R.HW i (sg0 D A)).e (R.thG i A.μ0 y) ≠ 0 := fun h0 =>
    hy0 ((hC.models.HW i (sg0 D A)).1 (h0.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ : ∃ v, (R.HW i (sg0 D A)).e (R.thG i A.μ0 y) v ≠ 0 := by
    by_contra hcon
    exact hne (MultilinearMap.ext fun v => not_not.1 fun hv => hcon ⟨v, hv⟩)
  obtain ⟨cc, hβ⟩ := hC.lev.βW i
  have hlev := (GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) _ (R.datWp i R.triv) hβ (R.pl P)
    (by rw [one_pow, Nat.cast_one]; exact fun h1 => (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
    (fun PP hPP => hG PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).1
  have hm := (Submodule.mem_inf.1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hy)).2).1
  have hrel := eig_rel (Wc D i) (R.pl P) hcj _ hv (fun k hk g =>
      (mult_lev R.θ _ _ _ _ hm v k (hlev k hk).1 g).trans ((congrArg (fun z : ℂ => z * (R.HW i (sg0 D A)).e (R.thG i A.μ0 y) v g) (hlev k hk).2).trans (one_mul _))) (c (R.pl P)) (fun d hd => by
      have h5 := (hWo (R.pl P) hG (Finsupp.single d 1) (R.thG i A.μ0 y)).symm.trans
        ((congrArg (R.HW i (sg0 D A)).e (hev c _ hG (Finsupp.single d 1) _ hy)).trans (map_smul _ _ _))
      exact congrArg (fun U : MMap (R.MW i (sg0 D A)) => U v) (h5.trans
        (congrArg (fun z : ℂ => z • (R.HW i (sg0 D A)).e (R.thG i A.μ0 y)) (evC_single (Wc D i) (R.pl P) (c (R.pl P)) d hd))))
  rw [hrW] at hrel
  have hdual := GlobalTheory.T.dualPoly_twistedHeckePoly_eq_contragredient ℂ D.R.r (A.q P) (fun j => c (R.pl P) (splitLab D.R.r j))
    (fun j => c (R.pl P) (dualLab (splitLab D.R.r j))) ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t))
    (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) hq0 (pow_ne_zero _ hq0) hr0 hrel.1 hrel.2
  have hsc : D.what₂.embLL (trScale A.r D.R.m A.t A.q A.etaVal P) = (A.q P : ℂ) ^ (D.R.m / 2 * D.R.t) *
      (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * (A.q P : ℂ) ^ (D.R.r - 1) := by
    have he : (2 * A.r + (D.R.m + 1) * A.t - 1) / 2 = D.R.m / 2 * D.R.t + (D.R.t + 1) / 2 + (D.R.r - 1) := by
      obtain ⟨a, ha⟩ := D.R.m_even
      obtain ⟨b, hb⟩ := D.R.t_odd
      rw [hr, ht, ha, show (a + a) / 2 = a by omega, show (a + a + 1) * D.R.t = 2 * (a * D.R.t) + D.R.t by ring]
      omega
    rw [trScale, map_mul, map_pow, map_natCast, he, pow_add, pow_add]
    ring
  apply Polynomial.map_injective D.what₂.embLL D.what₂.embLL.injective
  change (Formalism.L2.Col.heckePolyOf (A.r + A.t) (A.q P) fun k => sV (P, k)).map D.what₂.embLL =
    (dualPoly (trScale A.r D.R.m A.t A.q A.etaVal P) (p P) * (A.fam.L i A.μ0).blockProd P).map D.what₂.embLL
  rw [hW, Polynomial.map_mul, dualPoly_map, hsc, hE, hdual]

end GlobalTheory.Hk3.Link

end
