import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftSplitHeckePolysEqTransferResidualPolys
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualPolyTwistedHeckePolyEqContragredientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.CarriedHecke

theorem exists_sys_of_mem_span {K V H I J : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module ℂ H]
    (σ : K →+* ℂ) (op : I → Module.End K V) (j : V →ₛₗ[σ] H) (h : J → Module.End ℂ H) (ι : J → I)
    (hj : ∀ i f, j (op (ι i) f) = h i (j f)) (hc : Formalism.L2.Col.PairComm h) (C : (I → K) → Prop) (v : H)
    (hv : v ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op C : Set V))) (hv0 : v ≠ 0) (l : J → ℂ)
    (he : ∀ i, h i v = l i • v) : ∃ x, C x ∧ ∀ i, σ (x (ι i)) = l i := by
  classical

  have hstep : ∀ (i : J) (a : K) (k : ℕ) (g : V),
      ((h i - σ a • 1) ^ k) (j g) = j (((op (ι i) - a • 1) ^ k) g) := by
    intro i a k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [hj, map_smulₛₗ]
  have himg : ∀ x, ∀ f ∈ Formalism.L2.Col.eigAt op x, j f ∈ Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) := by
    intro x f hf
    rw [Formalism.L2.Col.eigAt, Submodule.mem_iInf] at hf ⊢
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (hf (ι i))
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [hstep, hk, map_zero]⟩
  set T : Submodule ℂ H := ⨆ (x : I → K) (_ : C x), Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) with hT
  have hle : Formalism.L2.Col.eigSum op C ≤ T.comap j := by
    refine iSup₂_le fun x hx f hf => ?_
    exact (le_iSup₂_of_le (f := fun (x : I → K) (_ : C x) => Formalism.L2.Col.eigAt h (fun i => σ (x (ι i)))) x hx le_rfl)
      (himg x f hf)
  have hvT : v ∈ T := by
    refine (Submodule.span_le.2 ?_) hv
    rintro _ ⟨f, hf, rfl⟩
    exact hle hf
  have hvl : v ∈ Formalism.L2.Col.eigAt h l := Formalism.L2.Col.mem_eigAt_of_forall_apply he
  by_contra hno
  push_neg at hno
  have hT' : T ≤ ⨆ (y : J → ℂ) (_ : y ≠ l), Formalism.L2.Col.eigAt h y := by
    refine iSup₂_le fun x hx => ?_
    obtain ⟨i, hi⟩ := hno x hx
    exact le_iSup₂_of_le (f := fun (y : J → ℂ) (_ : y ≠ l) => Formalism.L2.Col.eigAt h y) (fun i => σ (x (ι i)))
      (fun e => hi (congrFun e i)) le_rfl
  exact hv0 ((Submodule.disjoint_def.1 (Formalism.L2.Col.iSupIndep_eigAt hc l)) v hvl (hT' hvT))

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

set_option maxHeartbeats 1000000 in

theorem hecke_polys_of_carries : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hok hW hEx hS hinj p c hcar P hP
  obtain ⟨hC, hSF, hEE, -⟩ := GlobalTheory.T.core_clauses_of_weak_characterisation R F hW hEx
  obtain ⟨hG, hcj, hq⟩ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P hP
  have hq0 : (A3.A.q P : ℂ) ≠ 0 := by
    rw [hq, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact (R.pl P).ne_bot
  obtain ⟨_, _, _, htie⟩ := hC.fam.tie
  obtain ⟨-, hr, ht⟩ := htie.ranks
  have hrX : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := by rw [D.sp.X'_rank, hr, ht]; rfl
  have hrY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
  have hr0 : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm0 : 0 < D.R.m := by have := D.R.two_le_m; omega

  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcar.1
  have hwp : w ∈ R.EEp3 p :=
    (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c hcar) hw
  have hv0 : LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := fun h0 => hw0 (hinj p w hwp h0)
  have hwE : w ∈ EEc R.toRealDat R.SF c := (hEE c) ▸ hw
  obtain ⟨hX, hXo, hXn⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  obtain ⟨zE, hmE, hpE⟩ := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 ⟨P, hP⟩
  have heig : ∀ k : Fin (D.sp.X'.rank + 1), hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)
      (LinearMap.adjoint (R.Th A3.A.μ0) w) = GlobalTheory.Hk3.evC (Yc D 0) (R.pl P) (fun d => c (R.pl P) (dualLab d))
        (GlobalTheory.Hk3.splitC (Yc D 0).rank (zE k)) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun k =>
    (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 (R.pl P) hG _ _ (hmE k (Nat.lt_succ_iff.1 k.2)) hX hXo).2 c w hwE
  obtain ⟨x, hx, hxe⟩ := exists_sys_of_mem_span D.what₂.embLL (A3.rowI A3.A.μ0).opAll (R.jX A3.A.μ0)
    (fun k : Fin (D.sp.X'.rank + 1) => hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1))
    (fun k => Sum.inl ((⟨P, hP⟩ : A3.A.ok A3.A.μ0), (k : ℕ)))
    (fun k f => (GlobalTheory.T.familySplitOperators_eq_labelOperators_models R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo ⟨P, hP⟩ k
      (Nat.lt_succ_iff.1 k.2) f)
    (fun k k' => hXn.1 _ _ hG hG _ _) _ _ (hcar.2 (Submodule.mem_map_of_mem hw)) hv0 _ heig

  have hE : (p.1.1 P).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) fun j => c (R.pl P) (dualLab (splitLab D.R.r j))).comp
        (C ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) := by
    have h1 := hpE fun j => c (R.pl P) (dualLab (splitLab (Yc D 0).rank j))
    have h2 : (Formalism.L2.Col.heckePolyOf (A3.A.r + D.R.m * A3.A.t) (A3.A.q P) fun k => x (Sum.inl (⟨P, hP⟩, k))) =
        p.1.1 P * (A3.A.fam.R A3.A.μ0).blockProd ⟨P, hP⟩ := hx.1 ⟨P, hP⟩
    have h3 := congrArg (Polynomial.map D.what₂.embLL) h2
    rw [Formalism.L2.Col.map_heckePolyOf, Polynomial.map_mul, ← hrX] at h3
    rw [GlobalTheory.Hk3.Link.heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (x (Sum.inl (⟨P, hP⟩, k)))) ?_, h3, hrY] at h1
    · refine mul_right_cancel₀ ?_ h1
      rw [Ne, Polynomial.map_eq_zero]
      unfold BlockDat.blockProd
      refine List.prod_ne_zero fun h => ?_
      obtain ⟨ν, -, hν⟩ := List.mem_map.1 h
      exact GlobalTheory.Hk3.Link.blockPoly_ne_zero _ _ _ hν
    · intro k hk
      have h5 := hxe ⟨k, Nat.lt_succ_iff.2 hk⟩
      exact (h5.trans (GlobalTheory.Hk3.Link.evC_splitC (Yc D 0) (R.pl P) hcj _ _)).symm

  obtain ⟨h, hEo, -, -, hev, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hC hS R.SF hSF
  have hne : R.HE.e w ≠ 0 := fun h0 => hw0 ((hC.models.HE).1 (h0.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ : ∃ v, R.HE.e w v ≠ 0 := by
    by_contra hcon
    exact hne (MultilinearMap.ext fun v => not_not.1 fun hv => hcon ⟨v, hv⟩)
  obtain ⟨cc, hβ⟩ := hC.lev.βY 0 hm0
  have hlev := (GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ (R.pl P)
    (by
      have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).2.1 A3.A.μ0 (R.pl P) hG).1
      rw [Nat.cast_pow]
      intro hmem
      rcases Nat.eq_zero_or_pos cc with h0 | h0
      · rw [h0, pow_zero] at hmem
        exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
      · exact hN ((R.pl P).isPrime.mem_of_pow_mem _ hmem))
    (fun PP hPP => hG PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).1
  have hm := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hwE)).1
  have hrel := GlobalTheory.Hk3.Link.eig_rel (Yc D 0) (R.pl P) hcj _ hv (fun k hk g =>
      (GlobalTheory.Hk3.Link.mult_lev R.θ _ _ _ _ hm v k (hlev k hk).1 g).trans
        ((congrArg (fun z : ℂ => z * R.HE.e w v g) (hlev k hk).2).trans (one_mul _)))
      (fun d => c (R.pl P) (dualLab d)) (fun d hd => by
      have h5 := (hEo (R.pl P) hG (Finsupp.single d 1) w).symm.trans
        ((congrArg R.HE.e (hev c _ hG (Finsupp.single d 1) w hwE)).trans (map_smul _ _ _))
      exact congrArg (fun U : MMap (R.MY 0) => U v) (h5.trans
        (congrArg (fun z : ℂ => z • R.HE.e w) (GlobalTheory.Hk3.Link.evC_single (Yc D 0) (R.pl P) _ d hd))))
  rw [hrY] at hrel
  simp only [dualLab_dualLab] at hrel
  obtain ⟨hb0, hab⟩ := hrel
  have hrr : c (R.pl P) (splitLab D.R.r D.R.r) * c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) = 1 := by
    rw [hab D.R.r le_rfl, Nat.sub_self, hb0]
  have hbr : c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) ≠ 0 := right_ne_zero_of_mul_eq_one hrr
  have ha0 : c (R.pl P) (splitLab D.R.r 0) = 1 := by
    have := hab 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at this
    exact mul_right_cancel₀ hbr (this.trans (one_mul _).symm)
  have hba : ∀ j, j ≤ D.R.r → c (R.pl P) (dualLab (splitLab D.R.r j)) * c (R.pl P) (splitLab D.R.r D.R.r) =
      c (R.pl P) (splitLab D.R.r (D.R.r - j)) := by
    intro j hj
    have := hab (D.R.r - j) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hj] at this
    rw [← this, mul_assoc, mul_comm _ (c (R.pl P) (splitLab D.R.r D.R.r)), hrr, mul_one]
  have hdual := GlobalTheory.T.dualPoly_twistedHeckePoly_eq_contragredient ℂ D.R.r (A3.A.q P) (fun j => c (R.pl P) (splitLab D.R.r j))
    (fun j => c (R.pl P) (dualLab (splitLab D.R.r j))) ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) 1 hq0
    (pow_ne_zero _ hq0) hr0 ha0 hba
  have hs0 : ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) ≠ 0 := pow_ne_zero _ hq0
  constructor
  · unfold RealDat.polE
    rw [hE, Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hs0, C_1, one_mul, Polynomial.comp_X]
  · unfold RealDat.polW
    rw [GlobalTheory.Hk3.Link.dualPoly_map, hE, map_pow, map_natCast]
    have hsc : (A3.A.q P : ℂ) ^ (D.R.r - 1 + D.R.m / 2 * D.R.t) =
        (A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t) * 1 * (A3.A.q P : ℂ) ^ (D.R.r - 1) := by
      rw [pow_add]; ring
    rw [hsc, hdual, C_1, one_mul, Polynomial.comp_X]

end GlobalTheory.CarriedHecke
