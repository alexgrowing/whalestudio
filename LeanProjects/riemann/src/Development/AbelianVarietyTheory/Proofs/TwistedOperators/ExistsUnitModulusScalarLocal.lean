import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenLevelGroupSubgroupOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarIdempotentValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarRationalTranslateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFiniteTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaEx

theorem selfDualLattice_intertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial' (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

theorem jetKap_unique : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ κ' : ℂ),
    JetKap ch p x y κ → JetKap ch p x y κ' → κ = κ' := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ κ' h1 h2
  set F := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) with hFdef
  have hF : Differentiable ℂ F :=
    GlobalTheory.MovedDict.Entire.differentiable_intertwining_moved hPr hInp ch hIs p hp x y
  obtain ⟨hsd, hsd'⟩ := GlobalTheory.MovedSD.sd_srcLat_tgtLat hPr hInp ch hIs p hp x y
  have hF0 : F ≠ 0 := selfDualLattice_intertwiner_baseVector_ne_zero ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) hsd hsd'
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D hF hF0
  have e := (h1 α).symm.trans (h2 α)
  rw [applyAt0_monomial', applyAt0_monomial', GlobalTheory.ProdThetaConj.taylor_const_mul hF,
    GlobalTheory.ProdThetaConj.taylor_const_mul hF] at e
  have e' := (opp p).injective (mul_left_cancel₀ (ch.S.Z.c0 p).ne_zero e)
  have hP : (α.prod fun v e => period ch.S.Z.δ v.1 ^ e) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e'' := mul_left_cancel₀ (mul_ne_zero hP hfac) (by simpa only [mul_assoc] using e')
  exact mul_right_cancel₀ hα e''

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : UnitAt q a)
    (hub : UnitAt q b) : UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dif_pos hab, dif_pos ha', dif_pos hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

end GlobalTheory.MovedKappaEx

namespace GlobalTheory.MovedKappaEx

theorem exists_kappa : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ₀ : ℂ, Mod1All κ₀ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ₀‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ₀ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  obtain ⟨hns, hnb⟩ := hp.nodes
  have chain : ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
      (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) ∧
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _)) →
      ∃ κ, Mod1All κ ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) ∧ JetKap ch p x y κ := by
    intro Q hQ hQx
    obtain ⟨r, s, x₀, hr, hs, hx₀, hsx, rfl⟩ := GlobalTheory.T.exists_rational_finite_translate hPr hInp ch hIs _ hns Q hQ x
    obtain ⟨r', s', y₀, hr', hs', hy₀, hsy, rfl⟩ := GlobalTheory.T.exists_rational_finite_translate hPr hInp ch hIs _ hnb Q hQ y
    obtain ⟨κ₀, hm₀, hu₀, hj₀⟩ := GlobalTheory.T.standard_lattice_size_sum hPr hInp ch hIs p hp x₀ y₀ hx₀ hy₀
    have stepS : ∀ g ∈ splitOff (ch.G.V p.small) Q, ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
        (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
        ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
      have gen : ∀ g : FinPt ch.G p.small, (∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧
          SuppAt e _ (g : GA D (ch.G.V p.small))) → ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
          (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
          ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
        rintro g ⟨e, he, hoff, hsupp⟩ x' κ hj hm hu
        obtain ⟨c, hc, hcu, hjc⟩ := GlobalTheory.T.jet_scalar_idempotent_value hPr hInp ch hIs p hp x' y₀ κ hj e he g 1 hsupp
          (by rw [OneMemClass.coe_one]; exact GlobalTheory.LeviSplitChar.suppAt_one e _)
        rw [one_mul] at hjc
        exact ⟨c * κ, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm,
          fun q hq hf => unitAt_mul hc hm (@hcu q hf (hoff q hq)) (hu q hq hf), hjc⟩
      intro g hg
      induction hg using Subgroup.closure_induction'' with
      | mem g hg => exact gen g hg
      | inv_mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact gen g⁻¹ ⟨e, he, hoff, by rw [InvMemClass.coe_inv]; exact GlobalTheory.SplitPlace.suppAt_inv hsupp⟩
      | one => intro x' κ hj hm hu; exact ⟨κ, hm, hu, by rwa [one_mul]⟩
      | mul g₁ g₂ _ _ h1 h2 =>
        intro x' κ hj hm hu
        obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := h2 x' κ hj hm hu
        obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := h1 _ κ₁ hj₁ hm₁ hu₁
        exact ⟨κ₂, hm₂, hu₂, by rwa [mul_assoc]⟩
    have stepB : ∀ g ∈ splitOff (ch.G.V p.big) Q, ∀ (y' : FinPt ch.G p.big) (κ : ℂ), JetKap ch p (s * x₀) y' κ → Mod1All κ →
        (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
        ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (s * x₀) (g * y') κ' := by
      have gen : ∀ g : FinPt ch.G p.big, (∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧
          SuppAt e _ (g : GA D (ch.G.V p.big))) → ∀ (y' : FinPt ch.G p.big) (κ : ℂ), JetKap ch p (s * x₀) y' κ → Mod1All κ →
          (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
          ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (s * x₀) (g * y') κ' := by
        rintro g ⟨e, he, hoff, hsupp⟩ y' κ hj hm hu
        obtain ⟨c, hc, hcu, hjc⟩ := GlobalTheory.T.jet_scalar_idempotent_value hPr hInp ch hIs p hp (s * x₀) y' κ hj e he 1 g
          (by rw [OneMemClass.coe_one]; exact GlobalTheory.LeviSplitChar.suppAt_one e _) hsupp
        rw [one_mul] at hjc
        exact ⟨c * κ, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm,
          fun q hq hf => unitAt_mul hc hm (@hcu q hf (hoff q hq)) (hu q hq hf), hjc⟩
      intro g hg
      induction hg using Subgroup.closure_induction'' with
      | mem g hg => exact gen g hg
      | inv_mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact gen g⁻¹ ⟨e, he, hoff, by rw [InvMemClass.coe_inv]; exact GlobalTheory.SplitPlace.suppAt_inv hsupp⟩
      | one => intro y' κ hj hm hu; exact ⟨κ, hm, hu, by rwa [one_mul]⟩
      | mul g₁ g₂ _ _ h1 h2 =>
        intro y' κ hj hm hu
        obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := h2 y' κ hj hm hu
        obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := h1 _ κ₁ hj₁ hm₁ hu₁
        exact ⟨κ₂, hm₂, hu₂, by rwa [mul_assoc]⟩
    obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := stepS s hs x₀ κ₀ hj₀ hm₀ (fun q _ hf => @hu₀ q hf)
    obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := stepB s' hs' y₀ κ₁ hj₁ hm₁ hu₁
    obtain ⟨c, hc, hcu, hjc⟩ := GlobalTheory.T.jet_scalar_rational_translate hPr hInp ch hIs p hp _ _ κ₂ hj₂ r r' hr hr'
    refine ⟨c * κ₂, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm₂, fun q hq hf => unitAt_mul hc hm₂ ?_ (hu₂ q hq hf), ?_⟩
    · obtain ⟨hqx, hqy⟩ := hQx q hq
      rw [mul_assoc] at hqx hqy
      exact @hcu q hf (hsx q hq) (hsy q hq) hqx hqy
    · rw [mul_assoc, mul_assoc]
      exact hjc
  obtain ⟨κ₀, hm, -, hj⟩ := chain ∅ (by simp) (by simp)
  refine ⟨κ₀, hm, fun q hf hx hy lam => ?_, hj⟩
  obtain ⟨κq, -, hu, hjq⟩ := chain {q} (by simpa using hf.out) (by simpa using ⟨hx, hy⟩)
  obtain rfl := jetKap_unique hPr hInp ch hIs p hp x y κ₀ κq hj hjq
  exact hu q (Finset.mem_singleton_self q) hf lam

end GlobalTheory.MovedKappaEx
