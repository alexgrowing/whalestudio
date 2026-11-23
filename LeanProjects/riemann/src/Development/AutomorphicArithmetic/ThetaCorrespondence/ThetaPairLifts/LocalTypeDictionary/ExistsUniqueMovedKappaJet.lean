import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitModulusScalarLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsMovedKappaDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumRootExistsAlgebraic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplittingOfMovedKappaTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRationalMoveOfJets
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DifferentiableMovedOperatorEval
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedSeriesDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitModulusScalarLocalStatement

section
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
theorem jet_kappa_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ κ' : ℂ),
    JetKap ch p x y κ → JetKap ch p x y κ' → κ = κ' := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ κ' h1 h2
  set F := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) with hFdef
  have hF : Differentiable ℂ F :=
    _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hPr hInp ch hIs p hp x y
  obtain ⟨hsd, hsd'⟩ := _root_.GlobalTheory.MovedSD.moved_series_decomposition hPr hInp ch hIs p hp x y
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
end GlobalTheory.MovedKappaEx
namespace GlobalTheory.MovedKappaEx
theorem exists_moved_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
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
    obtain ⟨r, s, x₀, hr, hs, hx₀, hsx, rfl⟩ := _root_.GlobalTheory.T.movedKappa_decomposition_exists hPr hInp ch hIs _ hns Q hQ x
    obtain ⟨r', s', y₀, hr', hs', hy₀, hsy, rfl⟩ := _root_.GlobalTheory.T.movedKappa_decomposition_exists hPr hInp ch hIs _ hnb Q hQ y
    obtain ⟨κ₀, hm₀, hu₀, hj₀⟩ := _root_.GlobalTheory.T.moved_vacuum_has_algebraic_root hPr hInp ch hIs p hp x₀ y₀ hx₀ hy₀
    have stepS : ∀ g ∈ splitOff (ch.G.V p.small) Q, ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
        (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
        ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
      have gen : ∀ g : FinPt ch.G p.small, (∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧
          SuppAt e _ (g : GA D (ch.G.V p.small))) → ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
          (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
          ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
        rintro g ⟨e, he, hoff, hsupp⟩ x' κ hj hm hu
        obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.splitting_of_moved_kappa_twist hPr hInp ch hIs p hp x' y₀ κ hj e he g 1 hsupp
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
        obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.splitting_of_moved_kappa_twist hPr hInp ch hIs p hp (s * x₀) y' κ hj e he 1 g
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
    obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.rational_jet_move_exists hPr hInp ch hIs p hp _ _ κ₂ hj₂ r r' hr hr'
    refine ⟨c * κ₂, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm₂, fun q hq hf => unitAt_mul hc hm₂ ?_ (hu₂ q hq hf), ?_⟩
    · obtain ⟨hqx, hqy⟩ := hQx q hq
      rw [mul_assoc] at hqx hqy
      exact @hcu q hf (hsx q hq) (hsy q hq) hqx hqy
    · rw [mul_assoc, mul_assoc]
      exact hjc
  obtain ⟨κ₀, hm, -, hj⟩ := chain ∅ (by simp) (by simp)
  refine ⟨κ₀, hm, fun q hf hx hy lam => ?_, hj⟩
  obtain ⟨κq, -, hu, hjq⟩ := chain {q} (by simpa using hf.out) (by simpa using ⟨hx, hy⟩)
  obtain rfl := _root_.GlobalTheory.MovedKappaEx.jet_kappa_unique hPr hInp ch hIs p hp x y κ₀ κq hj hjq
  exact hu q (Finset.mem_singleton_self q) hf lam
end GlobalTheory.MovedKappaEx
end
end

section
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_moved_kappa_jet : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ₀ : ℂ, Mod1All κ₀ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ₀‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ₀ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedKappaEx.exists_moved_kappa | exact _root_.GlobalTheory.MovedKappaEx.exists_moved_kappa | (intros; apply _root_.GlobalTheory.MovedKappaEx.exists_moved_kappa <;> assumption)
end
