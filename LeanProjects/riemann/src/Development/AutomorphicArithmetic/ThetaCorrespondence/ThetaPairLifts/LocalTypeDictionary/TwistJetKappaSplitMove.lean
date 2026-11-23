import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarLocalIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFunctionInfiniteRationalLaw
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedSeriesDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DifferentiableMovedOperatorEval
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarLocalIdentityStatement

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
namespace GlobalTheory.SplitMoveKappa
theorem jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hκ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hread⟩ := _root_.GlobalTheory.T.twist_splitMoveFrames_jets hP hI ch hch p hp x y e he s s' hs hs'
  have hC := ch.S.Z.crv
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hsd' := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp (s * x) (s' * y)
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : ch.S.Z.e0 p ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) (0 : Formalism.MainNotions.TaylorLogMetric.VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK ch.S.Z.δ _ hC ch.S.Z.pt0) hn.symm
  have hK0 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D _, GlobalTheory.NormSum.VacInt.sd_std D _, rfl⟩
  have hK1 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) := Or.inr ⟨_, _, hsd.1, hsd.2, rfl⟩
  have hK2 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p (s * x) (s' * y)) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p (s * x) (s' * y))) := Or.inr ⟨_, _, hsd'.1, hsd'.2, rfl⟩
  obtain ⟨-, -, -, htrip⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK ch.S.Z.δ hC (ch.G.pS p).rank (ch.G.pT p).rank
  obtain ⟨μ, hμ⟩ := htrip _ _ _ hK0 hK1 hK2 _ he0.1 he0ne
  have hμ8 : μ ^ 8 = 1 := hμ.2.2.2.2.2.2.2.2.1
  have hμI := hμ.2.2.2.2.2.2.2.2.2
  refine ⟨x₀, y₀, hx₀, hy₀, ζ * μ, ⟨8 * n, by omega, by rw [mul_pow, pow_mul', hζ, pow_mul, hμ8, one_pow, one_pow, one_mul]⟩, r, hr, ?_⟩
  have hd := _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hP hI ch hch p hp x y
  have h1 := hread (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) (hd.const_mul κ) hκ
  intro k
  rw [om_toPair_mul, h1 k]
  congr 3
  refine congrArg _ (funext fun z => ?_)
  have hs1 : (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) =
      κ • Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) := rfl
  rw [hs1, GlobalTheory.InertSign.Iop_smul, hμI]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.SplitMoveKappa
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
theorem _root_.GlobalTheory.T.twist_jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  first | exact @_root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | exact _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | (intros; apply _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move <;> assumption)
end
