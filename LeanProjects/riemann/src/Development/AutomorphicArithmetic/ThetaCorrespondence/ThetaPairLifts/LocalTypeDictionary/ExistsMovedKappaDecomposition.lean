import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFiniteTranslate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFiniteTranslateStatement

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
namespace GlobalTheory.MovedKappaDec
theorem exists_movedKappa_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ X hX Q hQ x
  obtain ⟨r, s, k, hr, hs, hk, e⟩ := GlobalTheory.RatSplitLat.exists_rat_split_lat (ch.G.V X) (ch.S.N.fr X) (∏ q ∈ Q, q)
    (Finset.prod_pos fun q hq => (hQ q hq).pos) (x * ch.S.N.u X)
  have hs' := GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit _ Q s hs
  have hB := GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL ch.S.toGridChoice X hX k hk
  refine ⟨r, s, k * (ch.S.N.u X)⁻¹, hr, hs', hB, fun q hq => ?_, ?_⟩
  · have key : ∀ s' ∈ GlobalTheory.MovedKappaEx.splitOff (ch.G.V X) Q, ∀ y : FinPt ch.G X,
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s' * y)) (GlobalTheory.SumSize.latAt ch.S.toGridChoice X y) := by
      intro s' hs'
      induction hs' using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact fun y => GlobalTheory.MovedSplitEq.eqAt_latAt_mul ch.S.toGridChoice X hX q (hQ q hq) e he (hoff q hq) g y hsupp
      | one => exact fun y => by rw [one_mul]; exact eqAt_refl q _
      | mul a b _ _ ha hb => exact fun y => by rw [mul_assoc]; exact eqAt_trans (ha (b * y)) (hb y)
      | inv a _ ha =>
        intro y
        have := ha (a⁻¹ * y)
        rw [mul_inv_cancel_left] at this
        exact eqAt_symm this
    have := key s hs' (k * (ch.S.N.u X)⁻¹)
    rw [hB] at this
    exact this
  · rw [← mul_assoc, ← e, mul_inv_cancel_right]
end GlobalTheory.MovedKappaDec
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
theorem _root_.GlobalTheory.T.movedKappa_decomposition_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  first | exact @_root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition | exact _root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition | (intros; apply _root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition <;> assumption)
end
