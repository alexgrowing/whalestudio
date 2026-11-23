import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentUnitDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentUnitDecompositionStatement

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
noncomputable section
namespace GlobalTheory.SplitCharValue
theorem splitCharValue_split_characters : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ x₀ : (Formalism.L2.Theta.AE D)ˣ,
    (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) →
    (Mod1All ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ Mod1All ((ch.G.chrT p x₀ : Circle) : ℂ)) ∧
    ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrT p x₀ : Circle) : ℂ) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp e he x₀ hx
  have hW := ch.W.om_is p (defPair_inRange hp)
  obtain ⟨e', he', hoff, a, hx'⟩ : ∃ e' : Formalism.L2.Theta.AE D, IsSplitIdem D e' ∧
      (∀ q, GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.OffPrime e' q) ∧
      ∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e' * a + (1 - e') := by
    obtain ⟨a, ha | ha⟩ := hx
    · exact ⟨e, he, fun _ h => h, a, ha⟩
    · exact ⟨cA D e, GlobalTheory.ConjAdjWeil.isSplitIdem_conj he, fun _ h => offPrime_conj h, a, ha⟩
  have hS := char_split_value D _ _ hW.hecS hW.resS e' he' x₀ a hx'
  have hT := char_split_value D _ _ hW.hecT hW.resT e' he' x₀ a hx'
  exact ⟨⟨hS.1, hT.1⟩, fun q _ hq => ⟨hS.2 q (hoff q hq), hT.2 q (hoff q hq)⟩⟩
end GlobalTheory.SplitCharValue
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
theorem _root_.GlobalTheory.T.twist_split_character_values : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ x₀ : (Formalism.L2.Theta.AE D)ˣ,
    (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) →
    (Mod1All ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ Mod1All ((ch.G.chrT p x₀ : Circle) : ℂ)) ∧
    ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrT p x₀ : Circle) : ℂ) := by
  first | exact @_root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters | exact _root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters | (intros; apply _root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters <;> assumption)
end
