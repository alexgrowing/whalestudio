import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstK
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareConvolutionLargeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallConvolutionExistsIntegrableTranslates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DominantTermNeZero

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ConstNZ
theorem constK_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.ConstK := by
  intro h1 h2 hLM h3 h4 h5
  obtain ⟨CF0, hH⟩ := ((_root_.GlobalTheory.T.square_convolution_estimate h1 h2 h3 h4 h5).and (_root_.GlobalTheory.T.exists_integrable_translates_small_convolution h1 h2 h3 h4 h5)).and (_root_.GlobalTheory.T.dominant_term_ne_zero h1 h2 hLM h3 h4 h5)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  obtain ⟨⟨hb, hs⟩, hn⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  intro i j t
  obtain ⟨M, hM, a, τ, τ', n, Φ, hnat, hfl, g, g₁, hI⟩ := hn i j t
  obtain ⟨b', hb'⟩ := ch.rm.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched ch.S.B t ch.rm i j (tensT ch.W a τ) (tensT ch.W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hfl, rfl, rfl⟩
  obtain ⟨z, hz, hzi⟩ := hs i j t M hM _ _ hΘ g g₁
  have hconv : SquareConv ch.W M _ _ z g g₁ := ⟨hb i j t M hM _ _ hΘ g g₁, hzi⟩
  have hc := hch.const i j t M hM _ _ hΘ z g g₁ hconv
  have hL : zdeg z * ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := mul_ne_zero hz hI
  rw [hc] at hL
  exact ⟨⟨M, hM, _, _, hΘ, z, g, g₁, hconv, right_ne_zero_of_mul hL⟩, left_ne_zero_of_mul hL⟩
end GlobalTheory.ConstNZ
end
end
