import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedIntegralFiniteSupport
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistSmallKernelInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedIntegralFiniteSupportStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.StripPlaces
theorem exists_combination_trivial_off_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁ (z : GA D (G.V (.grid i j)) →₀ ℂ),
  ∃ (z' : GA D (G.V (.grid i j)) →₀ ℂ) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    translates z' (kerSmall W Θ' g g₁) = translates z (kerSmall W Θ' g g₁) ∧ zdeg z' = zdeg z ∧
    ∀ b ∈ z'.support, ∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.grid i j)).gram v b = 1 := by
  intro _ _ _ _ _
  classical
  obtain ⟨CF0, hA⟩ := _root_.GlobalTheory.T.twist_small_kernel_invariant ‹_› ‹_› ‹_› ‹_› ‹_›
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hA⟩ := hA ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  intro G W hW B ρ hρ t i j Θ Θ' hM g g₁ z
  obtain ⟨L, S, hLfg, hLsp, hinv⟩ := hA D large₂ hε hx Γ Pl0 T A Ks R F hS G W hW B ρ hρ t i j Θ Θ' hM g g₁
  choose b' P hP hK using fun b => GlobalTheory.T.exists_finiteSupport_mul_latticeStabilizer (G.V (.grid i j)) L hLfg hLsp S b
  set f := kerSmall W Θ' g g₁ with hf
  have key : ∀ b u, f (u * b' b) = f (u * b) := fun b u => by
    have := hinv _ (hK b) (u * b' b)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  refine ⟨z.mapDomain b', z.support.biUnion P, ?_, ?_, ?_⟩
  · funext u
    simp only [translates]
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finsupp.sum_congr fun b _ => by rw [key]
  · simp only [zdeg]
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  · intro c hc v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hc)
    exact hP b v fun h => hv (Finset.mem_biUnion.2 ⟨b, hb, h⟩)
end GlobalTheory.StripPlaces
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strip_combination_trivial_outside_set : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁ (z : GA D (G.V (.grid i j)) →₀ ℂ),
  ∃ (z' : GA D (G.V (.grid i j)) →₀ ℂ) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    translates z' (kerSmall W Θ' g g₁) = translates z (kerSmall W Θ' g g₁) ∧ zdeg z' = zdeg z ∧
    ∀ b ∈ z'.support, ∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.grid i j)).gram v b = 1 := by
  first | exact @_root_.GlobalTheory.StripPlaces.exists_combination_trivial_off_places | exact _root_.GlobalTheory.StripPlaces.exists_combination_trivial_off_places | (intros; apply _root_.GlobalTheory.StripPlaces.exists_combination_trivial_off_places <;> assumption)
end
