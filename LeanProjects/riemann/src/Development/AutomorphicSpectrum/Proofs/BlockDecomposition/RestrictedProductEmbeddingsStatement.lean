import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductEmbeddings
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_embeddings : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [∀ i, TopologicalSpace (Hl i)] [∀ i, T2Space (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH : ∀ i, Subgroup (Hl i))
    (hpc : ∀ i, Continuous (p i)) (hec : ∀ i, Continuous (e i))
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hKc : IsCompact (K : Set Γ))
    (hKo : ∀ i, IsOpen (KH i : Set (Hl i))) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)),
    ∃ V : ∀ i, Subgroup (Hl i), (∀ i, IsOpen (V i : Set (Hl i))) ∧ (∀ i, V i ≤ KH i) ∧
      (∀ᶠ i in cofinite, V i = KH i) ∧ ∀ u, (∀ i, p i u ∈ V i) → u ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open | exact GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open | (intros; apply GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open <;> assumption)
