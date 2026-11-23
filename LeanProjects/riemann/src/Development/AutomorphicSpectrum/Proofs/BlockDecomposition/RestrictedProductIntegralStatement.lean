import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductIntegral
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictedProductQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHeckeSumStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_integral : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH V : ∀ i, Subgroup (Hl i))
    (f : ∀ i, Hl i → ℂ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hev : ∀ x, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hVe : ∀ᶠ i in cofinite, V i = KH i ∧ f i = (KH i : Set (Hl i)).indicator 1)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x)
    (l : List ι) (hl : l.Nodup)
    (hfix : ∀ i, i ∉ l → (fun x => hint (KH i) fun m => f i m * g (x * e i m)) = g),
    hint K (fun x => (∏ᶠ i, f i (p i x)) * g x) =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g 1 := by
  first | exact @GlobalTheory.CompanionTheory.FinActCore.hint_prod_eq_foldr | exact GlobalTheory.CompanionTheory.FinActCore.hint_prod_eq_foldr | (intros; apply GlobalTheory.CompanionTheory.FinActCore.hint_prod_eq_foldr <;> assumption)
