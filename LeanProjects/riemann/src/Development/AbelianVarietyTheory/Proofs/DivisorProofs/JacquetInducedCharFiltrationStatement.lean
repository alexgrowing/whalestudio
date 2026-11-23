import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetInducedCharFiltration
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_induced_char_filtration : GlobalTheory.Published.GeometricLemmaFiltration → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (b : Fin 2 → ℕ) (hb : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ),
    (∀ j, IsSmoothChar (χ j)) → ∀ (l d : ℕ) (hld : l + d ≤ N) (Vy : Type) [AddCommGroup Vy] [Module ℂ Vy]
    (Y : Representation ℂ (GL (Fin d) k) Vy) (W' : Type) [AddCommGroup W'] [Module ℂ W']
    (Q : Representation ℂ (GL (Fin d) k) W'),
    IsSubquotient Q ((jacU (tripPlace hld) (pairInd k b hb χ)).comp (midHom k l d N)) →
    ∀ f : Q.IntertwiningMap Y, f ≠ 0 →
    ∃ (x x' c c' : ℕ) (h : x + x' = d) (s₁ s₂ : ℝ), c + c' = l ∧
      s₁ - s₂ = (c : ℝ) - c' + ((x : ℝ) - x') / 2 - ((b 0 : ℝ) - b 1) / 2 ∧
      ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (Q' : Representation ℂ (GL (Fin (x + x')) k) V'),
        IsSubquotient Q' (prod₂ (detRep (Fin x) (χ 0 * absPow k (s₁ : ℂ))) (detRep (Fin x') (χ 1 * absPow k (s₂ : ℂ)))) ∧
        ∃ f' : Q'.IntertwiningMap (Y.comp (glCast h)), f' ≠ 0 := by
  first | exact @GlobalTheory.MidBlockCell.exists_map_of_midBlock | exact GlobalTheory.MidBlockCell.exists_map_of_midBlock | (intros; apply GlobalTheory.MidBlockCell.exists_map_of_midBlock <;> assumption)
