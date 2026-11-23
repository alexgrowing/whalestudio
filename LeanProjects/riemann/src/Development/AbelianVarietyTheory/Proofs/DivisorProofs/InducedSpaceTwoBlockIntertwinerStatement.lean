import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedSpaceTwoBlockIntertwiner
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_space_two_block_intertwiner : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m n : ℕ) (ν χ : kˣ →* ℂˣ), IsSmoothChar χ → ∀ (ε : Bool) (C : GL (Fin (m + n)) k),
    ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = m + n) (χ' : Fin 2 → kˣ →* ℂˣ)
      (T : GlobalTheory.FullRankCoinv.indSp k n (m + n) ν →ₗ[ℂ] IndSp (pairPlace b hb) (ofChar (pairChar k b χ'))),
      ((b 0 = m ∧ b 1 = n ∧ χ' 0 = χ ∧ χ' 1 = χ * ν⁻¹) ∨ (b 0 = n ∧ b 1 = m ∧ χ' 0 = (χ * ν⁻¹)⁻¹ ∧ χ' 1 = χ⁻¹)) ∧
      Function.Bijective T ∧
      ∀ (f : GL (Fin (m + n)) k → ℂ) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n (m + n) ν) (g M : GL (Fin (m + n)) k),
        M.1 = C.1 * (if ε then ((g⁻¹ : GL (Fin (m + n)) k).1)ᵀ else g.1) * (C⁻¹ : GL (Fin (m + n)) k).1 →
        ∀ hf' : (fun x => ((χ (GlobalTheory.SplitFlip.gdet M) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet M) ((n : ℂ) / 2)) *
            f (x * M)) ∈ GlobalTheory.FullRankCoinv.indSp k n (m + n) ν,
          T ⟨_, hf'⟩ = pairInd k b hb χ' g (T ⟨f, hf⟩) := by
  first | exact @GlobalTheory.FibreIdent.exists_ident | exact GlobalTheory.FibreIdent.exists_ident | (intros; apply GlobalTheory.FibreIdent.exists_ident <;> assumption)
