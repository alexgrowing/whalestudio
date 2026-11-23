import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryFixesOrthogonalComplement
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocAdMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_unitary_fixes_orthogonal_complement : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsHermND σ J → ∀ {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    (x : GLoc σ J v) (W : Submodule (Fv F v) (Fin n → Fv F v)), (∀ z, ((splitHom σ J τ x).1 - 1) *ᵥ z ∈ W) →
    ∀ (u : Fin n → Fv F v), (∀ w ∈ W, u ⬝ᵥ (J.map τ *ᵥ w) = 0) → (splitHom σ J (τ.comp σ) x).1 *ᵥ u = u := by
  first | exact @GlobalTheory.ConjFix.conj_fix | exact GlobalTheory.ConjFix.conj_fix | (intros; apply GlobalTheory.ConjFix.conj_fix <;> assumption)
