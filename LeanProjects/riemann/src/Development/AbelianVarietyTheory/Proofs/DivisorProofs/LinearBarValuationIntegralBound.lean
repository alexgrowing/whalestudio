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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumValueNeZeroOfLinearFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterLocalFunctionalEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVacuumFixedByMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactElementOfUnitDeterminantStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

theorem GlobalTheory.WRightUnram.scalar_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ h ∈ UAt σ G.W (evFin F B.v₁),
      (∀ i j, ValuativeRel.valuation (Fv F B.v₁) ((mat h).map (piW B.τ₁) i j) ≤ 1) →
      ValuativeRel.valuation (Fv F B.v₁) ((mat h).map (piW B.τ₁)).det = 1 → ∀ c : ℂ,
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ → ι φ₁ = c • fun Y => ι φ (Y * (mat h).map (piW B.τ₁))) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT ι hι h hh _hint hdet c hc
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_character_local_functional_equivariant hP F E σ B a a' G X om om' hT ι hι
  have hu : ValuativeRel.valuation (Fv F B.v₁)
      ((Matrix.GeneralLinearGroup.det (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h) : (Fv F B.v₁)ˣ) : Fv F B.v₁) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val]; exact hdet
  obtain ⟨k, hk, hkdet⟩ := GlobalTheory.T.exists_compact_element_of_unit_determinant hP F E σ B a a' G X om om' hT _ hu
  obtain ⟨⟨ck, hck⟩, hkχ⟩ := hχ k hk.1
  have hvSB := (hT.geo.hM'.vac B.v₁).1
  have e0 := congrFun (hck _ hvSB _ hvSB (GlobalTheory.T.spherical_vacuum_fixed_by_maximal_compact hP F E σ B a a' G X om om' hT k hk)) 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.zero_mul] at e0
  have h0 := GlobalTheory.T.vacuum_value_ne_zero_of_linear_functional hP F E σ B a a' G X om om' hT ι hι
  have hck1 : ck = 1 := by
    have : (ck - 1) * ι (G.M'.vac B.v₁) 0 = 0 := by linear_combination -e0
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
  rw [(hχ h hh).2 c hc, ← hkdet, ← hkχ ck hck, hck1]
