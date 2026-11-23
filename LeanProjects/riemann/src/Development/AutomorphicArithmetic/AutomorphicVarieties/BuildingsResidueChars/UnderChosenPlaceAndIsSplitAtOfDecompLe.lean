import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω), (∀ v, (s.w v).under (𝓞 (Lp L)) = v) ∧ ∀ w : Plc L, Dec (F := Lp L) (s.A (w.under (𝓞 (Lp L)))) ≤ (W.resP L Ω).range → IsSplitAt w := by
  intro l _ L Ω _ _ _ _ _ _ s
  obtain ⟨_, _, _, _, w, A, hAw, hAv, _⟩ := s
  refine ⟨fun v => ?_, fun w' hw' => UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (hAv _) hw' w' rfl⟩
  have h1 := hAw v
  have h2 := hAv v
  apply HeightOneSpectrum.ext
  ext x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← h1 (algebraMap _ _ x), ← h2 x]
  have hx : ((algebraMap (𝓞 (Lp L)) (𝓞 L) x : 𝓞 L) : L) = algebraMap (Lp L) L (x : Lp L) := rfl
  rw [hx, ← IsScalarTower.algebraMap_apply]
