import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Sd UpperTheory.V.Sd.Eis

private theorem co_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem co_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]

theorem UpperTheory.V.Br.ctOne :
    UpperTheory.V.Br.CtOne := by
  intro F _ _
  obtain ⟨h1, h2, h3, h4, -, -, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock F
  letI iM : MeasurableSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := MeasurableSpace.pi
  have hμ : (unipMeasure F 2 1).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have hL : ratN F 2 1 = unipLattice F 2 1 := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hF : IsAddFundamentalDomain (ratN F 2 1) (unipFundamentalDomain F 2 1) (unipMeasure F 2 1) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have main : ∀ [MeasurableSpace (NA F)] [BorelSpace (NA F)] (ν : Measure (NA F)) [ν.IsAddHaarMeasure] (D₀ : Set (NA F)),
      IsAddFundamentalDomain (ratN F 2 1) D₀ ν → ∀ φ : GA F 2 → ℂ, (∀ γ g, φ (ratGL F 2 γ * g) = φ g) →
      (∀ g, cterm ν D₀ φ g = 0) → GlobalTheory.CuspRep.IsCuspidal φ := by
    intro j1 j2 ν _ D₀ hD₀ φ hl h0 r hr0 hr1 i1 i2 μ D hμ' hD g
    obtain rfl : r = 1 := by omega
    obtain rfl : i1 = j1 :=
      (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ j1 j2).symm
    have hper : ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * g) = φ (unip x * g) := by
      rintro _ ⟨y, rfl⟩ x
      rw [hx, hx x]
      refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
      rw [← mul_assoc, co_rat_aff, co_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
      rfl
    have hD' : IsAddFundamentalDomain (ratN F 2 1) D ν := hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
    have h : ∫ x in D, φ (unip x * g) ∂ν = 0 :=
      (hD'.setIntegral_eq hD₀ (f := fun x => φ (unip x * g)) fun γ x => hper γ γ.2 x).trans (h0 g)
    rw [Measure.isAddLeftInvariant_eq_smul μ ν, Measure.restrict_smul, integral_smul_nnreal_measure, h, smul_zero]
  exact ⟨iM, hB, unipMeasure F 2 1, hμ, unipFundamentalDomain F 2 1, hF, @main iM hB _ hμ _ hF⟩
