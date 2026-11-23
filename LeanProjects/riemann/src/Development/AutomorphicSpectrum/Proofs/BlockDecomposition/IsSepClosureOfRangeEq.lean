import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

theorem GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [Algebra F (Om l)] (K : FinExt l),
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) → IsSepClosure F (Om l) := by
  intro l _ F _ _ K hK
  have hmem : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Om l) q ∈ (algebraMap F (Om l)).fieldRange := by
    intro q
    have h : algebraMap ℚ_[l] (Om l) q ∈ Set.range (algebraMap F (Om l)) := by
      rw [hK]
      exact K.1.algebraMap_mem q
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  let e := (algebraMap F (Om l)).rangeRestrictFieldEquiv
  let φ : ℚ_[l] →+* F :=
    e.symm.toRingHom.comp ((algebraMap ℚ_[l] (Om l)).codRestrict (algebraMap F (Om l)).fieldRange hmem)
  have hφ : ∀ q, algebraMap F (Om l) (φ q) = algebraMap ℚ_[l] (Om l) q := by
    intro q
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨algebraMap ℚ_[l] (Om l) q, hmem q⟩)
    exact h
  have hcomp : (algebraMap F (Om l)).comp φ = algebraMap ℚ_[l] (Om l) := RingHom.ext hφ
  haveI : CharZero F := (algebraMap F (Om l)).charZero
  haveI halg : Algebra.IsAlgebraic F (Om l) := by
    constructor
    intro x
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact hpx
  exact IsSepClosure.mk inferInstance (Algebra.IsAlgebraic.isSeparable_of_perfectField)
