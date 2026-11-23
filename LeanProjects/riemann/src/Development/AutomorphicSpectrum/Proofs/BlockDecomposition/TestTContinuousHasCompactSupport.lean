import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC

variable {F : Type} [Field F] [NumberField F]

def boxW (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v) :=
  {x | (v ∈ S → x ∈ U v) ∧ (v ∉ S → x ∈ v.adicCompletionIntegers F)}

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_integer _

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  exact isCompact_iff_compactSpace.2 inferInstance

theorem isOpen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsOpen (U v)) :
    IsOpen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  have h1 : IsOpen {y : Af F | ∀ v ∈ S, y v ∈ U v} := by
    have : {y : Af F | ∀ v ∈ S, y v ∈ U v} = ⋂ v ∈ S, (fun y : Af F => y v) ⁻¹' U v := by
      ext y; simp
    rw [this]
    exact isOpen_biInter_finset fun v _ => (hU v).preimage (RestrictedProduct.continuous_eval v)
  have h2 : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => isOpen_integers v)
  exact h1.inter h2

theorem isCompact_boxW (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v))
    (v : HeightOneSpectrum (𝓞 F)) : IsCompact (boxW S U v) := by
  by_cases hv : v ∈ S
  · have : boxW S U v = U v := by
      ext x; simp [boxW, hv]
    rw [this]; exact hU v
  · have : boxW S U v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [boxW, hv]
    rw [this]; exact isCompact_integers v

theorem isCompact_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v)) :
    IsCompact (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  haveI : ∀ v, CompactSpace (boxW S U v) := fun v => isCompact_iff_compactSpace.1 (isCompact_boxW S U hU v)
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal ((S : Set _)ᶜ) :=
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let gP : (∀ v, boxW S U v) → RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
      (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal ((S : Set _)ᶜ)) :=
    fun x => ⟨fun v => (x v).1, Filter.eventually_principal.2 fun v hv => (x v).2.2 (by simpa using hv)⟩
  have hgP : Continuous gP :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff.2
      (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v))
  let g : (∀ v, boxW S U v) → Af F := fun x => RestrictedProduct.inclusion _ _ hle (gP x)
  have hg : Continuous g := (RestrictedProduct.continuous_inclusion hle).comp hgP
  have hr : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U = Set.range g := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v => ⟨y v, fun hv => h1 v hv, fun hv => h2 v hv⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨fun v hv => (x v).2.1 hv, fun v hv => (x v).2.2 hv⟩
  rw [hr]
  exact isCompact_range hg

theorem isClopen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v) ∧ IsOpen (U v)) :
    IsClopen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) :=
  ⟨(isCompact_boxA S U fun v => (hU v).1).isClosed, isOpen_boxA S U fun v => (hU v).2⟩

theorem testT_continuous_hasCompactSupport : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)),
    Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) →
    Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧
      HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  intro F _ _ ρ S U hρ hρc hU
  have hB := isClopen_boxA S U hU
  have hBc := isCompact_boxA S U fun v => (hU v).1
  have hfst : Continuous (fun y : AF F => fstA F y) := continuous_fst
  have hsnd : Continuous (fun y : AF F => sndA F y) := continuous_snd
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    refine (Complex.continuous_ofReal.comp (hρ.comp hfst)).mul ?_
    exact (IsClopen.continuous_indicator hB continuous_const).comp hsnd
  · have hK : IsCompact ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F)) :=
      hρc.isCompact.prod hBc
    refine HasCompactSupport.intro (K := ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F))) hK ?_
    intro y hy
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    by_cases h1 : sndA F y ∈ GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U
    · have h2 : ρ (fstA F y) = 0 := by
        by_contra h3
        exact hy ⟨subset_tsupport ρ h3, h1⟩
      simp [h2]
    · simp [Set.indicator_of_notMem h1]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC
