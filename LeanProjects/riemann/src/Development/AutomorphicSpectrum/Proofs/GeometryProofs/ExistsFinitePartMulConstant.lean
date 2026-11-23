import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.ProjectiveUnramifiedQuotient
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTopStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariantStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfDiv
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT.LateralTheory

theorem ringHom_ext_of_isFractionRing {V K L : Type} [CommRing V] [IsDomain V] [Field K] [Field L] [Algebra V K]
    [IsFractionRing V K] (φ ψ : L →+* K) (θ : V →+* L) (h₁ : φ.comp θ = algebraMap V K)
    (h₂ : ψ.comp θ = algebraMap V K) : φ = ψ := by
  have e₁ : ∀ v, φ (θ v) = algebraMap V K v := fun v => RingHom.congr_fun h₁ v
  have e₂ : ∀ v, ψ (θ v) = algebraMap V K v := fun v => RingHom.congr_fun h₂ v
  ext c
  obtain ⟨v, w, hw0, hc⟩ := IsFractionRing.div_surjective (A := V) (φ c)
  have hw : algebraMap V K w ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hw0
  have hθ : θ w * c = θ v := φ.injective (by
    rw [map_mul, e₁, e₁, ← hc]
    field_simp)
  have h3 := congrArg ψ hθ
  rw [map_mul, e₂, e₂] at h3
  rw [← hc, div_eq_iff hw, ← h3, mul_comm]

theorem point_ext {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of V))
    (f g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hf : f ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    (hg : g ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    (x y : Spec (CommRingCat.of (FractionRing V))) (h : f x = g y) : f = g := by
  obtain ⟨⟨z, φ⟩, hz⟩ := (Scheme.SpecToEquivOfField (FractionRing V) X).symm.surjective f
  obtain ⟨⟨w, ψ⟩, hw⟩ := (Scheme.SpecToEquivOfField (FractionRing V) X).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz hw
  have hzw : z = w := by
    have h1 : f x ∈ Set.range (X.fromSpecResidueField z) := by
      rw [← hz]; exact ⟨_, rfl⟩
    have h2 : g y ∈ Set.range (X.fromSpecResidueField w) := by
      rw [← hw]; exact ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at h1 h2
    rw [h] at h1
    exact h1.symm.trans h2
  subst hzw
  let θ : CommRingCat.of V ⟶ X.residueField z := Spec.preimage (X.fromSpecResidueField z ≫ π)
  have hθ : Spec.map θ = X.fromSpecResidueField z ≫ π := Spec.map_preimage _
  have h₁ : θ ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, ← Category.assoc, hz, hf]
  have h₂ : θ ≫ ψ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, ← Category.assoc, hw, hg]
  have hφψ : φ = ψ := by
    apply CommRingCat.hom_ext
    exact ringHom_ext_of_isFractionRing (V := V) φ.hom ψ.hom θ.hom
      (congrArg CommRingCat.Hom.hom h₁) (congrArg CommRingCat.Hom.hom h₂)
  rw [← hz, ← hw, hφψ]

variable {V : Type} [CommRing V] [IsDomain V] {T : Type} [CommGroup T]

theorem toUnit_genPt_left : (toUnit (genPt V)).left =
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
  simpa using Over.w (toUnit (genPt V))

theorem section_ext (Γ : QFGroup V T) (σ τ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Γ.G)
    (h : toUnit (genPt V) ≫ σ = toUnit (genPt V) ≫ τ) : σ = τ := by
  haveI := Γ.separated
  haveI hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap V (FractionRing V)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))]
      exact bot_le)⟩
  have h' := congrArg Over.Hom.left h
  simp only [Over.comp_left, toUnit_genPt_left] at h'
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of V)) Γ.G.hom
    ((Over.w σ).trans (Over.w τ).symm)
    (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h')

theorem exists_pt_of_section (Γ : QFGroup V T) (σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Γ.G) :
    ∃ t, toUnit (genPt V) ≫ σ = Γ.pt t := by
  let c := toUnit (genPt V) ≫ σ
  let x₀ : Spec (CommRingCat.of (FractionRing V)) := default
  have hover : ∀ c' : genPt V ⟶ Γ.G, c'.left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := fun c' => Over.w c'
  have hgen : (Γ.G.hom (c.left x₀)).asIdeal = ⊥ := by
    have e : Γ.G.hom (c.left x₀) =
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) x₀ := by
      rw [← hover c]; rfl
    have hx₀ : x₀.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top x₀.asIdeal).resolve_right x₀.isPrime.ne_top
    rw [e]
    change Ideal.comap (algebraMap V (FractionRing V)) x₀.asIdeal = ⊥
    rw [hx₀]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hgen
  refine ⟨t, Over.OverMorphism.ext ?_⟩
  exact point_ext Γ.G.hom _ _ (hover _) (hover _) x₀ x hx.symm

end GlobalTheory.CompanionTheory.Ar.BT.LateralTheory
