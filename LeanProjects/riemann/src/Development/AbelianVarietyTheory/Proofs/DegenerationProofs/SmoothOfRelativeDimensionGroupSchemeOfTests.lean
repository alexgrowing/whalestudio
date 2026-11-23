import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOpensEtaleOfUniqueClassicalPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoordReducedFibreClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtAffineSpaceHomOfVectorOfCoordStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsDominantHomOfVectorOfQuasiFiniteAtStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointEqOfReductionCoordsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_fin (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_affineSpace_fin (S : Scheme.{0}) (n : ℕ) :
    SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
    (isStandardSmoothOfRelativeDimension_mvPolynomial_fin (ULift ℤ) n)

namespace ZJ

theorem Core.exists_opens_smoothOfRelativeDimension (C : Core) (hT : C.HasTests) (hF : C.Fib)
    (w : C.G.toScheme) (hc : IsClosed ({w} : Set C.G.toScheme)) :
    ∃ V : C.G.toScheme.Opens, w ∈ V ∧ SmoothOfRelativeDimension C.g (V.ι ≫ C.GG.hom) := by
  obtain ⟨hsep, hlft, -, hint, -, -, ha, hcart, -, -, -, hdom, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  obtain ⟨W, hw, u, -, hu⟩ := GlobalTheory.T.exists_coord_reducedFibre_closedPoint C hT hF w hc
  have hqf := GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord C w W hw u hc hu
  have huniq := GlobalTheory.T.classical_point_eq_of_reduction_coords C hT hF w W hw u hu
  have hint' : IsIntegral C.G.toScheme := hint
  have : Nonempty W.toScheme := ⟨⟨w, hw⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let t : W.toScheme ⟶ C.Z := W.ι ≫ C.GG.hom
  let u' : Fin C.g → Γ(W.toScheme, ⊤) := fun i => W.topIso.inv.hom (u i)
  let v : W.toScheme ⟶ 𝔸(Fin C.g; C.Z) := AffineSpace.homOfVector t u'
  have hv : v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z = t := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ C.GG.hom))
  have : IsSeparated t := inferInstanceAs (IsSeparated (W.ι ≫ C.GG.hom))
  have : IsDominant W.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact W.isOpen.dense ⟨w, hw⟩⟩
  have : IsDominant t := inferInstanceAs (IsDominant (W.ι ≫ C.GG.hom))
  have hA := smoothOfRelativeDimension_affineSpace_fin C.Z C.g
  have : Smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) := SmoothOfRelativeDimension.smooth C.g _
  have : LocallyOfFiniteType v := by
    have : LocallyOfFiniteType (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact locallyOfFiniteType_of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have : IsSeparated v := by
    have : IsSeparated (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact IsSeparated.of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  let U' : W.toScheme.Opens := t ⁻¹ᵁ C.U
  have hU' : (U' : Set W.toScheme).Nonempty := by
    obtain ⟨x, hx⟩ := t.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨x, hx⟩
  have hsm : SmoothOfRelativeDimension C.g (U'.ι ≫ t) := by
    let l : U'.toScheme ⟶ C.A.left := hcart.lift (U'.ι ≫ W.ι) (t ∣_ C.U)
      (by rw [morphismRestrict_ι, Category.assoc])
    have h1 : l ≫ C.a = U'.ι ≫ W.ι := hcart.lift_fst _ _ _
    have h2 : l ≫ C.A.hom = t ∣_ C.U := hcart.lift_snd _ _ _
    have : IsOpenImmersion (l ≫ C.a) := by rw [h1]; infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l C.a
    have h3 : U'.ι ≫ t = l ≫ C.A.hom ≫ C.U.ι := by
      rw [reassoc_of% h2, morphismRestrict_ι]
    have := C.dim
    have h4 : SmoothOfRelativeDimension (0 + (C.g + 0)) (l ≫ C.A.hom ≫ C.U.ι) := inferInstance
    rw [h3]
    simpa using h4
  have : IsDominant v := GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' W.toScheme C.Z t C.g U' hU' hsm u' ⟨w, hw⟩ hqf
  have := C.flat
  have := C.lft
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔸(Fin C.g; C.Z) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) C.normal
  have hc' : IsClosed ({⟨w, hw⟩} : Set W.toScheme) := by
    have := hc.preimage W.ι.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  obtain ⟨V, hV, hE⟩ := exists_opens_etale_of_unique_classical_points 𝔸(Fin C.g; C.Z)
    (𝔸(Fin C.g; C.Z) ↘ C.Z ≫ C.π) hN W.toScheme v ⟨w, hw⟩ U' hc' hqf hU' (by
      intro p _ a a' h hp hr hg _
      refine huniq p a a' ?_ ?_ hp hr fun i => ?_
      · rintro _ ⟨z, rfl⟩
        exact hg ⟨z, rfl⟩
      · change a ≫ t = a' ≫ t
        rw [← hv, reassoc_of% h]
      · have e : ∀ b : Sp (OO p) ⟶ W.toScheme,
            b.appTop.hom (u' i) = (b ≫ v).appTop.hom (AffineSpace.coord C.Z i) := fun b => by
          rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
          exact congrArg _ (AffineSpace.homOfVector_appTop_coord t u' i).symm
        exact (e a).trans ((congrArg (fun c : Sp (OO p) ⟶ 𝔸(Fin C.g; C.Z) =>
          c.appTop.hom (AffineSpace.coord C.Z i)) h).trans (e a').symm))
  have h5 : SmoothOfRelativeDimension (0 + C.g) ((V.ι ≫ v) ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) :=
    inferInstance
  rw [Category.assoc, hv, zero_add] at h5
  refine ⟨(V.ι ≫ W.ι).opensRange, ⟨⟨⟨w, hw⟩, hV⟩, rfl⟩, ?_⟩
  have h6 : SmoothOfRelativeDimension (0 + C.g)
      ((V.ι ≫ W.ι).isoOpensRange.inv ≫ V.ι ≫ t) := inferInstance
  rw [zero_add] at h6
  convert h6 using 1
  rw [← (V.ι ≫ W.ι).isoOpensRange_inv_comp]
  simp only [Category.assoc, t]

theorem Core.smoothOfRelativeDimension_of_hasTests :
    ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  intro C hT hF
  obtain ⟨-, hlft, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  choose V hV hs using C.exists_opens_smoothOfRelativeDimension hT hF
  let V' : {w : C.G.toScheme // IsClosed ({w} : Set C.G.toScheme)} → C.G.toScheme.Opens :=
    fun w => V w.1 w.2
  have htop : iSup V' = ⊤ :=
    (jacobson_closedPoints_tools_int C.G.toScheme (C.GG.hom ≫ C.π)).2.2.1 _ _ fun x hx =>
      ⟨fun _ => trivial, fun _ => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hV x hx⟩⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} C.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} C.g) V' htop
    fun w => hs w.1 w.2

end ZJ
end GlobalTheory
