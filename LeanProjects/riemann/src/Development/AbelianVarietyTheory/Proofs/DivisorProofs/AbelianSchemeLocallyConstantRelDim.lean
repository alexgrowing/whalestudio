import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem abelianScheme_locally_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S,
    ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  intro S A _ hA s
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have hsec : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  have he : ∀ t : S, A.hom (η[A].left t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  have fib : ∀ x, n x = n (η[A].left (A.hom x)) := fun x => by
    have hconn : _root_.IsPreconnected (A.hom ⁻¹' {A.hom x}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact isPreconnected_univ.image _ (A.hom.fiberι _).continuous.continuousOn
    exact hc.apply_eq_of_isPreconnected hconn rfl (he (A.hom x))
  let x₀ : A.left := η[A].left s
  let U : S.Opens := η[A].left ⁻¹ᵁ W x₀
  have hsU : s ∈ U := hW x₀
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  refine ⟨V, n x₀, hV, hsV, ?_⟩
  have dimy : ∀ y, n (pullback.fst A.hom V.ι y) = n x₀ := fun y => by
    have h1 : A.hom (pullback.fst A.hom V.ι y) ∈ V := by
      have := congrArg (fun g => g y) (pullback.condition (f := A.hom) (g := V.ι))
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact (pullback.snd A.hom V.ι y).2
    rw [fib, loc _ _ (hVU h1)]
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀))
    (fun y => pullback.fst A.hom V.ι ⁻¹ᵁ W (pullback.fst A.hom V.ι y))
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW _⟩) fun y => ?_
  rw [← dimy y]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    ((isPullback_morphismRestrict (pullback.fst A.hom V.ι) (W _)).paste_vert (IsPullback.of_hasPullback _ _))
    (hd (pullback.fst A.hom V.ι y))

end GlobalTheory.DualCon
