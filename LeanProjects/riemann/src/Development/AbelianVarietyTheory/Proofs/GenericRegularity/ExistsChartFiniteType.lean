import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

namespace GlobalTheory.ModelPoints

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem existsUnique_extension {W L : Type} [CommRing W] [IsDomain W] [ValuationRing W] [Field L] [Algebra W L]
    [IsFractionRing W L] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s] (y : Sp L ⟶ X) (r : Sp W ⟶ S)
    (h : y ≫ s = spMap (algebraMap W L) ≫ r) :
    ∃! x : Sp W ⟶ X, x ≫ s = r ∧ spMap (algebraMap W L) ≫ x = y := by
  have hP : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) s := by
    rw [← IsProper.eq_valuativeCriterion]
    exact ‹IsProper s›
  let S : ValuativeCommSq s := { R := W, K := L, i₁ := y, i₂ := r, commSq := ⟨h⟩ }
  obtain ⟨u⟩ := hP.1.1.1 S
  refine ⟨u.default.l, ⟨u.default.fac_right, u.default.fac_left⟩, ?_⟩
  rintro x ⟨hx₁, hx₂⟩
  exact congrArg CommSq.LiftStruct.l (u.uniq ⟨x, hx₂, hx₁⟩)

theorem existsUnique_chartHom {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (W : Type) [CommRing W]
    [IsLocalRing W] (yt : Sp W ⟶ X) (hy : yt (IsLocalRing.closedPoint W) ∈ U) :
    ∃! ψ : Γ(X, U) →+* W, spMap ψ ≫ hU.fromSpec = yt := by
  have hsub : Set.range yt ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := W) p).map yt.continuous).mem_open U.isOpen hy
  let g := IsOpenImmersion.lift hU.fromSpec yt hsub
  have hg : g ≫ hU.fromSpec = yt := IsOpenImmersion.lift_fac _ _ _
  refine ⟨(Spec.preimage g).hom, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom (Spec.preimage g).hom) ≫ hU.fromSpec = yt
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
  · intro ψ hψ
    have h₁ : Spec.map (CommRingCat.ofHom ψ) = g := by
      rw [← cancel_mono hU.fromSpec, hg]
      exact hψ
    have h₂ : CommRingCat.ofHom ψ = Spec.preimage g :=
      Spec.map_injective (h₁.trans (Spec.map_preimage g).symm)
    rw [← h₂]
    rfl

theorem exists_chart_finiteType {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : ∃ α : O →+* Γ(X, U), hU.fromSpec ≫ s = spMap α ∧ α.FiniteType := by
  refine ⟨(Spec.preimage (hU.fromSpec ≫ s)).hom, ?_, ?_⟩
  · show _ = Spec.map (CommRingCat.ofHom _)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  · have hlf : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ s))) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlf

theorem model_points_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W L : Type) [CommRing W] [IsDomain W] [ValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (oV : O →+* W) (fK : c.F →+* L) (y : Sp L ⟶ Xo.XF c), (algebraMap W L).comp oV = fK.comp β → y ≫ pullback.snd _ _ = spMap fK → ∃! yt : Sp W ⟶ Y.X, yt ≫ Y.s = spMap oV ∧ spMap (algebraMap W L) ≫ yt = y ≫ Y.j) ∧ (∀ (S : Scheme.{0}) (f : S ⟶ Y.X), ∃ G : SAB H S, Nonempty (SABMap G Y.t f)) ∧ ∀ (U : Y.X.Opens) (hU : IsAffineOpen U), ∃ α : O →+* Γ(Y.X, U), hU.fromSpec ≫ Y.s = spMap α ∧ α.FiniteType ∧ ∀ (W : Type) [CommRing W] [IsLocalRing W] (yt : Sp W ⟶ Y.X), yt (IsLocalRing.closedPoint W) ∈ U → ∃! ψ : Γ(Y.X, U) →+* W, spMap ψ ≫ hU.fromSpec = yt := by
  intro E _ _ _ H D l Xo c O _ β Y
  haveI : IsProper Y.s := projProper O Y.X Y.s Y.proj
  refine ⟨?_, ?_, ?_⟩
  · intro W L _ _ _ _ _ _ oV fK y hc hy
    apply existsUnique_extension Y.s (y ≫ Y.j) (spMap oV)
    rw [Category.assoc, Model.j_s, ← Category.assoc, hy, ← spMap_comp, ← spMap_comp, hc]
  · intro S f
    have hp := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull f Y.t
    exact ⟨_, ⟨hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩⟩
  · intro U hU
    obtain ⟨α, hα, hft⟩ := exists_chart_finiteType Y.s hU
    exact ⟨α, hα, hft, fun W _ _ yt hyt => existsUnique_chartHom hU W yt hyt⟩

end GlobalTheory.ModelPoints
