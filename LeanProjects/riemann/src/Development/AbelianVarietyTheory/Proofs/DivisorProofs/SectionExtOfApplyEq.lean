import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainFibFinite
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel

theorem section_ext_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (h : X ⟶ Sp k) {f g : Sp k ⟶ X}
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (pt : Sp k) (e : f pt = g pt) : f = g := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective f
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hf hg e ⊢
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
    Scheme.fromSpecResidueField_apply] at e
  subst e
  set ρ := Spec.preimage (X.fromSpecResidueField x ≫ h) with hρ
  have hr : X.fromSpecResidueField x ≫ h = Spec.map ρ := (Spec.map_preimage _).symm
  rw [Category.assoc, hr, ← Spec.map_comp, ← Spec.map_id] at hf hg
  have hφ := Spec.map_injective hf
  have hψ := Spec.map_injective hg
  suffices hfg : φ = ψ by rw [hfg]
  ext u
  have h1 : ∀ t : k, φ.hom (ρ.hom t) = t := fun t => by
    have := congrArg (fun m => m.hom t) hφ
    simpa using this
  have h2 : ∀ t : k, ψ.hom (ρ.hom t) = t := fun t => by
    have := congrArg (fun m => m.hom t) hψ
    simpa using this
  have hu : ρ.hom (φ.hom u) = u := φ.hom.injective (h1 _)
  rw [← hu, h2, h1]

theorem finite_points_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B) (d : ℕ),
    IsIsogDeg π d → Set.Finite {a : 𝟙_ (Over (Sp k)) ⟶ A | a ≫ π = 1} := by
  intro k _ A B _ π d hπ
  have := hπ.fin
  let pt : Sp k := IsLocalRing.closedPoint k
  have hF := π.left.finite_preimage_singleton ((1 : 𝟙_ (Over (Sp k)) ⟶ B).left pt)
  refine Set.Finite.of_finite_image (f := fun a => a.left pt) (hF.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    change π.left (a.left pt) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, show a ≫ π = 1 from ha]
  · intro a _ b _ hab
    exact Over.OverMorphism.ext (section_ext_of_apply_eq A.hom (Over.w a) (Over.w b) pt hab)

end GlobalTheory.IwLevel
