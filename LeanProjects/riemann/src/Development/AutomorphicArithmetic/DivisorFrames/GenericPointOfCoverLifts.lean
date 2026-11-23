import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.RootFrame

private theorem gen_factor {X G : Scheme.{0}} [IsIntegral X] [IsIntegral G] (j : G ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint G) ⤳ genericPoint X) :
    ∃ k : Spec X.functionField ⟶ Spec G.functionField,
      k ≫ G.fromSpecStalk (genericPoint G) ≫ j = X.fromSpecStalk (genericPoint X) := by
  let a : X.functionField ⟶ G.functionField := X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint G)
  have hs : Function.Surjective a := by
    intro u
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective _ u
    obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq b
    refine ⟨X.presheaf.germ U _ (hη.antisymm (genericPoint_specializes _) |>.eq ▸ hx) s, ?_⟩
    change j.stalkMap _ (X.presheaf.stalkSpecializes hη (X.presheaf.germ U _ _ s)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  have : IsIso a := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨a.hom.injective, hs⟩
  have e : Spec.map a ≫ X.fromSpecStalk (genericPoint X) = G.fromSpecStalk (genericPoint G) ≫ j := by
    simp only [a, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  refine ⟨inv (Spec.map a), ?_⟩
  rw [← e, IsIso.inv_hom_id_assoc]

theorem UpperTheory.generic_point_of_cover_lifts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ Z.X) (π : Y.X ⟶ gen Z), V.j ≫ ρ' = V.π ≫ π ≫ genι Z → π (genericPoint Y.X) ∈ Set.range Z.jQ → ∃ y₀ : Sp V.X.functionField ⟶ Xo.XF c, V.X.fromSpecStalk (genericPoint V.X) ≫ ρ' = y₀ ≫ Z.j := by
  intro E _ _ _ H Dw l Xo c Z F _ _ Y V ρ' π hρ hπ
  have hη : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
    have h : Flat (spMap (algebraMap (𝓞 F) F)) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).2
        (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors (𝓞 F))))
    have : Flat V.j := MorphismProperty.of_isPullback (P := @Flat) V.pb.flip h
    obtain ⟨y, -, hy⟩ := Flat.generalizingMap V.j (genericPoint_specializes (V.j (genericPoint V.G)))
    exact hy ▸ (genericPoint_specializes y).map V.j.continuous
  have hpre : IsPreimmersion V.j :=
    have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
    MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h
  have hg : V.π (genericPoint V.G) = genericPoint Y.X := by
    have h := (genericPoint_spec V.G).image V.π.continuous
    rw [Set.image_univ, V.π.surjective.range_eq, closure_univ] at h
    exact h.eq (genericPoint_spec Y.X)
  obtain ⟨k, hk⟩ := gen_factor V.j hη
  haveI := Z.jQ_open
  let q : Spec V.X.functionField ⟶ gen Z := k ≫ V.G.fromSpecStalk (genericPoint V.G) ≫ V.π ≫ π
  have hr : Set.range q ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have h1 : k p = IsLocalRing.closedPoint V.G.functionField :=
      Subsingleton.elim (α := PrimeSpectrum V.G.functionField) _ _
    have h2 : q p = π (genericPoint Y.X) := by
      change π (V.π (V.G.fromSpecStalk (genericPoint V.G) (k p))) = _
      rw [h1, Scheme.fromSpecStalk_closedPoint, hg]
    rw [h2]
    exact hπ
  refine ⟨IsOpenImmersion.lift Z.jQ q hr, ?_⟩
  have hy : IsOpenImmersion.lift Z.jQ q hr ≫ Z.jQ = q := IsOpenImmersion.lift_fac _ _ _
  have h3 : IsOpenImmersion.lift Z.jQ q hr ≫ Z.j = q ≫ genι Z :=
    (Category.assoc _ Z.jQ (genι Z)).symm.trans (congrArg (· ≫ genι Z) hy)
  refine Eq.trans ?_ h3.symm
  rw [← hk]
  simp only [q, Category.assoc, hρ]
