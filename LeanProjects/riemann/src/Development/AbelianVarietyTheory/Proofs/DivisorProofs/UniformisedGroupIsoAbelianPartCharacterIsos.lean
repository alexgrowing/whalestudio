import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.TInj

theorem torusHomOf_comp' {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem torusHomOf_id' {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem iso_lin_coord : ∀ (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂) (a : G₁ ≅ G₂), IsMonHom a.hom → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X ≃+ D₁.toPre.X), IsIso b ∧ Lin U₁ U₂ a.hom b h.toAddMonoidHom ∧ Coord U₁ U₂ a.hom b h.toAddMonoidHom := by
  intro R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ a ha
  have ha' : IsMonHom a.inv := inferInstance
  obtain ⟨b, hb, hbO⟩ := exists_abelian_hom R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨b', hb', hb'O⟩ := exists_abelian_hom R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  obtain ⟨h, hh⟩ := unifPre_hom_character_const R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨h', hh'⟩ := unifPre_hom_character_const R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  have oComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) c c',
      Over₀ Ua Ub f c → Over₀ Ub Ua g c' → Over₀ Ua Ua (f ≫ g) (c ≫ c') := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g c c' hf hg e
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg e, ← Category.assoc, hf e, Category.assoc]
  have tComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) k k',
      OnTorus Ua Ub f k → OnTorus Ub Ua g k' → OnTorus Ua Ua (f ≫ g) (fun χ => k (k' χ)) := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g k k' hf hg e
    obtain ⟨t, ht, hi⟩ := hf e
    obtain ⟨s, hs, hj⟩ := hg e
    refine ⟨t ≫ s, torusHomOf_comp' ht hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]
  have oId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), Over₀ Ua Ua (𝟙 Ga) (𝟙 _) := by
    intro Da Aa Ga _ _ Ua e
    simp
  have tId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), OnTorus Ua Ua (𝟙 Ga) (fun χ => χ) := by
    intro Da Aa Ga _ _ Ua e
    exact ⟨𝟙 _, torusHomOf_id' _, by simp⟩
  have u₁ := over₀_onTorus_unique R J hR D₁ D₁ A₁ A₁ G₁ G₁ U₁ U₁ (𝟙 G₁)
  have u₂ := over₀_onTorus_unique R J hR D₂ D₂ A₂ A₂ G₂ G₂ U₂ U₂ (𝟙 G₂)
  have bb : b ≫ b' = 𝟙 _ := u₁.1 _ _ (a.hom_inv_id ▸ oComp U₁ U₂ a.hom a.inv b b' hbO hb'O) (oId U₁)
  have bb' : b' ≫ b = 𝟙 _ := u₂.1 _ _ (a.inv_hom_id ▸ oComp U₂ U₁ a.inv a.hom b' b hb'O hbO) (oId U₂)
  have hh₁ : (fun χ => h (h' χ)) = fun χ => χ :=
    u₁.2 _ _ (a.hom_inv_id ▸ tComp U₁ U₂ a.hom a.inv h h' hh hh') (tId U₁)
  have hh₂ : (fun χ => h' (h χ)) = fun χ => χ :=
    u₂.2 _ _ (a.inv_hom_id ▸ tComp U₂ U₁ a.inv a.hom h' h hh' hh) (tId U₂)
  let hE : D₂.toPre.X ≃+ D₁.toPre.X :=
    { toFun := h, invFun := h', left_inv := fun χ => congrFun hh₂ χ, right_inv := fun χ => congrFun hh₁ χ,
      map_add' := h.map_add }
  have hL : Lin U₁ U₂ a.hom b hE.toAddMonoidHom := ⟨ha, hb, hbO, hh⟩
  exact ⟨b, hE, ⟨b', bb, bb'⟩, hL, coord_of_lin R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom b _ hL⟩

end GlobalTheory.TInj
