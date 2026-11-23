import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isSheaf_of_local_glue : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → Presieve.IsSheaf Scheme.zariskiTopology F := by
  intro F hext hglue
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  choose jj q hq using 𝒰.exists_eq
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨y₀, hy₀⟩ := hglue Y Y (fun p => 𝒰.X (jj p)) (fun p => 𝒰.f (jj p)) (fun p => x (jj p))
      (fun p => inferInstance) (fun p => ⟨p, q p, hq p⟩)
      (fun i k Z a b h => hx (jj i) (jj k) Z a b h)
    refine ⟨y₀, fun i => hext _ _ _ fun r => ?_⟩
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f i)
      (g := 𝒰.f (jj (𝒰.f i r))) r (q (𝒰.f i r)) (hq _).symm
    refine ⟨_, pullback.fst (𝒰.f i) (𝒰.f (jj (𝒰.f i r))), inferInstance, ⟨w, hw⟩, ?_⟩
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, pullback.condition, op_comp,
      FunctorToTypes.map_comp_apply, hy₀]
    exact (hx _ _ _ _ _ pullback.condition).symm
  · intro y y' h h'
    refine hext Y y y' fun p => ?_
    exact ⟨𝒰.X (jj p), 𝒰.f (jj p), inferInstance, ⟨q p, hq p⟩, (h _).trans (h' _).symm⟩

end GlobalTheory
