import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem schemeFil_comp_iso (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (σ : A₀ ⟶ B₀) [IsMonHom σ] [IsIso σ] (X : Over (Sp R)) (j : B₀.left ⟶ X.left)
    (wj : j ≫ X.hom = B₀.hom ≫ spMap π) (w : (σ.left ≫ j) ≫ X.hom = A₀.hom ≫ spMap π) (d : Crys κ (spMap π) A₀) :
    d ∈ schemeFil κ A₀ X (σ.left ≫ j) w ↔ push κ (spMap π) σ d ∈ schemeFil κ B₀ X j wj := by
  haveI : IsMonHom (inv σ) :=
    { one_hom := by rw [← cancel_mono σ]; simp
      mul_hom := by
        rw [← cancel_mono σ]
        simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, IsIso.inv_hom_id] }

  have mK : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (RingHom.id R) (σ.left ≫ j) :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := A₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := σ.left ≫ j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, w])
  have mJ : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (B₀.hom ≫ spMap π) (RingHom.id R) j :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := B₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, wj])
  have key : ∀ a, (homMor κ (spMap π) σ).isMor.pull1 (mJ.pull1 a) = mK.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) rfl a
  have key' : ∀ a, (homMor κ (spMap π) (inv σ)).isMor.pull1 (mK.pull1 a) = mJ.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) (by rw [← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.id_comp]) a
  have back : ∀ c : prim κ (spMap π) A₀, primPull κ (spMap π) σ (primPull κ (spMap π) (inv σ) c) = c := fun c ↦ by
    refine Subtype.ext ?_
    change (homMor κ (spMap π) σ).isMor.pull1 ((homMor κ (spMap π) (inv σ)).isMor.pull1 c.1) = c.1
    rw [IsMor.pullback1_comp _ _ (IsMor.id κ (A₀.hom ≫ spMap π)) (fun _ ↦ rfl)
      (by rw [← Over.comp_left, IsIso.hom_inv_id, Over.id_left])]
    exact IsMor.pullCohomologyOne_id _ _
  simp only [schemeFil, primitiveCrystalHodgeLiftClasses, Submodule.mem_dualAnnihilator, Submodule.mem_comap, Submodule.mem_map,
    Submodule.subtype_apply, push_apply]
  constructor
  · rintro H c ⟨a, ha, e⟩
    refine H _ ⟨a, ha, ?_⟩
    change mK.pull1 a = _
    rw [← key, e]; rfl
  · rintro H c ⟨a, ha, e⟩
    have := H (primPull κ (spMap π) (inv σ) c) ⟨a, ha, ?_⟩
    · rwa [back] at this
    · change mJ.pull1 a = (homMor κ (spMap π) (inv σ)).isMor.pull1 c.1
      rw [← key', e]

end GlobalTheory.SqLift
