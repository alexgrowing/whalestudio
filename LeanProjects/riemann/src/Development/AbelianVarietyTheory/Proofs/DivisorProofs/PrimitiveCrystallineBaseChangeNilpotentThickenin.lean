import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactLarge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem primCris_isBC_of_nilThick : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  intro A₀ _ g hA _ D _ _ π κ hκ hπ k
  haveI : Smooth A₀.hom := hA.smooth
  haveI : IsProper A₀.hom := hA.proper
  let P : Over (Sp ℂ) := A₀ ⊗ A₀
  haveI : Smooth P.hom := smooth_tensorObj_hom A₀ A₀
  haveI : IsProper P.hom := by
    change IsProper (A₀ ⊗ A₀).hom
    rw [Over.tensorObj_hom]; infer_instance
  have m2 : IsMor (dp0 ℂ) (P.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) (𝟙 P.left) :=
    ⟨k.dp, by rw [Category.assoc, ← k.base]; simp⟩
  have key : ∀ (f : P ⟶ A₀) (x : FirstDeRham (A₀.hom ≫ 𝟙 _)),
      pullOver κ (spMap π) f (k.isMor.pull1 x) = m2.pull1 (pullOver (dp0 ℂ) (𝟙 _) f x) := by
    intro f x
    have h'' : IsMor (dp0 ℂ) (A₀.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) f.left :=
      ⟨k.dp, by rw [← Category.assoc, Over.w f, Category.assoc, ← k.base]; simp⟩
    exact (IsMor.pullback1_comp k.isMor
        (IsMor.of_over κ (φ := f.left) (by rw [← Category.assoc, Over.w])) h'' (fun _ ↦ rfl)
        (by simp) x).trans
      (IsMor.pullback1_comp (IsMor.of_over (dp0 ℂ) (φ := f.left) (by rw [← Category.assoc, Over.w]))
        m2 h'' (fun _ ↦ rfl) (by simp) x).symm
  have hM : Function.Bijective (liftSemi k.isMor.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ A₀.left (A₀.hom ≫ 𝟙 _) (A₀.hom ≫ spMap π) (Over.Hom.left (𝟙 A₀))
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) (by simp) k.isMor
  have hN : Function.Bijective (liftSemi m2.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ P.left (P.hom ≫ 𝟙 _) (P.hom ≫ spMap π) (𝟙 P.left)
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) rfl m2
  have hZ : Function.Bijective (liftSemi k.pull) := by
    refine GlobalTheory.FlatKerLarge.liftSemi_bijective_of_exact_large ℂ D _ _ _ _ _ _ (prim (dp0 ℂ) (𝟙 _) A₀).subtype
      (pullOver (dp0 ℂ) (𝟙 _) μ[A₀] - pullOver (dp0 ℂ) (𝟙 _) (fst A₀ A₀) - pullOver (dp0 ℂ) (𝟙 _) (snd A₀ A₀))
      (prim κ (spMap π) A₀).subtype
      (pullOver κ (spMap π) μ[A₀] - pullOver κ (spMap π) (fst A₀ A₀) - pullOver κ (spMap π) (snd A₀ A₀))
      k.pull k.isMor.pull1 m2.pull1 (Submodule.injective_subtype _) ?_ (Submodule.injective_subtype _) ?_
      (fun _ ↦ rfl) ?_ hM hN.1
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro x
      simp only [LinearMap.sub_apply, map_sub, key]
  refine ⟨hZ, eq_top_iff.2 fun y _ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hZ.2 y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)

end GlobalTheory
