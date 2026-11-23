import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitRatioGeneratorsIsomorphicLineBunStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameCob

theorem res_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl

theorem comm_group_step {G : Type*} [CommGroup G] (a b c d e f g k : G) (A : a * b = c * d) (B : b = e * f)
    (C : d = g * k) : e * a * g⁻¹ * f = c * k := by
  subst B C
  calc e * a * g⁻¹ * f = g⁻¹ * (a * (e * f)) := by ac_rfl
    _ = g⁻¹ * (c * (g * k)) := by rw [A]
    _ = c * k := by rw [mul_left_comm c, inv_mul_cancel_left]

theorem frames_cohomologous : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X)
    (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → L'.IsLB → LBIso L L' →
    IsFrame L V hV u → IsFrame L' V hV u' →
    ∃ t : ∀ T : C, Γ(X, V T)ˣ, ∀ T T' a, u' T T' a * res (hV a) (t T) = t T' * u T T' a := by
  intro X C _ V hV L L' u u' hL hL' ⟨w, hw⟩ ⟨τ, hτg, hτ⟩ ⟨τ', hτ'g, hτ'⟩
  choose t ht htu using fun T => GlobalTheory.T.existsUnique_unit_ratio_generators_isomorphic_lineBundles X L L' (V T) w (τ T) (τ' T) hL hL' hw (hτg T) (hτ'g T)
  refine ⟨t, fun T T' a => ?_⟩
  have key : u' T T' a * res (hV a) (t T) * (u T T' a)⁻¹ = t T' := by
    refine htu T' _ (fun m m' => ?_)
    have hO : V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T ⊓ (L'.U m' ⊓ L.U m) := inf_le_inf_right _ (hV a)
    have A := congrArg (res hO) (ht T m m')
    have B := congrArg (res (inf_le_inf_left (V T') inf_le_left :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L'.U m')) (hτ' T T' a m')
    have C' := congrArg (res (inf_le_inf_left (V T') inf_le_right :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L.U m)) (hτ T T' a m)
    simp only [map_mul, map_inv, res_comp] at A B C' ⊢
    erw [res_comp] at A
    exact comm_group_step _ _ _ _ _ _ _ _ A B C'
  rw [← key, inv_mul_cancel_right]

end GlobalTheory.FrameCob
