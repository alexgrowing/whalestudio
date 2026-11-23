import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationPStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem le_iSup_of_pre_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  intro A _ g L u hA U K W h x hx
  obtain ⟨-, -, -, -, hinf, hmono, hsup, -, -, -, hbasic, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
  have hV' : IsAffineOpen V := hV
  let p : Ideal Γ(A.left, V) :=
    (IsLocalRing.maximalIdeal (A.left.presheaf.stalk x)).comap (A.left.presheaf.germ V x hxV).hom
  have hp : p ≠ ⊤ := Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp
  obtain ⟨z, hzV, hz⟩ := GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA V hV' m hm
  obtain ⟨i, hi⟩ := h z (hmono U V hVU hzV)
  have hzi : z ∈ pre u.ex (W i ⊓ V) := by rw [hinf]; exact ⟨hi, hzV⟩
  have hle : W i ⊓ V ≤ ⨆ b : {b : Γ(A.left, V) // A.left.basicOpen b ≤ W i}, A.left.basicOpen b.1 := by
    intro y hy
    obtain ⟨f, hf, hyf⟩ := hV'.exists_basicOpen_le (V := W i) ⟨y, hy.1⟩ hy.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨⟨b, hb⟩, hzb⟩ := (hsup _ _ z).mp (hmono _ _ hle hzi)
  have hbm : b ∉ m := fun hh ↦ (hbasic V b z).mp hzb ((hz b).mp hh)
  have hxb : x ∈ A.left.basicOpen b := by
    rw [Scheme.mem_basicOpen _ b x hxV]
    by_contra hn
    exact hbm (hpm (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn)))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hb hxb⟩

end GlobalTheory.CechPer
