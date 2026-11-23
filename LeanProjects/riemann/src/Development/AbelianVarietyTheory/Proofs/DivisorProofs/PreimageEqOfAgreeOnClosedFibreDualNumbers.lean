import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

theorem preimage_eq_of_agree_closedFibre : ∀ (k : Type) [Field k] (X B : Scheme.{0}) (h : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X), (∀ (Z : Scheme.{0}) (x : Z ⟶ B) (y : Z ⟶ Sp k), x ≫ h = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ W : X.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := by
  intro k _ X B h π₁ π₂ hyp W
  have hpt : ∀ b : B, π₁ b = π₂ b := by
    intro b
    set x := B.fromSpecResidueField b
    set φ := Spec.preimage (x ≫ h)
    have hφ : Spec.map φ = x ≫ h := Spec.map_preimage _
    have hinr : ∀ c : k, φ.hom (TrivSqZeroExt.inr c) = 0 := by
      intro c
      have : φ.hom (TrivSqZeroExt.inr c) * φ.hom (TrivSqZeroExt.inr c) = 0 := by
        rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
      exact mul_self_eq_zero.mp this
    let ψ : k →+* B.residueField b := φ.hom.comp (TrivSqZeroExt.inlHom k k)
    have hψ : ψ.comp (TrivSqZeroExt.fstHom k k k).toRingHom = φ.hom := by
      refine RingHom.ext fun z => ?_
      conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      rw [map_add, hinr, add_zero]
      rfl
    have hx : x ≫ h = Spec.map (CommRingCat.ofHom ψ) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
      rw [← hφ, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      rfl
    have e := hyp _ x _ hx
    obtain ⟨s⟩ : Nonempty (Spec (B.residueField b)) := inferInstance
    have h1 : (x ≫ π₁) s = (x ≫ π₂) s := by rw [e]
    simpa [x] using h1
  apply TopologicalSpace.Opens.ext
  ext b
  change π₁ b ∈ W ↔ π₂ b ∈ W
  rw [hpt b]

end GlobalTheory.LogKS
