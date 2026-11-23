import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {X : Scheme.{0}}

def valHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valHom x U h f = valAt' x U f := by
  rw [valAt', dif_pos h]; rfl

theorem specMap_valHom_fromSpec (x : Sp ℂ ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    spMap (valHom x U h) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp ℂ)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : CommRingCat.ofHom (valHom x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := rfl
  rw [spMap, e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem exists_pt_of_affine : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) (W : Opens (Tot I g)), (∀ p ∈ W, p.1 ∈ F.V) → ∀ U : X.Opens, IsAffineOpen U → (∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p := by
  intro I _ g Λ _ F B _ X s σ u W hW U hU hWU
  have han : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p ↦ valAt' (u.E p) U f) W := fun f p hp ↦
    GlobalTheory.SCV.analyticAt_of_differentiableOn (u.hol U f).2 ((u.hol U f).1.mem_nhds ⟨hW p hp, hWU p hp⟩)
  let φ : Γ(X, U) →+* Hol W :=
    (RingHom.pi fun p : W ↦ valHom (u.E p) U (hWU p p.2)).codRestrict (holSub W) fun f ↦
      ⟨fun p ↦ valAt' (u.E p) U f, han f, fun p ↦ valHom_apply _ _ _ f⟩
  refine ⟨spMap φ ≫ hU.fromSpec, ?_, fun p hp ↦ ?_⟩
  · simp [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  · have e : (Hol.ev p hp).toRingHom.comp φ = valHom (u.E p) U (hWU p hp) := RingHom.ext fun f ↦ rfl
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    exact specMap_valHom_fromSpec _ hU _

end GlobalTheory.AnPer
