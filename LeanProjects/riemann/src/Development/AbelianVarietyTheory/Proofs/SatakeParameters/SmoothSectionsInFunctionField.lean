import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem smooth_sections_in_functionField : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [inst' : Algebra ℂ Z'.functionField], Smooth p' → inst' = ffAlg p' → ∀ (W : Z'.Opens), IsAffineOpen W → ∀ (hW : genericPoint Z' ∈ W) (B : Subalgebra ℂ Z'.functionField), (∀ y, y ∈ B ↔ ∃ g : Γ(Z', W), (Z'.presheaf.germ W (genericPoint Z') hW).hom g = y) → Algebra.Smooth ℂ B := by
  intro Z' _ p' inst' hp hinst W hWa hW B hB
  subst hinst
  letI : Algebra ℂ Z'.functionField := ffAlg p'
  let φ : ℂ →+* Γ(Z', W) := (p'.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have h := HasRingHomProperty.appLE @Smooth p' hp ⟨⊤, isAffineOpen_top _⟩ ⟨W, hWa⟩ le_top
  have h' : RingHom.Smooth φ :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.bijective) h
  letI : Algebra ℂ Γ(Z', W) := φ.toAlgebra
  have hs : Algebra.Smooth ℂ Γ(Z', W) := h'
  let g := (Z'.presheaf.germ W (genericPoint Z') hW).hom
  have hg : Function.Injective g := germ_injective_of_isIntegral Z' (genericPoint Z') hW
  have hc : ∀ c : ℂ, g (algebraMap ℂ Γ(Z', W) c) = algebraMap ℂ Z'.functionField c := by
    intro c
    show g (φ c) = _
    simp only [φ, g, Scheme.Hom.appLE, CommRingCat.comp_apply, RingHom.comp_apply]
    show _ = (Z'.presheaf.germ ⊤ (genericPoint Z') trivial).hom ((p'.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl
  let gA : Γ(Z', W) →ₐ[ℂ] Z'.functionField := { g with commutes' := hc }
  let f : Γ(Z', W) →ₐ[ℂ] B := gA.codRestrict B (fun x => (hB _).2 ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => hg (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (hB y.1).1 y.2
    exact ⟨x, Subtype.ext hx⟩
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective f hf)

end GlobalTheory
