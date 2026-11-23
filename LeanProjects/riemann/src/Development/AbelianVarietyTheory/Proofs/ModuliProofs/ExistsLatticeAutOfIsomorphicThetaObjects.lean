import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem holUnif_linear_eq_self_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z = z := by
  have hmem : ∀ z, F z - z ∈ u.Λ := fun z => by
    rw [← u.ker]
    have h := u.ex_add (F z - z) z
    rw [sub_add_cancel, hF] at h
    exact mul_eq_right.1 h.symm
  have := u.discrete
  have hc : Continuous (fun z => (⟨F z - z, hmem z⟩ : u.Λ)) :=
    (F.continuous_of_finiteDimensional.sub continuous_id).subtype_mk _
  have h := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa [sub_eq_zero] using h

theorem holUnif_linear_lift_mem {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
    (u : HolUnif A L g) (u' : HolUnif A' L' g') (f : A ⟶ A') [IsMonHom f]
    (F : (Fin g → ℂ) → (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) (z : Fin g → ℂ) (hz : z ∈ u.Λ) :
    F z ∈ u'.Λ := by
  rw [← u'.ker, hF, (u.ker z).2 hz]
  exact MonObj.one_comp f

theorem exists_addEquiv_of_linearEquiv_range {La : Type} [AddCommGroup La] {g : ℕ} (Q Q' : La →+ (Fin g → ℂ))
    (hQ : Function.Injective Q) (hQ' : Function.Injective Q') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h₁ : ∀ x, h (Q' x) ∈ Q.range) (h₂ : ∀ x, h.symm (Q x) ∈ Q'.range) :
    ∃ gam : La ≃+ La, ∀ x, h (Q' x) = Q (gam x) := by
  choose a ha using h₁
  choose c hc using h₂
  refine ⟨{ toFun := a, invFun := c, left_inv := fun x => hQ' ?_, right_inv := fun x => hQ ?_,
            map_add' := fun x y => hQ ?_ }, fun x => (ha x).symm⟩
  · rw [hc, ha, h.symm_apply_apply]
  · rw [ha, hc, h.apply_symm_apply]
  · rw [map_add, ha, ha, ha, map_add, map_add]

theorem exists_lattice_aut_of_tMap_id :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t t' : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q Q' : La →+ (Fin g → ℂ)) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ), Function.Injective Q → Function.Injective Q' → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t'.A t'.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t'.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t'.act j₀) → TMap t' t (𝟙 _) → ∃ (gam : La ≃+ La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), ∀ x, h (Q' x) = Q (gam x) := by
  intro o _ g k J b em w w' t t' La _ EF lam ac Q Q' Hm Hm' hQ hQ' ⟨u, _, _, hΛ, _⟩ ⟨u', _, _, hΛ', _⟩ ⟨φ, hφ, _⟩
  have hid : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_of_iso (Iso.refl t.A))
  have he' : IsMonHom e.inv := inferInstance
  obtain ⟨F, hF⟩ : ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u'.ex z ≫ e.hom :=
    exists_linear_lift_of_isMonHom_polAV t'.pol t.pol t'.L t.L u' u e.hom he
  obtain ⟨G, hG⟩ : ∃ G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u'.ex (G z) = u.ex z ≫ e.inv :=
    exists_linear_lift_of_isMonHom_polAV t.pol t'.pol t.L t'.L u u' e.inv he'
  have hFG : ∀ z, F (G z) = z := holUnif_linear_eq_self_of_ex_eq u (F ∘ₗ G) fun z => by
    rw [LinearMap.comp_apply, hF, hG, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hGF : ∀ z, G (F z) = z := holUnif_linear_eq_self_of_ex_eq u' (G ∘ₗ F) fun z => by
    rw [LinearMap.comp_apply, hG, hF, Category.assoc, e.hom_inv_id, Category.comp_id]
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear F G (LinearMap.ext hFG) (LinearMap.ext hGF)
  obtain ⟨gam, hgam⟩ := exists_addEquiv_of_linearEquiv_range Q Q' hQ hQ' h
    (fun x => (hΛ _).1 (holUnif_linear_lift_mem u' u e.hom F hF _ ((hΛ' _).2 ⟨x, rfl⟩)))
    (fun x => (hΛ' _).1 (holUnif_linear_lift_mem u u' e.inv G hG _ ((hΛ _).2 ⟨x, rfl⟩)))
  exact ⟨gam, h, hgam⟩

end GlobalTheory
