import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.UnifTransport

theorem hermForm_smul_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm H (c • z) w = c * hermForm H z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem hermForm_add_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm H (z + z') w = hermForm H z w + hermForm H z' w := by
  simp only [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm H z (w + w') = hermForm H z w + hermForm H z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm H z (c • w) = star c * hermForm H z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_eq_of_im {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (him : ∀ x ∈ S, ∀ y ∈ S, (hermForm H' (h x) (h y)).im = (hermForm H x y).im) (z w : Fin g → ℂ) :
    hermForm H' (h z) (h w) = hermForm H z w := by
  have first : ∀ y ∈ S, ∀ x, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro y hy
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add, hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun x hx => him x hx y hy)
    exact fun x => LinearMap.congr_fun hf x
  have both : ∀ x y, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro x
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add, hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun y hy => first y hy x)
    exact fun y => LinearMap.congr_fun hf y
  apply Complex.ext
  ·
    have hI := both (Complex.I • z) w
    rw [map_smul, hermForm_smul_left, hermForm_smul_left, Complex.I_mul_im, Complex.I_mul_im] at hI
    exact hI
  · exact both z w

theorem transport_uniformisation :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (La' : Type) [AddCommGroup La'] (EF' : LinearMap.BilinForm ℤ La') (lam' : Fin (2 * g) → La') (ac' : J → La' → La') (Q' : La' →+ (Fin g → ℂ)) (Hm' : Matrix (Fin g) (Fin g) ℂ) (e : La ≃+ La') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (Function.Injective Q' ∧ DiscreteTopology (Q').range ∧ Submodule.span ℝ (Set.range Q') = ⊤ ∧ (Hm').IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧ ∀ x y, (hermForm Hm' (Q' x) (Q' y)).im = EF' x y) → (∀ x, Q' (e x) = h (Q x)) → (∀ x y, EF' (e x) (e y) = EF x y) → (∀ j x, e (ac j x) = ac' j (e x)) → (∀ i, ∃ y, e (lam i) = lam' i + k • y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF' x (ac' w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac' j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro o _ g k J b em w w' t La _ EF lam ac Q Hm La' _ EF' lam' ac' Q' Hm' e h hA hA' hQ hE hac hlam hU
  obtain ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩ := hU

  have hsym : ∀ x, h.symm (Q' x) = Q (e.symm x) := by
    intro x
    have hx := hQ (e.symm x)
    rw [e.apply_symm_apply] at hx
    rw [hx, LinearEquiv.symm_apply_apply]

  have him : ∀ x ∈ Set.range Q, ∀ y ∈ Set.range Q,
      (hermForm Hm' ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) x)
        ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) y)).im = (hermForm Hm x y).im := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [← hQ, ← hQ, hA'.2.2.2.2.2, hA.2.2.2.2.2, hE]
  have hH : ∀ a c, a ⬝ᵥ Hm'.mulVec (star c) = (h.symm a) ⬝ᵥ Hm.mulVec (star (h.symm c)) := by
    intro a c
    have hac' := hermForm_eq_of_im Hm Hm' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Set.range Q) hA.2.2.1 him
      (h.symm a) (h.symm c)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hac'
    exact hac'

  have hper : ∀ a v, v ∈ u.Λ → u.ex (a - v) = u.ex a := by
    intro a v hv
    have hsplit := u.ex_add (a - v) v
    rw [sub_add_cancel, (u.ker v).2 hv, _root_.mul_one] at hsplit
    exact hsplit.symm
  refine ⟨holUnifReparam u h.symm (fun _ => 1) (differentiable_const 1) (fun _ => one_ne_zero),
    fun l => χ' ⟨h.symm l, l.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold HolUnif.IsAH
    refine ⟨hA'.2.2.2.1, hA'.2.2.2.2.1, fun l => hAH.2.2.1 _, ?_⟩
    intro l i z hz
    simp only [holUnifReparam, div_one, map_add]
    rw [hH z l, hH l l]
    exact hAH.2.2.2 ⟨h.symm l, l.2⟩ i (h.symm z) hz
  · intro z
    show h.symm z ∈ u.Λ ↔ z ∈ Q'.range
    rw [hΛ]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      rw [hQ, ha, LinearEquiv.apply_symm_apply]
    · rintro ⟨c, rfl⟩
      exact ⟨e.symm c, (hsym c).symm⟩
  · intro x l hl
    have hpos : h.symm (l : Fin g → ℂ) = Q (e.symm x) := by rw [hl, hsym]
    have hform := hE (e.symm x) (ac w (e.symm x))
    rw [hac, e.apply_symm_apply] at hform
    rw [hform]
    exact hχ (e.symm x) ⟨h.symm l, l.2⟩ hpos
  · intro i
    obtain ⟨y, hy⟩ := hlam i
    have hl : lam' i = e (lam i) - k • y := eq_sub_of_add_eq hy.symm
    have hmem : (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) ∈ u.Λ := by
      by_cases hk : ((k : ℕ) : ℂ) = 0
      · rw [hk, mul_zero, zero_smul]
        exact zero_mem _
      · rw [inv_mul_cancel₀ hk, one_smul]
        exact (hΛ _).2 ⟨e.symm y, rfl⟩
    have hpt' : h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i))
        = ((k : ℕ) : ℂ)⁻¹ • Q (lam i) - (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) := by
      rw [hl, map_sub, map_nsmul, map_smul, map_sub, map_nsmul, hsym, hsym, e.symm_apply_apply, smul_sub,
        mul_smul, Nat.cast_smul_eq_nsmul]
    show (t.pt i).left = (u.ex (h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i)))).left
    rw [hpt', hper _ _ hmem, hpt]
  · intro j
    obtain ⟨F, hF1, hF2⟩ := hact j
    refine ⟨(h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ∘ₗ F ∘ₗ (h.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), ?_, ?_⟩
    · intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hsym, hF1, ← hQ, hac, e.apply_symm_apply]
    · intro z
      show u.ex (h.symm (h (F (h.symm z)))) = u.ex (h.symm z) ≫ t.act j
      rw [LinearEquiv.symm_apply_apply, hF2]

end GlobalTheory.UnifTransport
