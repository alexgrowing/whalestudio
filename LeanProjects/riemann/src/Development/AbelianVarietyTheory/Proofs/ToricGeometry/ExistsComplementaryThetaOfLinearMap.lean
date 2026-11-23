import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory
namespace ThetaComplement

theorem exists_le_mul_of_homogeneous {g : ℕ} (p q : (Fin g → ℂ) → ℝ) (hp : Continuous p)
    (hq : Continuous q) (hp2 : ∀ (r : ℝ) z, p ((r : ℂ) • z) = r ^ 2 * p z)
    (hq2 : ∀ (r : ℝ) z, q ((r : ℂ) • z) = r ^ 2 * q z) (hpos : ∀ z, z ≠ 0 → 0 < p z) :
    ∃ C : ℝ, ∀ z, q z ≤ C * p z := by
  have hne : ∀ z ∈ Metric.sphere (0 : Fin g → ℂ) 1, z ≠ 0 := by
    intro z hz h
    rw [h] at hz
    simp at hz
  have hc : ContinuousOn (fun z => q z / p z) (Metric.sphere (0 : Fin g → ℂ) 1) :=
    hq.continuousOn.div hp.continuousOn (fun z hz => (hpos z (hne z hz)).ne')
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : Fin g → ℂ) 1).image_of_continuousOn hc).bddAbove
  refine ⟨C, fun z => ?_⟩
  by_cases hz : z = 0
  · have h1 := hp2 0 z
    have h2 := hq2 0 z
    simp only [ofReal_zero, zero_smul] at h1 h2
    rw [hz, h1, h2]; simp
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    set u : Fin g → ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) • z with hu
    have hus : u ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      field_simp
    have h1 : q u / p u ≤ C := hC ⟨u, hus, rfl⟩
    rw [div_le_iff₀ (hpos u (hne u hus)), hu, hp2, hq2] at h1
    have h2 : 0 < ‖z‖⁻¹ ^ 2 := by positivity
    have h3 : ‖z‖⁻¹ ^ 2 * q z ≤ ‖z‖⁻¹ ^ 2 * (C * p z) := by linarith
    exact le_of_mul_le_mul_left h3 h2

theorem dot_symm {g : ℕ} (S : Matrix (Fin g) (Fin g) ℂ) (hS : S.IsSymm) (u v : Fin g → ℂ) :
    u ⬝ᵥ S.mulVec v = v ⬝ᵥ S.mulVec u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq, dotProduct_comm]

theorem im_form {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hH : H.IsHermitian) (u v : Fin g → ℂ) :
    2 * I * ((u ⬝ᵥ H.mulVec (star v)).im : ℂ)
      = u ⬝ᵥ H.mulVec (star v) - v ⬝ᵥ H.mulVec (star u) := by
  have h : v ⬝ᵥ H.mulVec (star u) = star (u ⬝ᵥ H.mulVec (star v)) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  rw [h, star_def, Complex.sub_conj]
  push_cast; ring

theorem exists_form {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ ∈ SiegelH (Fin g)) :
    ∃ H : Matrix (Fin g) (Fin g) ℂ, H.IsHermitian ∧ H.IsSymm ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) ∧
      ∀ n n' : Fin g → ℤ, H.mulVec (star (τ *ᵥ ofIntVec n + ofIntVec n'))
        = H.mulVec (τ *ᵥ ofIntVec n + ofIntVec n') - (2 * I) • ofIntVec n := by
  obtain ⟨hs, hY⟩ := hτ
  set Y := τ.map Complex.im with hYd
  have hYi : Y⁻¹.PosDef := hY.inv
  have hsym : ∀ i j, Y⁻¹ i j = Y⁻¹ j i := fun i j => by
    simpa using (hYi.isHermitian.apply i j).symm
  refine ⟨Y⁻¹.map (fun x : ℝ => (x : ℂ)), ?_, ?_, ?_, ?_⟩
  · ext i j
    simp [hsym i j]
  · ext i j
    simp [hsym i j]
  · intro z hz
    have h : (z ⬝ᵥ (Y⁻¹.map (fun x : ℝ => (x : ℂ))).mulVec (star z)).re
        = (fun i => (z i).re) ⬝ᵥ Y⁻¹.mulVec (fun i => (z i).re)
          + (fun i => (z i).im) ⬝ᵥ Y⁻¹.mulVec (fun i => (z i).im) := by
      simp [dotProduct, mulVec, re_sum, im_sum, Finset.sum_add_distrib]
    rw [h]
    have h1 := hYi.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).re)
    have h2 := hYi.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).im)
    simp only [star_trivial] at h1 h2
    by_cases hr : (fun i => (z i).re) = 0
    · have hi : (fun i => (z i).im) ≠ 0 := by
        intro hi
        apply hz
        funext i
        exact Complex.ext (congrFun hr i) (congrFun hi i)
      have h3 := hYi.dotProduct_mulVec_pos hi
      simp only [star_trivial] at h3
      linarith
    · have h3 := hYi.dotProduct_mulVec_pos hr
      simp only [star_trivial] at h3
      linarith
  · intro n n'
    have h1 : star (τ *ᵥ ofIntVec n + ofIntVec n') = τ *ᵥ ofIntVec n + ofIntVec n'
        - (2 * I) • ((Y.map (fun x : ℝ => (x : ℂ))) *ᵥ ofIntVec n) := by
      funext i
      apply Complex.ext <;>
        simp [dotProduct, mulVec, re_sum, im_sum, ofIntVec, hYd]
      ring
    have h2 : Y⁻¹.map (fun x : ℝ => (x : ℂ)) * Y.map (fun x : ℝ => (x : ℂ)) = 1 := by
      have := (Matrix.map_mul (L := Y⁻¹) (M := Y) (f := Complex.ofRealHom)).symm
      rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.1 hY.isUnit)] at this
      exact this.trans (by simp)
    rw [h1, mulVec_sub, mulVec_smul, mulVec_mulVec, h2, one_mulVec]

theorem exists_normal_form {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ ∈ SiegelH (Fin g))
    (huniq : ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) :
    ∃ (H : Matrix (Fin g) (Fin g) ℂ) (s : (Fin g → ℂ) → ℤ) (Q : (Fin g → ℂ) → ℂ),
      H.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) ∧
      Differentiable ℂ Q ∧
      (∀ l ∈ periodLattice τ, ∀ m ∈ periodLattice τ, ∃ k : ℤ,
        (s (l + m) : ℂ) = s l + s m + ((l ⬝ᵥ H.mulVec (star m)).im : ℂ) + 2 * k) ∧
      ∀ (n n' : Fin g → ℤ) (l z : Fin g → ℂ), l = τ *ᵥ ofIntVec n + ofIntVec n' →
        2 * π * I * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)
          = -(π * I * s l + π * (z ⬝ᵥ H.mulVec (star l)) + π / 2 * (l ⬝ᵥ H.mulVec (star l))
            + Q (z + l) - Q z) := by
  classical
  obtain ⟨H, hH, hS, hpos, hst⟩ := exists_form τ hτ
  have hs : ∃ s : (Fin g → ℂ) → ℤ, ∀ n n' : Fin g → ℤ,
      s (τ *ᵥ ofIntVec n + ofIntVec n') = n ⬝ᵥ n' := by
    refine ⟨fun w => if h : ∃ p : (Fin g → ℤ) × (Fin g → ℤ),
      w = τ *ᵥ ofIntVec p.1 + ofIntVec p.2 then h.choose.1 ⬝ᵥ h.choose.2 else 0, fun n n' => ?_⟩
    have h : ∃ p : (Fin g → ℤ) × (Fin g → ℤ),
      τ *ᵥ ofIntVec n + ofIntVec n' = τ *ᵥ ofIntVec p.1 + ofIntVec p.2 := ⟨(n, n'), rfl⟩
    simp only [dif_pos h]
    have h1 := h.choose_spec
    generalize h.choose = p at h1
    obtain ⟨h2, h3⟩ := huniq (p.1 + -n) (p.2 + -n') (by
      rw [ofIntVec_add, ofIntVec_add, ofIntVec_neg, ofIntVec_neg, mulVec_add, mulVec_neg]
      linear_combination (exp := 1) -h1)
    rw [add_neg_eq_zero] at h2 h3
    rw [h2, h3]
  obtain ⟨s, hs⟩ := hs
  have hcast : ∀ n n' : Fin g → ℤ, ((n ⬝ᵥ n' : ℤ) : ℂ) = ofIntVec n ⬝ᵥ ofIntVec n' := by
    intro n n'
    simp [dotProduct, ofIntVec]
  refine ⟨H, s, fun z => -(π / 2) * (z ⬝ᵥ H.mulVec z), hH, hpos, ?_, ?_, ?_⟩
  · simp only [dotProduct, mulVec]
    fun_prop
  · rintro _ ⟨n, n', rfl⟩ _ ⟨p, p', rfl⟩
    refine ⟨p ⬝ᵥ n', ?_⟩
    have h1 : τ *ᵥ ofIntVec n + ofIntVec n' + (τ *ᵥ ofIntVec p + ofIntVec p')
        = τ *ᵥ ofIntVec (n + p) + ofIntVec (n' + p') := by
      rw [ofIntVec_add, ofIntVec_add, mulVec_add]; abel
    have h2 := im_form H hH (τ *ᵥ ofIntVec n + ofIntVec n') (τ *ᵥ ofIntVec p + ofIntVec p')
    rw [h1, hs, hs, hs]
    generalize ((((τ *ᵥ ofIntVec n + ofIntVec n') ⬝ᵥ
      H.mulVec (star (τ *ᵥ ofIntVec p + ofIntVec p'))).im : ℝ) : ℂ) = y at h2 ⊢
    have h4 : (τ *ᵥ ofIntVec n + ofIntVec n') ⬝ᵥ ofIntVec p
        = ofIntVec p ⬝ᵥ (τ *ᵥ ofIntVec n) + ((p ⬝ᵥ n' : ℤ) : ℂ) := by
      rw [dotProduct_comm, dotProduct_add, hcast]
    have h5 : (τ *ᵥ ofIntVec p + ofIntVec p') ⬝ᵥ ofIntVec n
        = ofIntVec p ⬝ᵥ (τ *ᵥ ofIntVec n) + ((n ⬝ᵥ p' : ℤ) : ℂ) := by
      rw [dotProduct_comm, dotProduct_add, hcast, dot_symm τ hτ.1]
    rw [hst, hst, dotProduct_sub, dotProduct_sub, dot_symm H hS, dotProduct_smul, dotProduct_smul,
      h4, h5, smul_eq_mul, smul_eq_mul] at h2
    have h3 : y = ((n ⬝ᵥ p' : ℤ) : ℂ) - ((p ⬝ᵥ n' : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero (α := ℂ)) I_ne_zero)
      linear_combination h2
    rw [h3, add_dotProduct, dotProduct_add, dotProduct_add]
    push_cast
    ring
  · rintro n n' l z hl
    have h1 := hst n n'
    have h2 := hs n n'
    have h3 : l ⬝ᵥ ofIntVec n = ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) + ofIntVec n ⬝ᵥ ofIntVec n' := by
      rw [dotProduct_comm, hl, dotProduct_add]
    rw [← hl] at h1 h2
    rw [h1, h2, hcast]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, mulVec_add, dotProduct_add,
      add_dotProduct, h3, dot_symm H hS l z, dotProduct_comm z (ofIntVec n)]
    ring

theorem form_conj {g : ℕ} (H M : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    u ⬝ᵥ (Mᵀ * H * Mᵀᴴ).mulVec (star v) = (M *ᵥ u) ⬝ᵥ H.mulVec (star (M *ᵥ v)) := by
  have h : star (M *ᵥ v) = Mᵀᴴ *ᵥ star v := by
    funext i
    simp [mulVec, dotProduct]
  rw [h, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end ThetaComplement

open ThetaComplement in

theorem exists_complementary_theta_of_linear_map :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Q : (Fin g → ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))))) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 → (∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (N : ℕ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ l ∈ periodLattice τ, F l ∈ periodLattice τ) → ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧ ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ (fun z => f (F z) * G z) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => f (F z) * G z) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => f (F z) * G z) z)) := by
  intro h1 _ _ _ h5 g τ hτ N F hF
  obtain ⟨hd, hsp, huniq⟩ := h1 g τ hτ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, fun z₀ => ⟨fun _ => 1, one_ne_zero, fun f hf => ⟨?_, fun n n' z => ?_⟩⟩⟩
    · exact (hf.1.comp F.toContinuousLinearMap.differentiable).mul (differentiable_const _)
    · obtain ⟨p, p', hp⟩ := hF _ ⟨n, n', rfl⟩
      have := hf.2 p p' (F z)
      simp only [add_assoc, map_add F z, hp] at this ⊢
      simpa [eC] using this
  obtain ⟨H, s, Q, hH, hpos, hQ, hs, hnf⟩ := exists_normal_form τ hτ huniq
  let Λ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule (periodLattice τ)
  obtain ⟨ρ, hρ⟩ := h5 g Λ hd hsp H hpos
  have hFc : Continuous F := F.continuous_of_finiteDimensional
  have hcont : Continuous (fun z : Fin g → ℂ => (z ⬝ᵥ H.mulVec (star z)).re) := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    fun_prop
  have hhom : ∀ (r : ℝ) (z : Fin g → ℂ), (((r : ℂ) • z) ⬝ᵥ H.mulVec (star ((r : ℂ) • z))).re
      = r ^ 2 * (z ⬝ᵥ H.mulVec (star z)).re := by
    intro r z
    simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    simp
    ring
  obtain ⟨C, hC⟩ := exists_le_mul_of_homogeneous (fun z => (z ⬝ᵥ H.mulVec (star z)).re)
    (fun z => (F z ⬝ᵥ H.mulVec (star (F z))).re) hcont (hcont.comp hFc) hhom
    (fun r z => by rw [map_smul]; exact hhom r (F z)) hpos
  obtain ⟨d, hdC⟩ := exists_nat_ge (C + |ρ|)
  refine ⟨d, fun z₀ => ?_⟩
  set M := LinearMap.toMatrix' F with hM
  have hMF : ∀ z, M *ᵥ z = F z := fun z => by simp [hM]
  set H' : Matrix (Fin g) (Fin g) ℂ := ((N * d : ℕ) : ℂ) • H - (N : ℂ) • (Mᵀ * H * Mᵀᴴ) with hH'
  have hform : ∀ u v : Fin g → ℂ, u ⬝ᵥ H'.mulVec (star v) = (N : ℂ) * d * (u ⬝ᵥ H.mulVec (star v))
      - N * (F u ⬝ᵥ H.mulVec (star (F v))) := by
    intro u v
    rw [hH', sub_mulVec, dotProduct_sub, smul_mulVec, smul_mulVec, dotProduct_smul,
      dotProduct_smul, form_conj, hMF, hMF]
    simp
  obtain ⟨θ, hθd, hθ0, hθ⟩ := hρ H'
    (fun l => cexp (π * I * ((N : ℂ) * d * s l - N * s (F l)))) (by
      have := Matrix.isHermitian_mul_mul_conjTranspose Mᵀ hH
      rw [Matrix.IsHermitian, hH', conjTranspose_sub, conjTranspose_smul, conjTranspose_smul,
        this.eq, hH.eq]
      simp) (by
      intro z
      rw [hform]
      have h0 : 0 ≤ (z ⬝ᵥ H.mulVec (star z)).re := by
        by_cases hz : z = 0
        · simp [hz]
        · exact (hpos z hz).le
      have h1 := hC z
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have h2 : ((N : ℂ) * d * (z ⬝ᵥ H.mulVec (star z)) - N * (F z ⬝ᵥ H.mulVec (star (F z)))).re
          = N * (d * (z ⬝ᵥ H.mulVec (star z)).re - (F z ⬝ᵥ H.mulVec (star (F z))).re) := by
        simp; ring
      rw [h2]
      generalize (z ⬝ᵥ H.mulVec (star z)).re = a at *
      generalize (F z ⬝ᵥ H.mulVec (star (F z))).re = b at *
      have h3 : |ρ| * a ≤ d * a - b := by nlinarith
      have h4 : 0 ≤ |ρ| * a := mul_nonneg (abs_nonneg _) h0
      have h5 : ρ * a ≤ |ρ| * a := mul_le_mul_of_nonneg_right (le_abs_self _) h0
      nlinarith) (by
      intro l
      rw [Complex.norm_exp]
      simp) (by
      intro l m
      obtain ⟨k, hk⟩ := hs l l.2 m m.2
      obtain ⟨k', hk'⟩ := hs _ (hF _ l.2) _ (hF _ m.2)
      rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨N * d * k - N * k', ?_⟩
      have h2 : (((l : Fin g → ℂ) ⬝ᵥ H'.mulVec (star (m : Fin g → ℂ))).im : ℂ)
          = N * d * (((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (m : Fin g → ℂ))).im : ℂ)
            - N * ((F l ⬝ᵥ H.mulVec (star (F m))).im : ℂ) := by
        rw [hform]; simp
      rw [h2, Submodule.coe_add, map_add, hk, hk']
      push_cast
      ring) z₀
  refine ⟨fun z => θ z * cexp ((N : ℂ) * d * Q z - N * Q (F z)),
    mul_ne_zero hθ0 (Complex.exp_ne_zero _), fun f hf => ⟨?_, fun n n' z => ?_⟩⟩
  · have hFd : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
    exact (hf.1.comp hFd).mul (hθd.mul ((hQ.const_mul _).sub
      ((hQ.comp hFd).const_mul _)).cexp)
  · obtain ⟨p, p', hp⟩ := hF _ ⟨n, n', rfl⟩
    have e1 := hf.2 p p' (F z)
    have e2 := hθ ⟨_, n, n', rfl⟩ z
    have e3 := hnf n n' _ z rfl
    have e4 := hnf p p' _ (F z) hp
    simp only [add_assoc] at e1 ⊢
    simp only [hform] at e2
    rw [← hp] at e1
    generalize τ *ᵥ ofIntVec n + ofIntVec n' = l at *
    rw [map_add, e1, e2]
    unfold eC
    have key : ∀ a b c e a' e' x y : ℂ, a + b + c + e = a' + e' →
        cexp a * x * (cexp b * cexp c * y * cexp e) = cexp a' * (x * (y * cexp e')) := by
      intro a b c e a' e' x y h
      have := congrArg cexp h
      simp only [Complex.exp_add] at this
      linear_combination x * y * this
    apply key
    push_cast
    linear_combination (-(N : ℂ)) * e4 + N * d * e3

end GlobalTheory
