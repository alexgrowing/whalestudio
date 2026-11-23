import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaJetMeanL2Bound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.JetPlaceBound

theorem form_sum_right {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (x : V) {r : ℕ} (e : Fin r → V) (c : Fin r → K) :
    h.form σ x (∑ k, c k • e k) = ∑ k, σ (c k) * h.form σ x (e k) := by
  have h0 : h.form σ x 0 = 0 := by
    have := h.smul_right σ 0 x 0
    simpa using this
  let f : V →+ ℂ := { toFun := h.form σ x, map_zero' := h0, map_add' := h.add_right σ x }
  change f _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => h.smul_right σ _ _ _

theorem form_basis {K : Type} [Field K] {r : ℕ} (h : HermFam K (Fin r → K)) (σ : K →+* ℂ) (x y : Fin r → K) :
    h.form σ x y = ∑ k, ∑ l, starRingEnd ℂ (σ (x k)) * σ (y l) * h.form σ (Pi.single k 1) (Pi.single l 1) := by
  have e : ∀ w : Fin r → K, w = ∑ k, w k • (Pi.single k 1 : Fin r → K) := fun w => by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ∀ (a w : Fin r → K), h.form σ a w = ∑ l, σ (w l) * h.form σ a (Pi.single l 1) := fun a w => by
    conv_lhs => rw [e w]
    exact form_sum_right h σ a _ w
  rw [← h.conj_symm σ y x, h1 y x, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, h.conj_symm, h1 _ y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem posDef_of_re {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h1 : Hm.IsHermitian)
    (h2 : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos h1 fun x hx => ?_
  have h3 := h2 (star x) (by simpa using hx)
  rw [star_star] at h3
  refine Complex.pos_iff.2 ⟨h3, ?_⟩
  exact (h1.im_star_dotProduct_mulVec_self x).symm

theorem factor_norm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.PosDef) (N : ℕ) (χ : ℂ) (hχ : ‖χ‖ = 1)
    (z l : Fin g → ℂ) :
    ‖(χ * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ N‖ ^ 2 *
      Real.exp (-(Real.pi * N * (hermForm Hm (z + l) (z + l)).re)) =
      Real.exp (-(Real.pi * N * (hermForm Hm z z).re)) := by
  rw [add_comm z l, GlobalTheory.ThetaJetMean.herm_add_re hH l z, norm_pow, norm_mul, hχ, _root_.one_mul, Complex.norm_exp,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp [Complex.mul_re, Complex.div_ofNat_re]
  ring

theorem jet_bound_place : ∀ (K'' : Type) [Field K''] (σ : K'' →+* ℂ) (g r : ℕ) (hE : HermFam K'' (Fin r → K'')) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ) (N i : ℕ) (θ : Fin r → (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (ρ' : ℂ) (ρ0 : ℝ) (Y0 : Fin g → ℂ) (J : (Fin r → K'') →ₗ[K''] K'') (V : Submodule K'' (Fin r → K'')), 1 ≤ N → u.IsAH Hm χ → (∀ a, u.IsThetaFn Hm χ N (θ a)) → IsAddFundamentalDomain u.Λ Fd volume → (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → IsLeast {t | ∃ z ∈ u.Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} ρ0 → (∀ a b, hE.form σ (Pi.single a 1) (Pi.single b 1) = (∫ z in Fd, starRingEnd ℂ (θ a z) * θ b z * (Real.exp (-(Real.pi * N * (hermForm Hm z z).re)) : ℝ)) / (((volume Fd).toReal * ‖ρ'‖ ^ 2 : ℝ) : ℂ)) → (∀ c ∈ V, σ (J c) * ρ' = iteratedDeriv i (fun t : ℂ => ∑ a, σ (c a) * θ a (t • Y0)) 0) → ρ' ≠ 0 → ∀ (q : ℕ) (v : Fin q → Fin r → K'') (c : Fin q → ℂ), (∀ a, v a ∈ V) → ‖∑ a, c a * σ (J (v a))‖ ^ 2 ≤ (jetBd g N i ρ0 * √(Real.pi * (hermForm Hm Y0 Y0).re) ^ i) ^ 2 * (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)).re := by
  intro K _ σ g r hE A _ L u Hm χ Ef N i θ Fd ρ' ρ0 Y0 J V hN hAH hθ hFd hEf hbij hρ0 hform hJ hρ' q v c hv
  haveI := u.discrete
  have hH : Hm.PosDef := posDef_of_re hAH.1 hAH.2.1
  have hχ := hAH.2.2.1
  set E : (Fin g → ℂ) → ℝ := fun z => Real.exp (-(Real.pi * N * (hermForm Hm z z).re)) with hEdef
  have hHc : Continuous (fun z => hermForm Hm z z) := by unfold hermForm dotProduct Matrix.mulVec; fun_prop
  have hEc : Continuous E := by fun_prop
  have hθd : ∀ a, Differentiable ℂ (θ a) := fun a => (hθ a).1
  have hθc : ∀ a, Continuous (θ a) := fun a => (hθd a).continuous
  set φ : u.Λ → (Fin g → ℂ) → ℂ := fun l z =>
    (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ N with hφ
  have hφE : ∀ (l : u.Λ) z, ‖φ l z‖ ^ 2 * E (z + l) = E z := fun l z => factor_norm hH N (χ l) (hχ l) z l
  have hθφ : ∀ a (l : u.Λ) z, θ a (z + l) = φ l z * θ a z := fun a l z => (hθ a).2 l z
  set gm : Fin r → ℂ := fun k => ∑ a, c a * σ (v a k) with hgm
  set Θ : (Fin g → ℂ) → ℂ := fun z => ∑ k, gm k * θ k z with hΘ
  have hΘd : Differentiable ℂ Θ := by fun_prop
  have hΘφ : ∀ (l : u.Λ) z, Θ (z + l) = φ l z * Θ z := fun l z => by
    simp only [hΘ, hθφ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hjet := GlobalTheory.ThetaJetMean.theta_jet_le_l2_norm g N i u.Λ Hm Ef ρ0 Θ Fd Y0 hN u.full hH hEf hbij hρ0 hΘd
    (fun l z => by
      change ‖Θ (z + l)‖ ^ 2 * E (z + l) = ‖Θ z‖ ^ 2 * E z
      rw [hΘφ, norm_mul, ← hφE l z]; ring) hFd

  have hint : ∀ a b, IntegrableOn (fun z => starRingEnd ℂ (θ a z) * θ b z * (E z : ℂ)) Fd volume := fun a b => by
    have hc : Continuous (fun z => starRingEnd ℂ (θ a z) * θ b z * (E z : ℂ)) := by
      have := hθc a; have := hθc b
      fun_prop
    have h1 := GlobalTheory.ThetaJetMean.L_integ g u.Λ _ Fd u.full hc.norm (fun l z => by
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, hθφ]
      rw [abs_of_pos (show 0 < E (z + l) from Real.exp_pos _), abs_of_pos (show 0 < E z from Real.exp_pos _),
        ← hφE l z]; ring) hFd
    exact (integrable_norm_iff hc.aestronglyMeasurable).1 h1

  have hcd : ∀ k, ContDiffAt ℂ i (fun t : ℂ => θ k (t • Y0)) 0 := fun k => by
    have : Differentiable ℂ (fun t : ℂ => θ k (t • Y0)) := (hθd k).comp (differentiable_id.smul_const Y0)
    exact (this.contDiff (n := i)).contDiffAt
  have hlin : ∀ β : Fin r → ℂ, iteratedDeriv i (fun t : ℂ => ∑ k, β k * θ k (t • Y0)) 0 =
      ∑ k, β k * iteratedDeriv i (fun t : ℂ => θ k (t • Y0)) 0 := fun β => by
    rw [iteratedDeriv_fun_sum (fun k _ => contDiffAt_const.mul (hcd k))]
    exact Finset.sum_congr rfl fun k _ => iteratedDeriv_const_mul_field _ _
  have hval : (∑ a, c a * σ (J (v a))) * ρ' = iteratedDeriv i (fun t : ℂ => Θ (t • Y0)) 0 := by
    simp only [hΘ]
    rw [hlin, Finset.sum_mul]
    simp only [_root_.mul_assoc, hgm, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hJ _ (hv a), hlin, Finset.mul_sum]

  have hform2 : (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)) =
      (((∫ z in Fd, ‖Θ z‖ ^ 2 * E z) / ((volume Fd).toReal * ‖ρ'‖ ^ 2) : ℝ) : ℂ) := by
    have s1 : (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)) =
        ∑ k, ∑ l, starRingEnd ℂ (gm k) * gm l * hE.form σ (Pi.single k 1) (Pi.single l 1) := by
      simp only [hgm, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      simp only [form_basis hE σ (v _) (v _), Finset.mul_sum]
      calc _ = ∑ a, ∑ k, ∑ b, ∑ l, starRingEnd ℂ (c a) * c b * (starRingEnd ℂ (σ (v a k)) * σ (v b l) * hE.form σ (Pi.single k 1) (Pi.single l 1)) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ k, ∑ a, ∑ b, ∑ l, starRingEnd ℂ (c a) * c b * (starRingEnd ℂ (σ (v a k)) * σ (v b l) * hE.form σ (Pi.single k 1) (Pi.single l 1)) := Finset.sum_comm
        _ = ∑ k, ∑ a, ∑ l, ∑ b, starRingEnd ℂ (c a) * c b * (starRingEnd ℂ (σ (v a k)) * σ (v b l) * hE.form σ (Pi.single k 1) (Pi.single l 1)) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ k, ∑ l, ∑ a, ∑ b, starRingEnd ℂ (c a) * c b * (starRingEnd ℂ (σ (v a k)) * σ (v b l) * hE.form σ (Pi.single k 1) (Pi.single l 1)) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ k, ∑ l, ∑ b, ∑ a, starRingEnd ℂ (c a) * c b * (starRingEnd ℂ (σ (v a k)) * σ (v b l) * hE.form σ (Pi.single k 1) (Pi.single l 1)) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
              Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
            ring
    have s2 : ((∫ z in Fd, ‖Θ z‖ ^ 2 * E z : ℝ) : ℂ) =
        ∑ k, ∑ l, starRingEnd ℂ (gm k) * gm l * ∫ z in Fd, starRingEnd ℂ (θ k z) * θ l z * (E z : ℂ) := by
      rw [← integral_complex_ofReal]
      simp only [← integral_const_mul]
      rw [Finset.sum_congr rfl fun k _ => (integral_finset_sum _ fun l _ => (hint k l).const_mul _).symm,
        ← integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (hint k l).const_mul _]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      have : ((‖Θ z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (Θ z) * Θ z := by
        rw [Complex.conj_mul']; push_cast; rfl
      simp only
      rw [Complex.ofReal_mul, this]
      simp only [hΘ, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [s1, Complex.ofReal_div, s2, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hform, mul_div_assoc]
  rw [hform2, Complex.ofReal_re]
  rw [← hval, norm_mul, mul_pow] at hjet
  have hpos : 0 < ‖ρ'‖ ^ 2 := by positivity
  rw [← div_div, ← mul_div_assoc, le_div_iff₀ hpos]
  exact hjet

end GlobalTheory.JetPlaceBound
end
