import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

theorem exists_le_mul_of_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (q q' : E → ℝ) (hq : Continuous q) (hq' : Continuous q') (hpos : ∀ z, z ≠ 0 → 0 < q z)
    (hs : ∀ (t : ℝ) z, q (t • z) = t ^ 2 * q z) (hs' : ∀ (t : ℝ) z, q' (t • z) = t ^ 2 * q' z) :
    ∃ C : ℝ, ∀ z, q' z ≤ C * q z := by
  have hS : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hcont : ContinuousOn (fun z => q' z / q z) (Metric.sphere (0 : E) 1) := by
    refine hq'.continuousOn.div hq.continuousOn ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    exact (hpos z hz0).ne'
  obtain ⟨C, hC⟩ := hS.bddAbove_image hcont
  refine ⟨C, fun z => ?_⟩
  have h0 : ∀ f : E → ℝ, (∀ (t : ℝ) z, f (t • z) = t ^ 2 * f z) → f 0 = 0 := by
    intro f hf
    simpa using hf 0 0
  by_cases hz : z = 0
  · rw [hz, h0 q hs, h0 q' hs', mul_zero]
  · have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hwS : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr0.ne']
    have hzw : z = ‖z‖ • (‖z‖⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have hw0 : ‖z‖⁻¹ • z ≠ 0 := by
      intro h
      rw [h] at hwS
      simp at hwS
    have hwpos := hpos _ hw0
    have hCw : q' (‖z‖⁻¹ • z) / q (‖z‖⁻¹ • z) ≤ C := hC (Set.mem_image_of_mem _ hwS)
    rw [div_le_iff₀ hwpos] at hCw
    rw [hzw, hs, hs']
    calc ‖z‖ ^ 2 * q' (‖z‖⁻¹ • z) ≤ ‖z‖ ^ 2 * (C * q (‖z‖⁻¹ • z)) :=
          mul_le_mul_of_nonneg_left hCw (sq_nonneg _)
      _ = C * (‖z‖ ^ 2 * q (‖z‖⁻¹ • z)) := by ring

theorem hermForm_swap_of_isHermitian {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = (starRingEnd ℂ) (hermForm Hm z w) := by
  unfold hermForm
  change _ = star _
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h.apply j i]
  ring

theorem hermForm_add_add {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (z + w) (z + w) = hermForm Hm z z + hermForm Hm z w + hermForm Hm w z + hermForm Hm w w := by
  unfold hermForm
  simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add]
  ring

theorem re_hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z : Fin g → ℂ) :
    (hermForm Hm (t • z) (t • z)).re = t ^ 2 * (hermForm Hm z z).re := by
  unfold hermForm
  have hst : star (t • z) = t • star z := by rw [star_smul, star_trivial]
  rw [hst, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, Complex.smul_re]
  ring

theorem continuous_re_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (hermForm Hm z z).re := by
  unfold hermForm
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem exists_hermForm_pull {g g' : ℕ} {Hm : Matrix (Fin g') (Fin g') ℂ} (h : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) :
    ∃ K : Matrix (Fin g) (Fin g) ℂ, K.IsHermitian ∧ ∀ z w, hermForm K z w = hermForm Hm (F z) (F w) := by
  set M := LinearMap.toMatrix' F
  have hF : ∀ z, F z = M *ᵥ z := fun z => by rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h, fun z w => ?_⟩
  unfold hermForm
  rw [hF, hF, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z Mᵀ, vecMul_transpose, ← star_vecMul,
    vecMul_transpose]

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem semicharacter_add (u : HolUnif A L g) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l m : u.Λ) :
    χ (l + m) = χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im) := by
  obtain ⟨i, hi⟩ := GlobalTheory.SymmetricSemicharacter.exists_chart u GlobalTheory.SymmetricSemicharacter.valueRules hL 0
  have hfr := h.2.2.2
  have hl : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by
    rw [GlobalTheory.SectionTheta.ex_add_lattice]; exact hi
  have hex : u.ex ((l : Fin g → ℂ) + m) = u.ex 0 := by
    simpa using GlobalTheory.SectionTheta.ex_add_lattice u 0 (l + m)
  have hX : u.fr i ((l : Fin g → ℂ) + m) ≠ 0 := u.fr_ne i _ (by rw [hex]; exact hi)
  have hz : ∀ x, hermForm Hm 0 x = 0 := fun x => by simp [hermForm]
  have e1 : u.fr i 0 = χ (l + m) * cexp (Real.pi * hermForm Hm 0 ((l + m : u.Λ) : Fin g → ℂ) +
      Real.pi / 2 * hermForm Hm ((l + m : u.Λ) : Fin g → ℂ) ((l + m : u.Λ) : Fin g → ℂ)) *
      u.fr i (0 + ((l + m : u.Λ) : Fin g → ℂ)) := hfr (l + m) i 0 hi
  have e2 : u.fr i 0 = χ l * cexp (Real.pi * hermForm Hm 0 l + Real.pi / 2 * hermForm Hm l l) *
      u.fr i (0 + (l : Fin g → ℂ)) := hfr l i 0 hi
  have e3 : u.fr i (0 + (l : Fin g → ℂ)) = χ m * cexp (Real.pi * hermForm Hm (0 + (l : Fin g → ℂ)) m +
      Real.pi / 2 * hermForm Hm m m) * u.fr i (0 + (l : Fin g → ℂ) + m) := hfr m i (0 + l) hl
  simp only [hz, zero_add, mul_zero, Submodule.coe_add] at e1 e2 e3
  rw [e3] at e2
  rw [e2] at e1
  have hb : hermForm Hm (m : Fin g → ℂ) l = (starRingEnd ℂ) (hermForm Hm l m) :=
    hermForm_swap_of_isHermitian h.1 l m
  have hsc := Complex.sub_conj (hermForm Hm l m)
  have hexp : cexp (Real.pi / 2 * hermForm Hm l l) * cexp (Real.pi * hermForm Hm l m + Real.pi / 2 * hermForm Hm m m) =
      cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        cexp (Real.pi * I * (hermForm Hm l m).im) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hermForm_add_add, hb]
    congr 1
    push_cast at hsc ⊢
    linear_combination (Real.pi / 2 : ℂ) * hsc
  have hC := Complex.exp_ne_zero (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m))
  have key : (χ (l + m) - χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im)) *
      (cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        u.fr i ((l : Fin g → ℂ) + m)) = 0 := by
    linear_combination -e1 + (χ l * χ m * u.fr i ((l : Fin g → ℂ) + m)) * hexp
  rcases mul_eq_zero.1 key with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 (mul_ne_zero hC hX)

private theorem conj_cexp_pi_mul_I_mul_real (t : ℝ) :
    (starRingEnd ℂ) (cexp (Real.pi * I * t)) = cexp (-(Real.pi * I * t)) := by
  rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

theorem exists_complementary_theta
    (hth : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    (u : HolUnif A L g) (u' : HolUnif A' L' g') (hL : L.IsLB) (hL' : L'.IsLB)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (h : u.IsAH Hm χ) (h' : u'.IsAH Hm' χ') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (N : ℕ) :
    ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' N θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z) := by
  obtain ⟨K, hK, hKF⟩ := exists_hermForm_pull h'.1 F
  obtain ⟨Fl, hFl⟩ : ∃ Fl : u.Λ → u'.Λ, ∀ l, ((Fl l : u'.Λ) : Fin g' → ℂ) = F l :=
    ⟨fun l => ⟨F l, hF l l.2⟩, fun _ => rfl⟩
  have hFl_add : ∀ l m, Fl (l + m) = Fl l + Fl m := fun l m => by
    apply Subtype.ext
    rw [Submodule.coe_add, hFl, hFl, hFl, Submodule.coe_add, map_add]
  obtain ⟨ρ, hρ⟩ := hth g u.Λ u.discrete u.full Hm h.2.1
  obtain ⟨C, hC⟩ := exists_le_mul_of_homogeneous (fun z => (hermForm Hm z z).re) (fun z => (hermForm K z z).re)
    (continuous_re_hermForm Hm) (continuous_re_hermForm K) h.2.1 (re_hermForm_real_smul Hm)
    (re_hermForm_real_smul K)
  obtain ⟨d, hd⟩ := exists_nat_ge (ρ + N * C)
  refine ⟨d, fun z₀ => ?_⟩
  obtain ⟨Hg, hHg⟩ : ∃ Hg : Matrix (Fin g) (Fin g) ℂ, Hg = (d : ℂ) • Hm - (N : ℂ) • K := ⟨_, rfl⟩
  obtain ⟨χg, hχg⟩ : ∃ f : u.Λ → ℂ, ∀ l, f l = χ l ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N := ⟨_, fun _ => rfl⟩
  have hHg_form : ∀ z w, hermForm Hg z w = d * hermForm Hm z w - N * hermForm K z w := by
    intro z w
    simp [hHg, hermForm, sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul]
  have hHgH : Hg.IsHermitian := by
    rw [hHg, IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, h.1.eq, hK.eq]
    simp
  have hbound : ∀ z : Fin g → ℂ, ρ * (hermForm Hm z z).re ≤ (hermForm Hg z z).re := by
    intro z
    have hre : (hermForm Hg z z).re = d * (hermForm Hm z z).re - N * (hermForm K z z).re := by
      rw [hHg_form]; simp
    rw [hre]
    have h1 := hC z
    have h2 : 0 ≤ (hermForm Hm z z).re := by
      by_cases hz : z = 0
      · simp [hz, hermForm]
      · exact (h.2.1 z hz).le
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hd) h2]
  have hnorm : ∀ l, ‖χg l‖ = 1 := by
    intro l
    rw [hχg, norm_mul, norm_pow, norm_pow, h.2.2.1, Complex.norm_conj, h'.2.2.1, one_pow, one_pow, _root_.one_mul]
  have hsemi : ∀ l m : u.Λ, χg (l + m) = χg l * χg m *
      cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hg.mulVec (star (m : Fin g → ℂ))).im) := by
    intro l m
    change χg (l + m) = χg l * χg m * cexp (Real.pi * I * (hermForm Hg l m).im)
    have s1 := semicharacter_add u hL h l m
    have s2 := semicharacter_add u' hL' h' (Fl l) (Fl m)
    rw [hFl, hFl, ← hKF] at s2
    rw [hχg, hχg, hχg, hFl_add, s1, s2, hHg_form, map_mul, map_mul, conj_cexp_pi_mul_I_mul_real]
    have him : ((d : ℂ) * hermForm Hm l m - N * hermForm K l m).im =
        d * (hermForm Hm l m).im - N * (hermForm K l m).im := by simp
    rw [him]
    have he : cexp (Real.pi * I * (hermForm Hm l m).im) ^ d * cexp (-(Real.pi * I * (hermForm K l m).im)) ^ N =
        cexp (Real.pi * I * ((d * (hermForm Hm l m).im - N * (hermForm K l m).im : ℝ) : ℂ)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (χ l ^ d * χ m ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N * (starRingEnd ℂ) (χ' (Fl m)) ^ N) * he
  obtain ⟨G, hGd, hG0, hGt⟩ := hρ Hg χg hHgH hbound hnorm hsemi z₀
  refine ⟨G, hG0, fun θ hθ => ⟨?_, fun l z => ?_⟩⟩
  · exact (hθ.1.comp (LinearMap.toContinuousLinearMap F).differentiable).mul hGd
  · have t1 := hθ.2 (Fl l) (F z)
    rw [hFl, ← hKF, ← hKF] at t1
    have t2 : G (z + l) = χg l * cexp (Real.pi * hermForm Hg z l + Real.pi / 2 * hermForm Hg l l) * G z := hGt l z
    have hψ : χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h'.2.2.1]; simp
    have hψN : (χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l))) ^ N = 1 := by rw [hψ, one_pow]
    have hexp : cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N =
        cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ d := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    show θ (F (z + l)) * G (z + l) = _ * (θ (F z) * G z)
    rw [map_add, t1, t2, hHg_form, hHg_form, hχg]
    linear_combination (χ l ^ d * θ (F z) * G z * (cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N)) * hψN +
      (χ l ^ d * θ (F z) * G z) * hexp

end GlobalTheory.LatticeHom
