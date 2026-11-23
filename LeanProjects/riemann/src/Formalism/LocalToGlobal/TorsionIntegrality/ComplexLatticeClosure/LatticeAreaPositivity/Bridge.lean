import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.IsLatClosure
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsInitialThetaValue

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField Polynomial
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

theorem is_lattice_closure_holds : IsLatClosure := by
  intro a b hab
  have hD : a.re * b.im - a.im * b.re ≠ 0 := by
    intro h
    apply hab
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linarith
  have hind : LinearIndependent ℝ ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      Complex.zero_re, Complex.zero_im] at h1 h2
    constructor
    · have : s * (a.re * b.im - a.im * b.re) = 0 := by linear_combination b.im * h1 - b.re * h2
      exact (mul_eq_zero.mp this).resolve_right hD
    · have : t * (a.re * b.im - a.im * b.re) = 0 := by linear_combination a.re * h2 - a.im * h1
      exact (mul_eq_zero.mp this).resolve_right hD
  exact ⟨⟨a, b, hind⟩, Submodule.span_int_eq_addSubgroupClosure _⟩

theorem is_lattice_smul_holds : IsLatSmul := by
  rintro Λ c hc ⟨L, rfl⟩
  have h1 : L.lattice.toAddSubgroup = AddSubgroup.closure {L.ω₁, L.ω₂} := Submodule.span_int_eq_addSubgroupClosure _
  have h0 : c • AddSubgroup.closure {L.ω₁, L.ω₂} = AddSubgroup.closure {c • L.ω₁, c • L.ω₂} := by
    change AddSubgroup.map (DistribSMul.toAddMonoidHom ℂ c) _ = _
    rw [AddMonoidHom.map_closure, Set.image_pair]
    rfl
  rw [h1, h0]
  apply is_lattice_closure_holds
  have hpos := F.areaPos L
  unfold F.area at hpos
  have h2 : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := abs_pos.mp hpos
  have h3 : (starRingEnd ℂ) (c • L.ω₁) * (c • L.ω₂) = ((Complex.normSq c : ℝ) : ℂ) * ((starRingEnd ℂ) L.ω₁ * L.ω₂) := by
    rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.normSq_eq_conj_mul_self]
    ring
  rw [h3, Complex.im_ofReal_mul]
  exact mul_ne_zero (Complex.normSq_pos.mpr hc).ne' h2

theorem has_cm_smul_holds : HasCMSmul := by
  intro d Λ c h x hx
  rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hx ⊢
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨_, h s hs, by simp only [smul_eq_mul]; ring⟩

theorem sqrt_choice (s : ℂ) (d : ℕ) (hs : s ^ 2 = -(d : ℂ)) :
    s = Complex.I * ((Real.sqrt d : ℝ) : ℂ) ∨ -s = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
  have h1 : (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    ring
  have h2 : (s - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (s + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = 0 := by
    linear_combination hs - h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination -h)

theorem half_integral (K : Type) [Field K] [NumberField K] (d : ℕ) (hd4 : d % 4 = 3) (y : K) (hy : y ^ 2 = -(d : K)) :
    IsIntegral ℤ ((1 + y) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d = 4 * k + 3 := ⟨d / 4, by omega⟩
  have hkK : (d : K) = 4 * (k : K) + 3 := by rw [hk]; push_cast; ring
  refine ⟨X ^ 2 - X + C ((k : ℤ) + 1), ?_, ?_⟩
  · monicity!
  · rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast]
    push_cast
    linear_combination (1 / 4 : K) * hy - (1 / 4 : K) * hkK

theorem latI_hasCM (K : Type) [Field K] [NumberField K] (d : ℕ) (hd4 : d % 4 = 3) (x : K) (hx : x ^ 2 = -(d : K))
    (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (δ : ℂ) : HasCM d (latI φ 𝔞 δ) := by
  obtain ⟨y, hy, hφy⟩ : ∃ y : K, y ^ 2 = -(d : K) ∧ φ y = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
    have hs : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
    rcases sqrt_choice _ d hs with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨-x, by rw [neg_sq, hx], by rw [map_neg, h]⟩
  let w : 𝓞 K := ⟨(1 + y) / 2, half_integral K d hd4 y hy⟩
  have hw : φ ((w : 𝓞 K) : K) = F.cmTheta 1 d := by
    change φ ((1 + y) / 2) = _
    rw [map_div₀, map_add, map_one, hφy, map_ofNat]
    unfold F.cmTheta
    push_cast
    ring
  intro z hz
  unfold latI at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨w * c, 𝔞.mul_mem_left w hc, ?_⟩
    rw [← hw]
    push_cast
    rw [map_mul]
    ring
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem lattice_ideal_lattice_holds : LatILat := by
  intro K _ _ d _ hd4 x hx hK φ 𝔞 δ h𝔞 hδ
  refine ⟨?_, latI_hasCM K d hd4 x hx φ 𝔞 δ⟩
  obtain ⟨a, b, h, hl, -⟩ := exists_latI_basis K d hd4 x hx hK φ 𝔞 h𝔞
  rw [latI_eq_smul, hl]
  exact is_lattice_smul_holds _ δ hδ (is_lattice_closure_holds a b h.ne')

theorem lambda_conj_lattice_holds : LamConjLat := by
  intro D hU hC cc hcc δ hδ M _ hM ρ
  obtain ⟨𝔟, h𝔟, hρ⟩ := (hC cc hcc.1 M (br_jL_mem D cc hcc δ hδ M hM)).1 ρ
  have hjM : IntegralLatticeDensity.jL (TaylorLogMetric.lamOf D cc δ) ∈ M := by
    rw [← brcc_jL_delta D cc hcc δ hδ]; exact br_jL_mem D cc hcc δ hδ M hM
  have hj : ρ ⟨IntegralLatticeDensity.jL (TaylorLogMetric.lamOf D cc δ), hjM⟩ = IntegralLatticeDensity.jL (latI (brPhi D) 𝔟 1) := by
    rw [← br_lamOf_eq, ← hρ]; congr 2; exact (brcc_jL_delta D cc hcc δ hδ).symm
  obtain ⟨c, hc0, hlc, -⟩ := br_lamConj_eq hU M ρ (TaylorLogMetric.lamOf D cc δ) (latI (brPhi D) 𝔟 1) hM.2.1 hM.2.2
    (br_discr_lamOf D cc hcc δ hδ) (brcc_discr_one_ne D 𝔟 h𝔟) hjM hj
  obtain ⟨h1, h2⟩ := lattice_ideal_lattice_holds D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩
    (br_sqrt_sq D) (br_finrank_K D) (brPhi D) 𝔟 1 h𝔟 one_ne_zero
  rw [hlc]
  exact ⟨is_lattice_smul_holds _ c hc0 h1, has_cm_smul_holds _ _ c h2⟩

theorem lambda_conj_theta_holds : LamConjTheta := by
  intro D hU hC cc hcc δ hδ M _ hM ρ
  obtain ⟨h1, h2⟩ := lambda_conj_lattice_holds D hU hC cc hcc δ hδ M hM ρ
  have hd8 : D.host.d % 8 = 7 := by
    have := D.host.hyp.2.2.2.1
    omega
  obtain ⟨G, hG⟩ := th0Ex D.host.d _ hd8 h1 h2
  exact ⟨G, hG, fun G' hG' => th0Uniq D.host.d _ G' G h1 hG' hG, normPos D.host.d _ G h1 hG⟩

end Formalism.L2.Th1.F2
