import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem orbField {K : Type} [Field K] [CharZero K] (s : K →+* K) (θ : K) (hθ : θ ≠ 0)
    (hsθ : s θ = -θ) (hss : ∀ w, s (s w) = w) (x y z : K) (hx : s x = x) (hy : s y = y)
    (hdet : x * y - z * s z = θ ^ 2) :
    ∃ a b c d : K, a * d - b * c = 1 ∧ θ * (a * s b - b * s a) = x ∧ θ * (a * s d - b * s c) = z ∧
      θ * (c * s b - d * s a) = s z ∧ θ * (c * s d - d * s c) = y := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have s2 : s 2 = 2 := map_ofNat s 2
  by_cases hy0 : y = 0
  · by_cases hx0 : x = 0
    · have hN : z * s z = -θ ^ 2 := by
        rw [hx0, hy0] at hdet
        linear_combination -hdet
      by_cases hz : θ + z = 0
      · have hz' : z = -θ := by linear_combination hz
        have hsz : s z = θ := by rw [hz', map_neg, hsθ, neg_neg]
        refine ⟨θ, 0, 0, θ⁻¹, ?_, ?_, ?_, ?_, ?_⟩
        · field_simp
          simp
        · simp [hx0]
        · rw [map_inv₀, hsθ, hz']
          field_simp
          simp
        · rw [hsz, hsθ]
          field_simp
          simp
        · simp [hy0]
      · have hw : s z - θ ≠ 0 := by
          intro h0
          apply hz
          apply s.injective
          rw [map_add, hsθ, map_zero]
          linear_combination h0
        have sa : s ((θ + z) / θ) = (s z - θ) / (-θ) := by
          rw [map_div₀, map_add, hsθ]
          congr 1
          ring
        have sd : s (θ / (θ + z)) = (-θ) / (s z - θ) := by
          rw [map_div₀, map_add, hsθ]
          congr 1
          ring
        refine ⟨(θ + z) / θ, 0, 0, θ / (θ + z), ?_, ?_, ?_, ?_, ?_⟩
        · field_simp
          simp
        · simp [hx0]
        · rw [sd]
          simp only [zero_mul, sub_zero]
          field_simp
          linear_combination -hN
        · rw [sa]
          simp only [zero_mul, map_zero, mul_zero, zero_sub]
          field_simp
          linear_combination -hN
        · simp [hy0]
    · have sa : s (x / (2 * θ)) = -(x / (2 * θ)) := by
        rw [map_div₀, map_mul, hsθ, s2, hx]
        field_simp
      have sc : s ((s z - θ) / (2 * θ)) = -((z + θ) / (2 * θ)) := by
        rw [map_div₀, map_mul, hsθ, s2, map_sub, hss, hsθ]
        field_simp
        ring
      have sd : s ((s z + θ) / x) = (z - θ) / x := by
        rw [map_div₀, map_add, hsθ, hss, hx]
        ring
      refine ⟨x / (2 * θ), 1, (s z - θ) / (2 * θ), (s z + θ) / x, ?_, ?_, ?_, ?_, ?_⟩
      · field_simp
        ring
      · rw [sa, map_one]
        field_simp
        ring
      · rw [sd, sc]
        field_simp
        ring
      · rw [sa, map_one]
        field_simp
        ring
      · rw [sd, sc]
        field_simp
        linear_combination (-2) * hdet
  · have sa : s ((z + θ) / (2 * θ)) = -((s z - θ) / (2 * θ)) := by
      rw [map_div₀, map_mul, hsθ, s2, map_add, hsθ]
      field_simp
      ring
    have sb : s ((z - θ) / y) = (s z + θ) / y := by
      rw [map_div₀, map_sub, hsθ, hy]
      ring
    have sc : s (y / (2 * θ)) = -(y / (2 * θ)) := by
      rw [map_div₀, map_mul, hsθ, s2, hy]
      field_simp
    refine ⟨(z + θ) / (2 * θ), (z - θ) / y, y / (2 * θ), 1, ?_, ?_, ?_, ?_, ?_⟩
    · field_simp
      ring
    · rw [sa, sb]
      field_simp
      linear_combination (-2) * hdet
    · rw [map_one, sc]
      field_simp
      ring
    · rw [sa, sb]
      field_simp
      ring
    · rw [map_one, sc]
      field_simp
      ring

private theorem fix_of {R : Type} [CommRing R] (t t' a b c d a' b' c' d' : R) (ht : t * t' = 1)
    (hdet : a * d - b * c = 1) (e00 : t * (a * b' - b * a') = 0) (e01 : t * (a * d' - b * c') = t)
    (e10 : t * (c * b' - d * a') = -t) (e11 : t * (c * d' - d * c') = 0) :
    a' = a ∧ b' = b ∧ c' = c ∧ d' = d := by
  have p : a * b' - b * a' = 0 := by linear_combination t' * e00 - (a * b' - b * a') * ht
  have q : a * d' - b * c' = 1 := by linear_combination t' * e01 - (a * d' - b * c' - 1) * ht
  have r : c * b' - d * a' = -1 := by linear_combination t' * e10 - (c * b' - d * a' + 1) * ht
  have u : c * d' - d * c' = 0 := by linear_combination t' * e11 - (c * d' - d * c') * ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-a') * hdet + c * p - a * r
  · linear_combination (-b') * hdet + d * p - b * r
  · linear_combination (-c') * hdet - a * u + c * q
  · linear_combination (-d') * hdet - b * u + d * q

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

private theorem hermitian_standardVector : D.herm (rp X0) = !![0, rt D.θ; -rt D.θ, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dat.herm, X0, rp, Dat.mkE_def]

private theorem act_fix_iff (h : G1 E) :
    D.act (gl h) (rp X0) = rp X0 ↔ ∀ i j, D.bar (h i j) = h i j := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.det_coe
    rwa [Matrix.det_fin_two] at this
  have key : D.act (gl h) (rp X0) = rp X0 ↔
      h.1 * D.herm (rp X0) * D.star2 h.1 = D.herm (rp X0) := by
    have := D.herm_act (gl h) (rp X0)
    constructor
    · intro e
      rw [e] at this
      exact this.symm
    · intro e
      exact D.herm_injective (this.trans e)
  rw [key, hermitian_standardVector]
  have ht : rt D.θ * rt D.θ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ D.θ_ne_zero, map_one]
  constructor
  · intro e
    have e00 := congrFun (congrFun e 0) 0
    have e01 := congrFun (congrFun e 0) 1
    have e10 := congrFun (congrFun e 1) 0
    have e11 := congrFun (congrFun e 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at e00 e01 e10 e11
    obtain ⟨f1, f2, f3, f4⟩ := fix_of (rt D.θ) (rt D.θ⁻¹) (h 0 0) (h 0 1) (h 1 0) (h 1 1)
      (D.bar (h 0 0)) (D.bar (h 0 1)) (D.bar (h 1 0)) (D.bar (h 1 1)) ht hdet
      (by linear_combination e00) (by linear_combination e01) (by linear_combination e10) (by linear_combination e11)
    intro i j
    fin_cases i <;> fin_cases j
    · exact f1
    · exact f2
    · exact f3
    · exact f4
  · intro hb
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, hb, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · ring
    · linear_combination rt D.θ * hdet
    · linear_combination (-rt D.θ) * hdet
    · ring

private theorem part2 (h : G1 E) :
    D.act (gl h) (rp X0) = rp X0 ↔ ∃ g : G1 ℚ, gl h = em E (gl g) := by
  rw [act_fix_iff]
  constructor
  · intro hb
    have hz : ∀ i j, h i j = am E (D.co (h i j) 0) := fun i j => D.eq_am_of_bar_eq (hb i j)
    have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
      have := h.det_coe
      rwa [Matrix.det_fin_two] at this
    refine ⟨⟨Matrix.of fun i j => D.co (h i j) 0, ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      apply am_injective (E := E)
      simp only [Matrix.of_apply, map_sub, map_mul, map_one, ← hz]
      exact hdet
    · apply Units.ext
      ext i j
      exact hz i j
  · rintro ⟨g, hg⟩ i j
    have : h i j = am E (g i j) := congrArg (fun u : GL (Fin 2) (A E) => u.1 i j) hg
    rw [this]
    exact D.bar_am _

private theorem part3 (γ : SpecialLinearGroup (Fin 2) E) :
    D.act (gl (ratS E γ)) (rp X0) = rp X0 ↔ ∃ g, gl (ratS E γ) = em E (gl (ratS ℚ g)) := by
  constructor
  · intro e
    have hb := (act_fix_iff D _).1 e
    have inj : Function.Injective (algebraMap E (A E)) := AdeleRing.algebraMap_injective (𝓞 E) E
    have hz : ∀ i j, γ i j = algebraMap ℚ E (D.b.repr (γ i j) 0) := by
      intro i j
      have h1 : D.bar (rt (γ i j)) = rt (γ i j) := hb i j
      have h2 := D.eq_am_of_bar_eq h1
      rw [D.co_rt, am_rt] at h2
      exact inj h2
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe
      rwa [Matrix.det_fin_two] at this
    refine ⟨⟨Matrix.of fun i j => D.b.repr (γ i j) 0, ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      apply (algebraMap ℚ E).injective
      simp only [Matrix.of_apply, map_sub, map_mul, map_one, ← hz]
      exact hdet
    · apply Units.ext
      ext i j
      show rt (γ i j) = am E (rt (D.b.repr (γ i j) 0))
      rw [am_rt, ← hz]
  · rintro ⟨g, hg⟩
    exact (part2 D _).2 ⟨ratS ℚ g, hg⟩

private theorem part1 (ξ : Fin 4 → ℚ) (hq : qr D.δ ξ = qr D.δ X0) :
    ∃ γ : SpecialLinearGroup (Fin 2) E, rp ξ = D.act (gl (ratS E γ)) (rp X0) := by
  have inj : Function.Injective (algebraMap E (A E)) := AdeleRing.algebraMap_injective (𝓞 E) E
  have hsq : D.θ ^ 2 = algebraMap ℚ E D.δ := D.sq
  have hss : ∀ w, D.σ (D.σ w) = w := by
    intro w
    apply inj
    have := D.bar_bar (rt w)
    rwa [D.bar_rt, D.bar_rt] at this
  obtain ⟨z, hzdef⟩ : ∃ z, z = algebraMap ℚ E (ξ 2) + algebraMap ℚ E (ξ 3) * D.θ := ⟨_, rfl⟩
  have hsz : D.σ z = algebraMap ℚ E (ξ 2) - algebraMap ℚ E (ξ 3) * D.θ := by
    rw [hzdef, map_add, map_mul, D.conj, AlgEquiv.commutes, AlgEquiv.commutes]
    ring
  have hdet : algebraMap ℚ E (ξ 1) * algebraMap ℚ E (ξ 0) - z * D.σ z = D.θ ^ 2 := by
    have h0 : ξ 1 * ξ 0 - (ξ 2 ^ 2 - D.δ * ξ 3 ^ 2) = D.δ := by
      simp [qr, X0] at hq
      linarith
    have h1 := congrArg (algebraMap ℚ E) h0
    simp only [map_sub, map_mul, map_pow] at h1
    rw [hsz, hzdef]
    linear_combination h1 + (algebraMap ℚ E (ξ 3) ^ 2 - 1) * hsq
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5⟩ := orbField (D.σ : E →+* E) D.θ D.θ_ne_zero D.conj hss
    (algebraMap ℚ E (ξ 1)) (algebraMap ℚ E (ξ 0)) z (D.σ.commutes _) (D.σ.commutes _) hdet
  simp only [RingHom.coe_coe] at h2 h3 h4 h5
  refine ⟨⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h1⟩, D.herm_injective ?_⟩
  rw [D.herm_act, hermitian_standardVector]
  have hval : ((gl (ratS E ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h1⟩) : GL (Fin 2) (A E)) :
      Matrix (Fin 2) (Fin 2) (A E)) = !![rt a, rt b; rt c, rt d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hval, D.herm_eq]
  have g2 := congrArg (algebraMap E (A E)) h2
  have g3 := congrArg (algebraMap E (A E)) h3
  have g4 := congrArg (algebraMap E (A E)) h4
  have g5 := congrArg (algebraMap E (A E)) h5
  simp only [map_mul, map_sub] at g2 g3 g4 g5
  have m : D.mkE (rp ξ 2) (rp ξ 3) = rt z := by rw [hzdef]; exact D.mkE_rt _ _
  rw [m, D.bar_rt, am_rt, am_rt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, D.bar_rt, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination -g2
  · linear_combination -g3
  · linear_combination -g4
  · linear_combination -g5

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orbS :
    OrbS := by
  intro E _ _ _ D
  exact ⟨part1 D, part2 D, part3 D⟩
