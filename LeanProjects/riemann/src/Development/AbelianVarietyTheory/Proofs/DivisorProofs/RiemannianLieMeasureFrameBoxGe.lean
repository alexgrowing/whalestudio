import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_skew_of_I_smul_skew {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    (M : Matrix (Fin r) (Fin r) ℂ)
    (h1 : ∀ u w, hermC τ G (M *ᵥ u) w + hermC τ G u (M *ᵥ w) = 0)
    (h2 : ∀ u w, hermC τ G ((Complex.I • M) *ᵥ u) w + hermC τ G u ((Complex.I • M) *ᵥ w) = 0) :
    M = 0 := by
  have hl : ∀ (c : ℂ) v w, hermC τ G (c • v) w = c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hr : ∀ (c : ℂ) v w, hermC τ G v (c • w) = starRingEnd ℂ c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hA : ∀ u w, hermC τ G (M *ᵥ u) w = 0 := by
    intro u w
    have e1 := h1 u w
    have e2 := h2 u w
    rw [smul_mulVec, smul_mulVec, hl, hr, Complex.conj_I] at e2
    have : Complex.I * (2 * hermC τ G (M *ᵥ u) w) = 0 := by linear_combination e2 + Complex.I * e1
    simpa [Complex.I_ne_zero] using this
  have hGt : (G.map τ).det ≠ 0 := by
    have e := RingHom.map_det τ G
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (map_ne_zero τ).2 hG
  have hv : ∀ u, M *ᵥ u = 0 := by
    intro u
    refine Matrix.eq_zero_of_vecMul_eq_zero hGt ?_
    funext b
    have := hA u (Pi.single b 1)
    simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply] using this
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem finrank_comap_realLie_le (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hr : 1 ≤ r) (hG : G.det ≠ 0) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    Module.finrank ℝ ((realLie Ψ G).comap (fromFrame x)) ≤ Ψ.card * (r ^ 2 - 1) := by
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hsm : ∀ (c : ℂ) (V : EuclideanSpace ℂ (Ψ × Fin r × Fin r)),
      fromFrame x (c • V) = c • fromFrame x V := by
    intro c V
    funext τ
    have e : Matrix.of (fun a b => (c • V) (τ, a, b)) = c • Matrix.of (fun a b => V (τ, a, b)) := rfl
    show (mat x τ * Matrix.of (fun a b => (c • V) (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) =
      c • (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
    rw [e, Matrix.mul_smul, Matrix.smul_mul]
  have hIW : ∀ V, V ∈ W → Complex.I • V ∈ W → V = 0 := by
    intro V h1 h2
    have h1' : fromFrame x V ∈ realLie Ψ G := h1
    have h2' : fromFrame x (Complex.I • V) ∈ realLie Ψ G := h2
    rw [hsm] at h2'
    have hM : ∀ τ, Matrix.of (fromFrame x V τ) = 0 := fun τ =>
      eq_zero_of_skew_of_I_smul_skew hG _ (h1' τ).2 (h2' τ).2
    refine PiLp.ext fun p => ?_
    obtain ⟨τ, a, b⟩ := p
    have e : (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := hM τ
    have := key1 τ (Matrix.of (fun a b => V (τ, a, b)))
    rw [e, Matrix.mul_zero, Matrix.zero_mul] at this
    have := congrFun (congrFun this a) b
    simpa using this.symm
  let L : (W × W) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
    { toFun := fun p => (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm] }
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hp' : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 0 := hp
    have e1 : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := by
      rw [Submodule.coe_neg, smul_neg]; exact eq_neg_of_add_eq_zero_left hp'
    have h3 : Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) ∈ W := e1 ▸ p.1.2
    have h4 := hIW _ (-p.2).2 h3
    have h5 : p.2 = 0 := by
      have : -p.2 = 0 := Subtype.ext h4
      simpa using this
    have h6 : p.1 = 0 := by
      apply Subtype.ext
      rw [e1, h4, smul_zero]; rfl
    exact Prod.ext h6 h5
  let tr : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] (Ψ → ℂ) :=
    { toFun := fun Y τ => ∑ a, Y (τ, a, a)
      map_add' := by
        intro Y Z; funext τ; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c Y; funext τ; simp [Finset.smul_sum] }
  have htrW : ∀ Y ∈ W, tr Y = 0 := by
    intro Y hY
    have hY' : fromFrame x Y ∈ realLie Ψ G := hY
    funext τ
    have ht := (hY' τ).1
    have e : Matrix.of (fromFrame x Y τ) = mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ := rfl
    rw [e, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ (hx τ).isUnit, Matrix.one_mul] at ht
    show ∑ a, Y (τ, a, a) = (0 : Ψ → ℂ) τ
    simpa [Matrix.trace] using ht
  have hrange : L.range ≤ LinearMap.ker tr := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    have e : L p = (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := rfl
    rw [e, map_add]
    have h2 : tr (Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))) = Complex.I • tr p.2 := by
      funext τ; simp [tr, Finset.mul_sum]
    rw [h2, htrW _ p.1.2, htrW _ p.2.2, smul_zero, add_zero]
  have hsurj : LinearMap.range tr = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      if p.2.1 = ⟨0, hr⟩ ∧ p.2.2 = ⟨0, hr⟩ then c p.1 else 0), ?_⟩
    funext τ
    simp [tr]
  have hdimE : Module.finrank ℝ (EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 2 * (Ψ.card * (r * r)) := by
    rw [(WithLp.linearEquiv 2 ℝ (Ψ × Fin r × Fin r → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_prod, Fintype.card_coe, mul_comm]
  have hdimP : Module.finrank ℝ (Ψ → ℂ) = 2 * Ψ.card := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_coe, mul_comm]
  have h1 := LinearMap.finrank_range_add_finrank_ker tr
  rw [hsurj, finrank_top, hdimE, hdimP] at h1
  have h2 := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_prod] at h2
  have h3 : Ψ.card * (r ^ 2 - 1) = Ψ.card * (r * r) - Ψ.card := by
    rw [Nat.mul_sub_one, sq]
  rw [h3]
  omega

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem riemLie_frameBox_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ((ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε} := by
  intro E _ _ _ r Ψ G x hr hG hx ε hε hε1
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  unfold riemLie
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  refine le_trans ?_ (Measure.le_map_apply hf.aemeasurable _)
  rw [OrthonormalBasis.addHaar_eq_volume]
  have hdim := finrank_comap_realLie_le Ψ G x hr hG hx
  set N := Module.finrank ℝ W with hN
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin N) ℝ W) := ⟨stdOrthonormalBasis ℝ W⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  set η : ℝ := ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) with hη
  have hη0 : 0 ≤ η := by positivity
  have hcr : (N : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
    have : N ≤ Ψ.card * r ^ 2 := hdim.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast this
  have hη1 : η ≤ 1 := by
    rcases Nat.eq_zero_or_pos Ψ.card with h0 | h0
    · simp [hη, h0]
    · have : (1 : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
        have : 1 ≤ Ψ.card * r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
        exact_mod_cast this
      exact div_le_one_of_le₀ (hε1.trans this) (by positivity)
  have hNη : (N : ℝ) * η ≤ ε := by
    calc (N : ℝ) * η ≤ ((Ψ.card : ℝ) * (r : ℝ) ^ 2) * η := mul_le_mul_of_nonneg_right hcr hη0
      _ ≤ ε := by
        rcases eq_or_ne ((Ψ.card : ℝ) * (r : ℝ) ^ 2) 0 with h0 | h0
        · rw [h0, zero_mul]; exact hε.le
        · rw [hη, mul_div_cancel₀ _ h0]
  let C : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Ioo (-(η / 2)) (η / 2)
  have hmp : MeasurePreserving (fun Y : W => (b.repr Y).ofLp) volume volume :=
    (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
  have hC : volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) = ENNReal.ofReal η ^ N := by
    rw [hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp [Finset.prod_const]
  calc ENNReal.ofReal (η ^ (Ψ.card * (r ^ 2 - 1))) = ENNReal.ofReal η ^ (Ψ.card * (r ^ 2 - 1)) :=
        ENNReal.ofReal_pow hη0 _
    _ ≤ ENNReal.ofReal η ^ N := pow_le_pow_right_of_le_one' (ENNReal.ofReal_le_one.2 hη1) hdim
    _ = volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) := hC.symm
    _ ≤ _ := by
      refine measure_mono fun Y hY => ?_
      simp only [Set.mem_preimage, C, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, true_implies] at hY
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro τ a c
      have e : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rw [e, key1]
      have h1 : ‖(Y.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, c)‖ ≤ ‖Y‖ := PiLp.norm_apply_le _ _
      have h2 : ‖Y‖ ≤ ∑ i, |(b.repr Y).ofLp i| := by
        calc ‖Y‖ = ‖∑ i, (b.repr Y).ofLp i • b i‖ := by rw [b.sum_repr]
          _ ≤ ∑ i, ‖(b.repr Y).ofLp i • b i‖ := norm_sum_le _ _
          _ = ∑ i, |(b.repr Y).ofLp i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
      have h3 : ∑ i, |(b.repr Y).ofLp i| ≤ (N : ℝ) * (η / 2) := by
        calc ∑ i, |(b.repr Y).ofLp i| ≤ ∑ _i : Fin N, η / 2 :=
              Finset.sum_le_sum fun i _ => (abs_lt.2 (hY i)).le
          _ = (N : ℝ) * (η / 2) := by simp
      simp only [Matrix.of_apply]
      linarith

end GlobalTheory.CovTop.VolUp
