import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.MeasurePreservingOfAddEquiv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.NhdsInv

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin.SwSplit

open PositivityTheory.SiegelWeilFormula.SwLocFin HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc Filter
  Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig_of_cm (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem sigR_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ)
    (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, sig_sig_of_cm σ hcm e]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def rowMix {A : Type} [CommRing A] {n M : ℕ} (C : Matrix (Fin n) (Fin n) A) (Y : Fin n → Fin M → A) :
    Fin n → Fin M → A :=
  fun c i => ∑ k, C c k * Y k i

theorem rowMix_add {A : Type} [CommRing A] {n M : ℕ} (C : Matrix (Fin n) (Fin n) A) (Y Z : Fin n → Fin M → A) :
    rowMix C (Y + Z) = rowMix C Y + rowMix C Z := by
  funext c i
  simp [rowMix, mul_add, Finset.sum_add_distrib]

theorem rowMix_one {A : Type} [CommRing A] {n M : ℕ} (Y : Fin n → Fin M → A) :
    rowMix (1 : Matrix (Fin n) (Fin n) A) Y = Y := by
  funext c i
  simp [rowMix, Matrix.one_apply]

theorem rowMix_mul {A : Type} [CommRing A] {n M : ℕ} (P Q : Matrix (Fin n) (Fin n) A) (Y : Fin n → Fin M → A) :
    rowMix P (rowMix Q Y) = rowMix (P * Q) Y := by
  funext c i
  simp only [rowMix, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem rowMix_one_add {A : Type} [CommRing A] {n M : ℕ} (x : Matrix (Fin n) (Fin n) A) (Y : Fin n → Fin M → A) :
    rowMix (1 + x) Y = Y + rowMix x Y := by
  funext c i
  simp [rowMix, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

theorem sum_sum_sum_sum_comm {A : Type} [AddCommMonoid A] {n M : ℕ} (f : Fin M → Fin M → Fin n → Fin n → A) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ x : Fin M × Fin M × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have h2 : (∑ k, ∑ l, ∑ i, ∑ j, f i j k l) = ∑ y : Fin n × Fin n × Fin M × Fin M, f y.2.2.1 y.2.2.2 y.1 y.2.1 := by
    simp only [Fintype.sum_prod_type]
  rw [h1, h2]
  let e : (Fin M × Fin M × Fin n × Fin n) ≃ (Fin n × Fin n × Fin M × Fin M) :=
    { toFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
      invFun := fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

section Mat
variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}

theorem gramR_rowMix (hcm : IsCMExt F E σ) (J : Matrix (Fin M) (Fin M) E) (a : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (Y : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J (rowMix (a.map (sigR R σ)) Y) = a * gramR R σ J Y * (a.map (sigR R σ))ᵀ := by
  ext c p
  simp only [gramR, hR, hform, rowMix, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul,
    sigR_sigR R σ hcm, Finset.sum_mul, Finset.mul_sum]
  rw [sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_sum_eq_trace {A : Type} [CommRing A] (S T : Matrix (Fin n) (Fin n) A) :
    ∑ a, ∑ c, S a c * T c a = Matrix.trace (S * T) := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trPair_conj (hcm : IsCMExt F E σ) (J : Matrix (Fin M) (Fin M) E)
    (a b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Y : Fin n → Fin M → R ⊗[F] E) :
    trPair R ((a.map (sigR R σ))ᵀ * b * a) (gramR R σ J Y) =
      trPair R b (gramR R σ J (rowMix (a.map (sigR R σ)) Y)) := by
  unfold trPair
  rw [sum_sum_eq_trace, sum_sum_eq_trace, gramR_rowMix R σ hcm]
  congr 2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end Mat

theorem nM_rowMix_le (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} (C1 : ℝ)
    (hmul : ∀ (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (y : Matrix (Fin n) (Fin M) (Fv F v ⊗[F] E)),
      nM v (x * y) ≤ C1 * nM v x * nM v y)
    (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    nM v (rowMix x Y) ≤ C1 * nM v x * nM v Y := by
  have h := hmul x (Matrix.of Y)
  have e : (x * Matrix.of Y : Matrix (Fin n) (Fin M) (Fv F v ⊗[F] E)) = Matrix.of (rowMix x Y) := by
    ext c i
    erw [Matrix.mul_apply]
    rfl
  rw [e] at h
  exact h

theorem jtR_conj_inv' (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : Fv F v → ℂ) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    [μv.IsAddHaarMeasure] (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (hΦ : IsSB Φv) :
    ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → ∀ b b' : HermR (Fv F v) σ n,
      (b' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = ((1 + x).map (sigR (Fv F v) σ))ᵀ * b * (1 + x) →
      jtR (Fv F v) σ J ψR μv Φv b' = jtR (Fv F v) σ J ψR μv Φv b := by
  classical
  obtain ⟨C1, hC1, hmul⟩ := exists_nM_mul v (E := E) n n M
  obtain ⟨Cs, hCs, hsig⟩ := exists_nM_sig v σ n n
  obtain ⟨U, hU, hinvU⟩ := PositivityTheory.SiegelWeilFormula.OswLocFin.exists_nhds_invariant hΦ
  obtain ⟨ρ, hρ, hball⟩ := exists_ballM_subset (v := v) (p := n) (q := M) hU
  obtain ⟨R0, hR0⟩ := exists_bound_nM (v := v) (p := n) (q := M) hΦ.2.isCompact
  obtain ⟨r0, hr0, hdet⟩ := exists_isUnit_det v (E := E) n
  set R : ℝ := max R0 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K : ℝ := C1 * Cs + 1 with hKdef
  have hKpos : 0 < K := by positivity
  refine ⟨min r0 (min (1 / (2 * K)) (ρ / (K * R))), lt_min hr0 (lt_min (by positivity) (by positivity)), ?_⟩
  intro x hx b b' hb'
  have hx0 : nM v x ≤ r0 := hx.trans (min_le_left _ _)
  have hx1 : nM v x ≤ 1 / (2 * K) := hx.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hx2 : nM v x ≤ ρ / (K * R) := hx.trans ((min_le_right _ _).trans (min_le_right _ _))
  set x' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := x.map (sigR (Fv F v) σ) with hx'def
  set C : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (1 + x).map (sigR (Fv F v) σ) with hCdef
  have hC : C = 1 + x' := by
    rw [hCdef, hx'def, Matrix.map_add _ (fun a b => map_add _ a b), Matrix.map_one _ (map_zero _) (map_one _)]
  have hnx' : nM v x' ≤ Cs * nM v x := hsig x
  have hsmall : C1 * nM v x' ≤ 1 / 2 := by
    have h1 : C1 * nM v x' ≤ C1 * Cs * nM v x := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hnx' hC1
    have h2 : C1 * Cs * nM v x ≤ C1 * Cs * (1 / (2 * K)) := mul_le_mul_of_nonneg_left hx1 (by positivity)
    have h3 : C1 * Cs * (1 / (2 * K)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hsmall2 : C1 * nM v x' * R ≤ ρ := by
    have h1 : C1 * nM v x' ≤ C1 * Cs * nM v x := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hnx' hC1
    have h2 : C1 * Cs * nM v x ≤ C1 * Cs * (ρ / (K * R)) := mul_le_mul_of_nonneg_left hx2 (by positivity)
    have h3 : C1 * Cs * (ρ / (K * R)) * R ≤ ρ := by
      rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : C1 * Cs ≤ K := by rw [hKdef]; linarith
      nlinarith [mul_le_mul_of_nonneg_right this (le_of_lt (mul_pos hρ hRpos))]
    calc C1 * nM v x' * R ≤ C1 * Cs * (ρ / (K * R)) * R :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hRpos.le
      _ ≤ ρ := h3

  have hnorm : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, nM v (rowMix C Y) = nM v Y := by
    intro Y
    rw [hC, rowMix_one_add]
    by_cases hY : Y = 0
    · subst hY
      have : rowMix x' (0 : Fin n → Fin M → Fv F v ⊗[F] E) = 0 := by funext c i; simp [rowMix]
      rw [this, add_zero]
    · have hpos : 0 < nM v Y := lt_of_le_of_ne (nM_nonneg Y) (fun h => hY (nM_eq_zero.1 h.symm))
      refine nM_add_eq_of_lt ?_
      calc nM v (rowMix x' Y) ≤ C1 * nM v x' * nM v Y := nM_rowMix_le v C1 hmul x' Y
        _ ≤ 1 / 2 * nM v Y := mul_le_mul_of_nonneg_right hsmall hpos.le
        _ < nM v Y := by linarith

  have hΦC : ∀ Y, Φv (rowMix C Y) = Φv Y := by
    intro Y
    by_cases hY : nM v Y ≤ R
    · rw [hC, rowMix_one_add]
      refine hinvU Y _ (hball ?_)
      show nM v (rowMix x' Y) ≤ ρ
      calc nM v (rowMix x' Y) ≤ C1 * nM v x' * nM v Y := nM_rowMix_le v C1 hmul x' Y
        _ ≤ C1 * nM v x' * R := mul_le_mul_of_nonneg_left hY (mul_nonneg hC1 (nM_nonneg _))
        _ ≤ ρ := hsmall2
    · have h1 : Y ∉ tsupport Φv := fun h => hY ((hR0 Y h).trans (le_max_left _ _))
      have h2 : rowMix C Y ∉ tsupport Φv := fun h => hY ((hnorm Y) ▸ ((hR0 _ h).trans (le_max_left _ _)))
      rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

  have hCu : IsUnit C.det := by
    have := hdet x hx0
    rw [hCdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact this.map _
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃+ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := rowMix C
      invFun := rowMix C⁻¹
      left_inv := fun Y => by rw [rowMix_mul, Matrix.nonsing_inv_mul C hCu, rowMix_one]
      right_inv := fun Y => by rw [rowMix_mul, Matrix.mul_nonsing_inv C hCu, rowMix_one]
      map_add' := rowMix_add C }
  have hcont : ∀ P : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), Continuous (rowMix (M := M) P) := by
    intro P
    refine continuous_pi fun c => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_const.mul ((continuous_apply i).comp (continuous_apply k))
  have hmp : MeasurePreserving e μv μv := by
    refine PositivityTheory.SiegelWeilFormula.OswLocFin.measurePreserving_of_addEquiv μv e (hcont C) (hcont C⁻¹)
      {Y | nM v Y ≤ 1} (isCompact_ballM 1) ?_ ?_
    · refine ⟨0, ?_⟩
      rw [(isOpen_ballM (v := v) (p := n) (q := M) one_pos).interior_eq]
      show nM v (0 : Fin n → Fin M → Fv F v ⊗[F] E) ≤ 1
      rw [nM_zero]; exact zero_le_one
    · ext Y
      show nM v (rowMix C Y) ≤ 1 ↔ nM v Y ≤ 1
      rw [hnorm]
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.mk e.toEquiv (hcont C) (hcont C⁻¹)).measurableEmbedding
  unfold jtR
  rw [hb']
  have hint : ∀ Y, Φv Y * ψR (trPair (Fv F v) ((C)ᵀ * (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (1 + x))
      (gramR (Fv F v) σ J Y)) =
      (fun Z => Φv Z * ψR (trPair (Fv F v) (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Z))) (e Y) := by
    intro Y
    show _ = Φv (rowMix C Y) * _
    rw [hΦC, hCdef, trPair_conj (Fv F v) σ hcm J (1 + x) b Y]
    rfl
  simp_rw [hint]
  exact hmp.integral_comp hemb (fun Z => Φv Z * ψR (trPair (Fv F v) (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Z)))

end PositivityTheory.SiegelWeilFormula.SwLocFin.SwSplit

end
