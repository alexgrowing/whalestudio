import ReciprocityTheory.SemistableReduction.SemiDegT

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def IsAt {K : Type} [Field K] {r : ℕ} (i : Fin r) (x : Fin r → K) : Prop :=
  ∀ a, a ≠ i → x a = 0

theorem gramC_single {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ)
    (σ : K →+* ℂ) (i : Fin r) (x : Fin r → K) (hx : IsAt i x) :
    (gramC (diagMet δ σ) σ ![x]).det.re = ‖σ (x i)‖ ^ 2 * δ σ i := by
  rw [Matrix.det_unique]
  simp only [gramC, Matrix.of_apply, embVec, diagMet, Matrix.mulVec_diagonal, dotProduct,
    Pi.star_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Fin.default_eq_zero, Matrix.cons_val_zero]
    rw [show star (σ (x i)) * (((δ σ i : ℝ) : ℂ) * σ (x i)) =
        ((δ σ i : ℝ) : ℂ) * (starRingEnd ℂ (σ (x i)) * σ (x i)) by
      rw [Complex.star_def]; ring]
    rw [Complex.conj_mul']
    simp only [Complex.re_ofReal_mul]
    norm_cast
    ring
  · intro a _ ha
    simp [Fin.default_eq_zero, hx a ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem latDeg_single {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (C : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (x : Fin r → K)
    (hx : IsAt i x) :
    latDeg (diagMet δ) C ![x] = Real.log (spanIdx C ![x] : ℝ) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (‖σ (x i)‖ ^ 2 * δ σ i) := by
  unfold latDeg spanIdx
  congr 2
  exact Finset.sum_congr rfl fun σ _ => by rw [gramC_single δ σ i x hx]

theorem sum_log_single {K : Type} [Field K] [NumberField K] (z : K) (hz : z ≠ 0) (d : ℝ)
    (hd : 0 < d) :
    ∑ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) =
      2 * Real.log |((Algebra.norm ℚ z : ℚ) : ℝ)| + (Fintype.card (K →+* ℂ) : ℝ) * Real.log d := by
  have h1 : ∀ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) = 2 * Real.log ‖σ z‖ + Real.log d := by
    intro σ
    have : ‖σ z‖ ≠ 0 := by simpa using hz
    rw [Real.log_mul (pow_ne_zero 2 this) hd.ne', Real.log_pow]
    push_cast
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_emb, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

theorem kBasisIn_single {K : Type} [Field K] [NumberField K] {r : ℕ} (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hat : ∀ x ∈ Gr, IsAt i x) (v : Fin r → K)
    (hv : v ∈ Gr) (hvi : v i ≠ 0) : IsKBasisIn Gr ![v] := by
  have hv0 : v ≠ 0 := fun h => hvi (by rw [h]; rfl)
  refine ⟨fun j => by fin_cases j; simpa using hv, ?_, ?_⟩
  · exact linearIndependent_unique_iff.2 (by simpa using hv0)
  · intro x hx
    rw [Set.range_unique, Submodule.mem_span_singleton]
    refine ⟨x i / v i, ?_⟩
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, Fin.default_eq_zero, Matrix.cons_val_zero]
    by_cases ha : a = i
    · subst ha
      field_simp
    · rw [hat x hx a ha, hat v hv a ha, mul_zero]

theorem rankOne_le_zero (hB : LatDegBasisStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hGr : Gr.FG) (hat : ∀ x ∈ Gr, IsAt i x)
    (x0 : Fin r → K) (hx0 : x0 ∈ Gr) (hx0i : x0 i ≠ 0)
    (hdeg : latDeg (diagMet δ) Gr ![x0] ≤ 0) (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gr)
    (k : ℕ) (c : Fin k → Fin r → K) (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ =>
    Matrix.posDef_diagonal_iff.2 fun a => by exact_mod_cast hδ σ a
  have hci : ∀ j, c j i ≠ 0 := by
    intro j h0
    apply hc.2.1.ne_zero j
    funext a
    by_cases ha : a = i
    · subst ha; exact h0
    · exact hat _ (hC (hc.1 j)) a ha
  match k, c, hc, hci with
  | 0, c, hc, _ => exact (latDeg_zero_fam _ _ c hc).le
  | 1, c, hc, hci =>
    have hc1 : c = ![c 0] := by funext j; fin_cases j; rfl
    have hGc : IsKBasisIn Gr c := by
      rw [hc1]
      exact kBasisIn_single i Gr hat (c 0) (hC (hc.1 0)) (hci 0)
    calc latDeg (diagMet δ) C c ≤ latDeg (diagMet δ) Gr c :=
          latDeg_le_of_le _ C Gr c hC hGr hc hGc
      _ = latDeg (diagMet δ) Gr ![x0] :=
          hB K r 1 (diagMet δ) Gr c ![x0] hpd hGr hGc (kBasisIn_single i Gr hat x0 hx0 hx0i)
      _ ≤ 0 := hdeg
  | k + 2, c, hc, hci =>
    exfalso
    have hli := hc.2.1
    let t : Fin (k + 2) → K := fun j => if j = 0 then c 1 i else if j = 1 then -(c 0 i) else 0
    have ht : ∑ j, t j • c j = 0 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h0 : ∀ j : Fin k, t j.succ.succ = 0 := fun j => by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _), if_neg]
        intro h
        exact Fin.succ_ne_zero j (Fin.succ_injective _ h)
      simp only [h0, zero_smul, Finset.sum_const_zero, add_zero]
      have t0 : t 0 = c 1 i := by simp [t]
      have t1 : t (Fin.succ 0) = -(c 0 i) := by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _)]
        rfl
      rw [t0, t1]
      funext a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases ha : a = i
      · subst ha
        simp only [Fin.succ_zero_eq_one]
        ring
      · rw [hat _ (hC (hc.1 0)) a ha, hat _ (hC (hc.1 _)) a ha]
        ring
    have := Fintype.linearIndependent_iff.1 hli t ht 1
    simp [t] at this
    exact hci 0 this

theorem relIndex_sup_proj {G : Type} [AddCommGroup G] (π : G →+ G) (A X C : AddSubgroup G)
    (hXC : X ≤ C) (hA : ∀ a ∈ A, π a = 0) (hC : ∀ x ∈ C, π x = x) :
    (A ⊔ X).relIndex (A ⊔ C) = X.relIndex C := by
  have heq : A ⊔ X = X.comap π ⊓ (A ⊔ C) := by
    apply le_antisymm
    · refine le_inf (sup_le ?_ ?_) (sup_le_sup_left hXC A)
      · intro a ha
        show π a ∈ X
        rw [hA a ha]
        exact X.zero_mem
      · intro x hx
        show π x ∈ X
        rw [hC x (hXC hx)]
        exact hx
    · rintro z ⟨hzX, hz⟩
      obtain ⟨a, ha, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hz
      have hπ : π (a + w) = w := by rw [map_add, hA a ha, hC w hw, zero_add]
      have hwX : w ∈ X := by
        have : π (a + w) ∈ X := hzX
        rwa [hπ] at this
      exact AddSubgroup.add_mem_sup ha hwX
  have hmap : (A ⊔ C).map π = C := by
    rw [AddSubgroup.map_sup]
    have h1 : A.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hA a ha]
      exact AddSubgroup.zero_mem _
    have h2 : C.map π = C := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [hC x hx]
        exact hx
      · intro x hx
        exact ⟨x, hx, hC x hx⟩
    rw [h1, h2, bot_sup_eq]
  rw [heq, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, hmap]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
