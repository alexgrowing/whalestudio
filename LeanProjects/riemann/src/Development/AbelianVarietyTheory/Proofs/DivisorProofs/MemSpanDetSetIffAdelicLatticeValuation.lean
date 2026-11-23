import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.AdelicDetSpan

variable {E : Type} [Field E] [NumberField E]

noncomputable def comp (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem comp_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    comp P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem val_det_le_one {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  let N : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨M i j, h i j⟩
  have e : M = v.integer.subtype.mapMatrix N := rfl
  rw [e, ← RingHom.map_det]
  exact N.det.2

theorem exists_clear (Q : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hy : Valued.v (comp Q y) ≤ 1) :
    ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      P.valuation E (b : E) * Valued.v (comp P y) ≤ 1 := by
  classical
  have hloc : ∀ P : HeightOneSpectrum (𝓞 E), ∃ c : 𝓞 E, c ∉ Q.asIdeal ∧
      P.valuation E (c : E) * Valued.v (comp P y) ≤ 1 := by
    intro P
    by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, by simpa using h1⟩
    have hPQ : P ≠ Q := by rintro rfl; exact h1 hy
    have hnle : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      hPQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hnle
    have hlt : P.valuation E (a : E) < 1 := (P.valuation_lt_one_iff_mem (K := E) a).2 haP
    have h0 : Valued.v (comp P y) ≠ 0 := by
      intro h; rw [h] at h1; exact h1 zero_le_one
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ h0)⁻¹
    refine ⟨a ^ m, fun h => haQ (Q.isPrime.mem_of_pow_mem m h), ?_⟩
    have : ((a ^ m : 𝓞 E) : E) = (a : E) ^ m := by simp
    rw [this, map_pow]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
    calc _ ≤ (Valued.v (comp P y))⁻¹ * Valued.v (comp P y) := mul_le_mul' hm.le le_rfl
      _ = 1 := inv_mul_cancel₀ h0
  choose c hcQ hc using hloc
  have hfin : {P : HeightOneSpectrum (𝓞 E) | ¬ Valued.v (comp P y) ≤ 1}.Finite :=
    Filter.eventually_cofinite.1 y.2
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  refine ⟨∏ P ∈ hfin.toFinset, c P, ?_, fun P => ?_⟩
  · rw [Q.isPrime.prod_mem_iff]
    rintro ⟨P, -, h⟩
    exact hcQ P h
  · by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact mul_le_one' (hle _ _) h1
    · have hm : P ∈ hfin.toFinset := by simpa using h1
      rw [← Finset.prod_erase_mul _ _ hm]
      have : (((∏ x ∈ hfin.toFinset.erase P, c x) * c P : 𝓞 E) : E) =
        ((∏ x ∈ hfin.toFinset.erase P, c x : 𝓞 E) : E) * (c P : E) := by push_cast; rfl
      rw [this, map_mul, mul_assoc]
      exact mul_le_one' (hle _ _) (hc P)

theorem exists_approx_matrix (Q : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) (hg : h * g = 1) :
    ∃ X : Matrix (Fin n) (Fin n) E,
      (∀ i j, Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j) ≤ 1) ∧
      Valued.v (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det = 1 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => Pi.map fun _ : Fin n =>
      (algebraMap E (Q.adicCompletion E) : E → _)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) Q
  have hc : Continuous fun X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) => h * X :=
    continuous_const.matrix_mul continuous_id
  have hb : IsOpen {z : Q.adicCompletion E | Valued.v z < 1} := by
    have h := Valued.isOpen_ball (Q.adicCompletion E) 1
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff_lt_embedding]
  have hU : IsOpen {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
      (∀ i j, Valued.v ((h * X - 1) i j) < 1) ∧ Valued.v ((h * X).det - 1) < 1} := by
    refine IsOpen.inter ?_ (hb.preimage (hc.matrix_det.sub continuous_const))
    have : IsOpen (⋂ i, ⋂ j, {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
        Valued.v ((h * X - 1) i j) < 1}) :=
      isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hb.preimage ((hc.sub continuous_const).matrix_elem i j)
    simp only [← Set.setOf_forall] at this
    exact this
  obtain ⟨X, h1, h2⟩ := hd.exists_mem_open hU ⟨g, ⟨fun i j => by rw [hg]; simp, by rw [hg]; simp⟩⟩
  refine ⟨X, fun i j => ?_, ?_⟩
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j) < 1 := h1 i j
    have e : (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j =
        (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j +
          (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by simp
    rw [e]
    refine Valuation.map_add_le _ h3.le ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det - 1) < 1 := h2
    have := Valuation.map_eq_of_sub_lt Valued.v (x := (1 : Q.adicCompletion E)) (by rw [map_one]; exact h3)
    rwa [map_one] at this

theorem comp_mulVec {n : ℕ} (h : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
    (X : Matrix (Fin n) (Fin n) E) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    comp P (h.mulVec (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) =
      ((comp P).mapMatrix h * (algebraMap E (P.adicCompletion E)).mapMatrix X) i j := by
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, comp_alg]

theorem mem_span_detSet_iff : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  intro E _ _ n g L hL x
  classical
  have hL' : ∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
      Valued.v (comp Q ((g⁻¹).1.mulVec
        (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i)) ≤ 1 := hL
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  have hhg : ∀ Q : HeightOneSpectrum (𝓞 E),
      (comp Q).mapMatrix (g⁻¹).1 * (comp Q).mapMatrix g.1 = 1 := fun Q => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hdet : ∀ (Q : HeightOneSpectrum (𝓞 E)) (X : Matrix (Fin n) (Fin n) E),
      Q.valuation E X.det = Valued.v (comp Q g.1.det) *
        Valued.v ((comp Q).mapMatrix (g⁻¹).1 *
          (algebraMap E (Q.adicCompletion E)).mapMatrix X).det := fun Q X => by
    rw [← map_mul, RingHom.map_det, ← Matrix.det_mul, ← mul_assoc, ← map_mul, Units.mul_inv,
      map_one, one_mul, ← RingHom.map_det, val_alg]
  show _ ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (comp Q g.1.det)
  constructor
  · intro hx Q
    induction hx using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨v, hv, rfl⟩ := hd
      rw [hdet]
      refine mul_le_of_le_one_right' (val_det_le_one _ _ fun i j => ?_)
      rw [← comp_mulVec]
      exact (hL' _).1 (hv j) i Q
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul a b _ hb =>
      have e : a • b = (a : E) * b := rfl
      rw [e, map_mul]
      exact (mul_le_of_le_one_left' (hle Q a)).trans hb
  · intro hx
    have hloc : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧
        b • x ∈ Submodule.span (𝓞 E) (detSet L) := by
      intro Q
      obtain ⟨X, hX1, hX2⟩ := exists_approx_matrix Q _ _ (hhg Q)
      choose c hcQ hc using fun i j => exists_clear Q ((g⁻¹).1.mulVec
        (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i)
        (by rw [comp_mulVec]; exact hX1 i j)
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, b = ∏ p : Fin n × Fin n, c p.1 p.2 := ⟨_, rfl⟩
      have hbQ : b ∉ Q.asIdeal := by
        rw [hb, Q.isPrime.prod_mem_iff]
        rintro ⟨p, -, h⟩
        exact hcQ _ _ h
      have hb1 : Q.valuation E (b : E) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) Q (r := b)).2 hbQ
      have hbc : ∀ i j (P : HeightOneSpectrum (𝓞 E)),
          P.valuation E (b : E) ≤ P.valuation E (c i j : E) := by
        intro i j P
        obtain ⟨t, ht⟩ : c i j ∣ b := hb ▸ Finset.dvd_prod_of_mem
          (fun p : Fin n × Fin n => c p.1 p.2) (Finset.mem_univ (i, j))
        have : (b : E) = (c i j : E) * (t : E) := by rw [ht]; push_cast; rfl
        rw [this, map_mul]
        exact mul_le_of_le_one_right' (hle P t)
      have hd : ((b : E) • X).det ∈ detSet L := by
        refine ⟨fun j i => (b : E) * X i j, fun j => (hL' _).2 fun i P => ?_, rfl⟩
        have e : comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) ((b : E) * X k j)) i) =
            algebraMap E _ (b : E) * comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) := by
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, comp_alg, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [e, map_mul, val_alg]
        exact (mul_le_mul' (hbc i j P) le_rfl).trans (hc i j P)
      have hdv : Q.valuation E ((b : E) • X).det = Valued.v (comp Q g.1.det) := by
        rw [Matrix.det_smul, map_mul, map_pow, hb1, one_pow, one_mul, hdet, hX2, mul_one]
      obtain ⟨d, hdd⟩ : ∃ d, d = ((b : E) • X).det := ⟨_, rfl⟩
      rw [← hdd] at hd hdv
      have hg0 : Valued.v (comp Q g.1.det) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 ((g.isUnit.map Matrix.detMonoidHom).map (comp Q)).ne_zero
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [map_zero] at hdv
        exact hg0 hdv.symm
      obtain ⟨s, hsQ, hs⟩ := exists_clear Q (algebraMap E _ (x / d)) (by
        rw [comp_alg, val_alg, map_div₀, hdv]
        exact (div_le_one₀ (zero_lt_iff.2 hg0)).2 (hx Q))
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
        ((s : E) * (x / d)) (fun P => by
          have := hs P
          rwa [comp_alg, val_alg, ← map_mul] at this)
      refine ⟨s, hsQ, ?_⟩
      have e : s • x = a • d := by
        have e1 : s • x = (s : E) * x := rfl
        have e2 : a • d = algebraMap (𝓞 E) E a * d := rfl
        rw [e1, e2, ha]
        field_simp
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hd)
    let I : Ideal (𝓞 E) := (Submodule.span (𝓞 E) (detSet L)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E x)
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
      have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
      obtain ⟨b, hb, hbx⟩ := hloc ⟨M, hM.isPrime, hM0⟩
      exact hb (hIM hbx)
    have h1 : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 E) • x ∈ Submodule.span (𝓞 E) (detSet L) := h1
    rwa [one_smul] at h2

end GlobalTheory.AdelicDetSpan
