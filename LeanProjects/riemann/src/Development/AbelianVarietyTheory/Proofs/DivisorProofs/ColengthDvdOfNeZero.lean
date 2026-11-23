import Mathlib

open NumberField

namespace GlobalTheory.ColengthDifferent

section

variable {E : Type} [Field E] [NumberField E]

theorem injective_of_charZero {F : Type} [Field F] [CharZero F] (f : 𝓞 E →+* F) :
    Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [RingHom.comap_ker]
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro n hn
  have : f.comp (algebraMap ℤ (𝓞 E)) = Int.castRingHom F := RingHom.ext_int _ _
  rw [this] at hn
  simpa using hn

theorem traceDual_mem_one (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).traceDual k ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_traceDual]
  intro a ha
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
  have h := ((integralBasis E).traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E y) k
  rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply] at h
  rw [Algebra.traceForm_apply, mul_comm, ← Algebra.traceForm_apply, ← h]
  exact ⟨_, rfl⟩

theorem exists_mul_traceDual {δ : 𝓞 E} (hδ : δ ∈ differentIdeal ℤ (𝓞 E))
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E δ * (integralBasis E).traceDual k := by
  have h1 : (δ : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).mpr ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ] at h1
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp ((Submodule.mem_div_iff_forall_mul_mem.mp h1) _ (traceDual_mem_one k))
  exact ⟨c, hc⟩

theorem sum_eq_trace {F : Type} [Field F] [CharZero F] {ι : Type} [Fintype ι]
    (σ : ι → (E →+* F)) (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E) (x : E) :
    ∑ i, σ i x = algebraMap ℚ F (Algebra.trace ℚ E x) := by
  classical
  let K := AlgebraicClosure F
  let φ : ι → (E →ₐ[ℚ] K) := fun i => ((algebraMap F K).comp (σ i)).toRatAlgHom
  have hφ : Function.Injective φ := by
    intro i j h
    apply hσ
    ext y
    exact (algebraMap F K).injective (congrArg (fun f : E →ₐ[ℚ] K => f y) h)
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hφ, by rw [hc, AlgHom.card]⟩
  apply (algebraMap F K).injective
  rw [map_sum, ← IsScalarTower.algebraMap_apply ℚ F K, trace_eq_sum_embeddings K]
  exact hbij.sum_comp (fun f : E →ₐ[ℚ] K => f x)

theorem mul_dual_expand {c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E} {δ : 𝓞 E}
    (hc : ∀ k, algebraMap (𝓞 E) E (c k) = algebraMap (𝓞 E) E δ * (integralBasis E).traceDual k)
    (a : 𝓞 E) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    a * c l = ∑ k, (RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l • c k := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  set b := integralBasis E
  set ω := RingOfIntegers.basis E
  rw [map_mul, hc, map_sum]
  have hrepr : ∀ k, algebraMap (𝓞 E) E ((ω.repr (a * ω k) l) • c k) =
      (b.traceDual.repr (algebraMap (𝓞 E) E a * b.traceDual l) k) •
        (algebraMap (𝓞 E) E δ * b.traceDual k) := by
    intro k
    rw [map_zsmul, hc, ← Int.cast_smul_eq_zsmul ℚ]
    congr 1
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
    have h := (b.traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E (a * ω k)) l
    rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply, Algebra.traceForm_apply] at h
    have hb : b k = algebraMap (𝓞 E) E (ω k) := integralBasis_apply E k
    rw [← eq_intCast (algebraMap ℤ ℚ), h, hb]
    congr 1
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl fun k _ => hrepr k]
  simp_rw [← mul_smul_comm, ← Finset.mul_sum]
  rw [b.traceDual.sum_repr]
  ring

theorem mul_proj {T : Type} [CommRing T] (t : 𝓞 E →+* T) {R : Type} [Ring R] [Algebra T R]
    (A : 𝓞 E →+* R) {c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E} {δ : 𝓞 E}
    (hc : ∀ k, algebraMap (𝓞 E) E (c k) = algebraMap (𝓞 E) E δ * (integralBasis E).traceDual k)
    (a : 𝓞 E) :
    A a * ∑ k, t (c k) • A (RingOfIntegers.basis E k) =
      t a • ∑ k, t (c k) • A (RingOfIntegers.basis E k) := by
  set ω := RingOfIntegers.basis E
  have h1 : ∀ l, t (a * c l) • A (ω l) = ∑ k, (ω.repr (a * ω k) l) • (t (c k) • A (ω l)) := by
    intro l
    rw [mul_dual_expand hc, map_sum, Finset.sum_smul]
    simp only [map_zsmul, smul_assoc]
    rfl
  calc A a * ∑ k, t (c k) • A (ω k) = ∑ k, t (c k) • A (a * ω k) := by
        rw [Finset.mul_sum]; simp only [mul_smul_comm, map_mul]
    _ = ∑ k, ∑ l, (ω.repr (a * ω k) l) • (t (c k) • A (ω l)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        conv_lhs => rw [← ω.sum_repr (a * ω k)]
        rw [map_sum, Finset.smul_sum]
        simp only [map_zsmul, smul_comm (t (c k))]
    _ = ∑ l, t (a * c l) • A (ω l) := by rw [Finset.sum_comm]; simp only [h1]
    _ = t a • ∑ k, t (c k) • A (ω k) := by rw [Finset.smul_sum]; simp only [map_mul, mul_smul]

theorem sum_proj_eq_one {F : Type} [Field F] [CharZero F] {ι : Type} [Fintype ι]
    (σ : ι → (E →+* F)) (hσ : Function.Injective σ) (hcard : Fintype.card ι = Module.finrank ℚ E)
    {R : Type} [Ring R] [Algebra F R] (A : 𝓞 E →+* R)
    (δ : ι → 𝓞 E) (hδ0 : ∀ i, δ i ≠ 0) (c : ι → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E)
    (hc : ∀ i k, algebraMap (𝓞 E) E (c i k) =
      algebraMap (𝓞 E) E (δ i) * (integralBasis E).traceDual k) :
    ∑ i, (σ i (algebraMap (𝓞 E) E (δ i)))⁻¹ •
      ∑ k, σ i (algebraMap (𝓞 E) E (c i k)) • A (RingOfIntegers.basis E k) = 1 := by
  set b := integralBasis E
  set ω := RingOfIntegers.basis E
  have hd : ∀ i, σ i (algebraMap (𝓞 E) E (δ i)) ≠ 0 := fun i => by
    rw [map_ne_zero_iff _ (σ i).injective]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mpr (hδ0 i)
  have h1 : ∀ i, (σ i (algebraMap (𝓞 E) E (δ i)))⁻¹ •
      ∑ k, σ i (algebraMap (𝓞 E) E (c i k)) • A (ω k) = ∑ k, σ i (b.traceDual k) • A (ω k) := by
    intro i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc, map_mul, smul_smul, ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  have htr : ∀ k, ∑ i, σ i (b.traceDual k) = ((ω.repr 1 k : ℤ) : F) := by
    intro k
    rw [sum_eq_trace σ hσ hcard]
    have h := (b.traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E 1) k
    rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply, Algebra.traceForm_apply,
      RingHom.map_one (algebraMap (𝓞 E) E), one_mul] at h
    rw [← h]
    rw [eq_intCast, eq_ratCast, Rat.cast_intCast]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, htr, Int.cast_smul_eq_zsmul, ← map_zsmul, ← map_sum, ω.sum_repr, map_one]

theorem colength_dvd_of_ne_zero (F T : Type) [Field F] [CharZero F] [CommRing T] [IsDomain T]
    [Algebra T F] [IsFractionRing T F] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι → (𝓞 E →+* T))
    (m : ι → ℕ) (g : ℕ) (e : Fin g ≃ Σ i : ι, Fin (m i)) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T)
    (u : ∀ i, Fin (m i) → (Fin g → T)) (hτ : Function.Injective τ)
    (hcard : Fintype.card ι = Module.finrank ℚ E)
    (hsp : ∀ i (w : Fin g → T), (∀ a, (A a).mulVec w = τ i a • w) →
      ∃ cf : Fin (m i) → T, w = ∑ k, cf k • u i k)
    (δ : ι → 𝓞 E) (hδ : ∀ i, δ i ∈ differentIdeal ℤ (𝓞 E)) (hδ0 : ∀ i, δ i ≠ 0) :
    (Matrix.of fun j k : Fin g => u (e j).1 (e j).2 k).det ∣ ∏ i, τ i (δ i) ^ m i := by
  classical
  set ω := RingOfIntegers.basis E
  choose c hc using fun i k => exists_mul_traceDual (hδ i) k
  let P : ι → Matrix (Fin g) (Fin g) T := fun i => ∑ k, τ i (c i k) • A (ω k)
  have hPv : ∀ i j a, (A a).mulVec ((P i).mulVec (Pi.single j 1)) =
      τ i a • (P i).mulVec (Pi.single j 1) := by
    intro i j a
    rw [Matrix.mulVec_mulVec, mul_proj (τ i) A (hc i) a, Matrix.smul_mulVec]
  choose cf hcf using fun i j => hsp i _ (hPv i j)
  have hF := IsFractionRing.injective T F
  let g' : ι → 𝓞 E →+* F := fun i => (algebraMap T F).comp (τ i)
  have hg' : ∀ i, Function.Injective (g' i) := fun i => injective_of_charZero _
  let σ : ι → E →+* F := fun i => IsFractionRing.lift (hg' i)
  have hσ : ∀ i x, σ i (algebraMap (𝓞 E) E x) = algebraMap T F (τ i x) :=
    fun i x => IsFractionRing.lift_algebraMap _ _
  have hσinj : Function.Injective σ := by
    intro i j h
    apply hτ
    ext x
    apply hF
    rw [← hσ, ← hσ, h]
  let AF : 𝓞 E →+* Matrix (Fin g) (Fin g) F := (algebraMap T F).mapMatrix.comp A
  have hone := sum_proj_eq_one σ hσinj hcard AF δ hδ0 c hc
  simp only [hσ] at hone
  have hPF : ∀ i, (P i).map (algebraMap T F) = ∑ k, algebraMap T F (τ i (c i k)) • AF (ω k) := by
    intro i
    ext r s
    simp only [P]
    rw [Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, AF, RingHom.comp_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply]
  set d : ι → F := fun i => algebraMap T F (τ i (δ i)) with hd_def
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    simp only [hd_def]
    rw [← hσ, map_ne_zero_iff _ (σ i).injective]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mpr (hδ0 i)
  have hent : ∀ r s, ∑ i, (d i)⁻¹ * algebraMap T F (P i r s) = (1 : Matrix (Fin g) (Fin g) F) r s := by
    intro r s
    rw [← hone, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, ← hPF, Matrix.map_apply, smul_eq_mul]
  have hcol : ∀ i j k, P i k j = ∑ l, cf i j l * u i l k := by
    intro i j k
    have := congrFun (hcf i j) k
    rw [Matrix.mulVec_single_one] at this
    simpa [Finset.sum_apply] using this
  set G : Matrix (Fin g) (Fin g) T := Matrix.of fun j r => cf (e r).1 j (e r).2 with hG
  set U : Matrix (Fin g) (Fin g) T := Matrix.of fun r k => u (e r).1 (e r).2 k with hU
  have hmat : G.map (algebraMap T F) * Matrix.diagonal (fun r => (d (e r).1)⁻¹) *
      U.map (algebraMap T F) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.map_apply, hG, hU, Matrix.of_apply]
    rw [Equiv.sum_comp e (fun x => algebraMap T F (cf x.1 j x.2) * (d x.1)⁻¹ *
      algebraMap T F (u x.1 x.2 k)), Fintype.sum_sigma]
    calc _ = ∑ i, (d i)⁻¹ * algebraMap T F (P i k j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcol, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_mul]
          ring
      _ = _ := by
          rw [hent, Matrix.one_apply, Matrix.one_apply]
          simp [eq_comm]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_one,
    ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det,
    Finset.prod_inv_distrib, mul_right_comm,
    mul_inv_eq_one₀ (Finset.prod_ne_zero_iff.mpr fun r _ => hd _)] at hdet
  have hprod : ∏ r : Fin g, τ (e r).1 (δ (e r).1) = ∏ i, τ i (δ i) ^ m i := by
    rw [Equiv.prod_comp e (fun x => τ x.1 (δ x.1)), Fintype.prod_sigma]
    simp
  have hkey : G.det * U.det = ∏ i, τ i (δ i) ^ m i := by
    apply hF
    rw [← hprod, map_mul, map_prod, hdet]
  exact Dvd.intro_left _ hkey

end

theorem colength_dvd : ∀ (E F T : Type) [Field E] [NumberField E] [Field F] [CharZero F] [CommRing T] [IsDomain T] [Algebra T F] [IsFractionRing T F] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι → (𝓞 E →+* T)) (m : ι → ℕ) (g : ℕ) (e : Fin g ≃ Σ i : ι, Fin (m i)) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T) (u : ∀ i, Fin (m i) → (Fin g → T)), Function.Injective τ → Fintype.card ι = Module.finrank ℚ E → IsIntegrallyClosed T → (∀ i (w : Fin g → T), (∀ a, (A a).mulVec w = τ i a • w) → ∃ cf : Fin (m i) → T, w = ∑ k, cf k • u i k) → (∀ i k a, (A a).mulVec (u i k) = τ i a • u i k) → ∀ δ : ι → 𝓞 E, (∀ i, δ i ∈ differentIdeal ℤ (𝓞 E)) → (Matrix.of fun j k : Fin g => u (e j).1 (e j).2 k).det ∣ ∏ i, τ i (δ i) ^ m i := by
  intro E F T _ _ _ _ _ _ _ _ ι _ _ τ m g e A u hτ hcard _ hsp _ δ hδ
  classical
  by_cases hz : ∃ i, δ i = 0 ∧ m i ≠ 0
  · obtain ⟨i, hi, hm⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, map_zero, zero_pow hm])]
    exact dvd_zero _
  · push Not at hz
    obtain ⟨δ₀, hδ₀, hδ₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
    let δ' : ι → 𝓞 E := fun i => if δ i = 0 then δ₀ else δ i
    have h := colength_dvd_of_ne_zero F T ι τ m g e A u hτ hcard hsp δ'
      (fun i => by simp only [δ']; split_ifs; exacts [hδ₀, hδ i])
      (fun i => by simp only [δ']; split_ifs with h; exacts [hδ₀0, h])
    have hp : ∏ i, τ i (δ i) ^ m i = ∏ i, τ i (δ' i) ^ m i :=
      Finset.prod_congr rfl fun i _ => by
        by_cases h0 : δ i = 0
        · rw [hz i h0, pow_zero, pow_zero]
        · simp only [δ', if_neg h0]
    rw [hp]
    exact h

end GlobalTheory.ColengthDifferent
