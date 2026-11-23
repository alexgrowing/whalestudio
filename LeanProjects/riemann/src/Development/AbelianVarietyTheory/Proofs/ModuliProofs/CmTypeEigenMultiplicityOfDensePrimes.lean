import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TraceSpread

variable {E : Type} [Field E] [NumberField E]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.TraceSpread.isSplitting_embeddings (K : Type) [Field K] [IsAlgClosed K]
    [CharZero K] :
    _root_.GlobalTheory.EigenSplit.IsSplitting fun φ : E →+* K => φ.comp (algebraMap (𝓞 E) E) := by
  have hinj : Function.Injective fun φ : E →+* K => φ.comp (algebraMap (𝓞 E) E) :=
    fun φ ψ h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  have hdisc : IsUnit ((NumberField.discr E : ℤ) : K) :=
    (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E)).isUnit
  simpa using _root_.GlobalTheory.EigenSplit.isSplitting_of_isDomain (R := K) hinj (Embeddings.card E K)
    (RingHom.id K) hdisc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
private lemma ringOfIntegers_ringHom_injective' {K : Type} [Field K] [CharZero K]
    (τ : 𝓞 E →+* K) : Function.Injective τ := by
  refine (injective_iff_map_eq_zero τ).mpr fun a ha => ?_
  by_contra hne
  have haE : (a : E) ≠ 0 := by
    intro h; exact hne (RingOfIntegers.coe_injective (h.trans (map_zero (algebraMap (𝓞 E) E)).symm))
  obtain ⟨z, hz, h⟩ := exists_integral_multiples ℤ ℚ ({(a : E)⁻¹} : Finset E)
  let c : 𝓞 E := ⟨z • (a : E)⁻¹, h _ (Finset.mem_singleton_self _)⟩
  have hzc : (z : 𝓞 E) = a * c := by
    apply RingOfIntegers.coe_injective
    show ((z : 𝓞 E) : E) = (a : E) * (z • (a : E)⁻¹)
    rw [zsmul_eq_mul, mul_left_comm, mul_inv_cancel₀ haE, _root_.mul_one]
    simp
  have : τ (z : 𝓞 E) = 0 := by rw [hzc, map_mul, ha, zero_mul]
  rw [map_intCast] at this
  exact hz (Int.cast_eq_zero.mp this)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.TraceSpread.exists_embedding {K : Type} [Field K] [CharZero K]
    (τ : 𝓞 E →+* K) :
    ∃ φ : E →+* K, φ.comp (algebraMap (𝓞 E) E) = τ := by
  refine ⟨IsFractionRing.lift (ringOfIntegers_ringHom_injective' τ), ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (ringOfIntegers_ringHom_injective' τ) a

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.TraceSpread.trace_eq_sum {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {V : Type} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (ρ : 𝓞 E →+* Module.End K V) (a : 𝓞 E) :
    LinearMap.trace K V (ρ a) = ∑ φ : E →+* K,
      (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : K) *
        φ a := by
  classical
  have hsplit := _root_.GlobalTheory.TraceSpread.isSplitting_embeddings (E := E) K
  have hint := _root_.GlobalTheory.EigenSplit.isInternal_eigenSub hsplit ρ
  have hmaps : ∀ φ : E →+* K, Set.MapsTo (ρ a)
      (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
      (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) :=
    fun φ x hx => _root_.GlobalTheory.EigenSplit.apply_mem_eigenSub hx a
  rw [LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  refine Finset.sum_congr rfl fun φ _ => ?_
  have hres : (ρ a).restrict (hmaps φ) = (φ a) • LinearMap.id := by
    ext x
    show ρ a (x : V) = φ (a : E) • (x : V)
    exact (_root_.GlobalTheory.EigenSplit.mem_eigenSub.mp x.2) a
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.TraceSpread.map_trace {R K : Type} [CommRing R] [CommRing K]
    {n : ℕ} (f : R →+* K) (A : Module.End R (Fin n → R))
    (A' : Module.End K (Fin n → K)) (h : ∀ c, f ∘ A c = A' (f ∘ c)) :
    f (LinearMap.trace R _ A) = LinearMap.trace K _ A' := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin n)),
    LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n)), Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  have hc : (f ∘ (Pi.single i 1 : Fin n → R)) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [← hc, ← h]
  rfl

variable [IsCMField E]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
private lemma intTrace_cast_eq_sum_embeddings {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (a : 𝓞 E) :
    ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K) = ∑ φ : E →+* K, φ a := by
  have h₁ := Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E) a
  have h₂ := trace_eq_sum_embeddings (K := ℚ) (L := E) K (x := (a : E))
  calc ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K)
      = algebraMap ℚ K (algebraMap ℤ ℚ (Algebra.intTrace ℤ (𝓞 E) a)) := by simp
    _ = algebraMap ℚ K (Algebra.trace ℚ E (algebraMap (𝓞 E) E a)) := by rw [h₁]
    _ = ∑ σ : E →ₐ[ℚ] K, σ (a : E) := h₂
    _ = ∑ φ : E →+* K, φ a :=
      (Fintype.sum_equiv (RingHom.equivRatAlgHom E K) _ _ fun φ => rfl).symm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
variable [IsCMField E] in

theorem _root_.GlobalTheory.TraceSpread.finrank_iff_trace (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) {K : Type} [Field K]
    [IsAlgClosed K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [Module.Finite K V] (ρ : 𝓞 E →+* Module.End K V) (s : K)
    (hs : s ^ 2 = -(H.d : K)) :
    (∀ τ : 𝓞 E →+* K, (τ H.rt = s → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ τ) = p) ∧
      (τ H.rt ≠ s → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ τ) = q)) ↔
    ∀ a, 2 * s * LinearMap.trace K V (ρ a) =
      (p + q) * s * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K) +
      (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : K) := by
  have hroot : ∀ τ : 𝓞 E →+* K, τ H.rt = s ∨ τ H.rt = -s := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [hs, ← map_pow, H.rt_sq, map_neg, map_natCast]
  have hs0 : s ≠ 0 := by
    rintro rfl
    have hd : (H.d : K) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
    apply hd
    have := hs
    rw [zero_pow two_ne_zero] at this
    exact neg_eq_zero.mp this.symm
  constructor
  · intro hmult a
    rw [_root_.GlobalTheory.TraceSpread.trace_eq_sum, intTrace_cast_eq_sum_embeddings,
      intTrace_cast_eq_sum_embeddings, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [show ((H.rt * a : 𝓞 E) : E) = (H.rt : E) * (a : E) from map_mul (algebraMap (𝓞 E) E) _ _,
      map_mul]
    rcases hroot (φ.comp (algebraMap (𝓞 E) E)) with h | h
    · rw [(hmult _).1 h]
      have h' : φ (H.rt : E) = s := h
      rw [h']
      ring
    · have hne : (φ.comp (algebraMap (𝓞 E) E)) H.rt ≠ s := by
        rw [h]; intro h'; exact hs0 (by linear_combination -h' / 2)
      rw [(hmult _).2 hne]
      have h' : φ (H.rt : E) = -s := h
      rw [h']
      ring
  · intro hid τ
    obtain ⟨φ, rfl⟩ := _root_.GlobalTheory.TraceSpread.exists_embedding τ
    let c : (E →+* K) → K := fun ψ =>
      2 * s * (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (ψ.comp (algebraMap (𝓞 E) E))) : K) -
        ((p + q) * s + (p - q) * ψ (H.rt : E))
    have hli := (linearIndependent_monoidHom (𝓞 E) K).comp
      (fun ψ : E →+* K => ((ψ.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* K) : 𝓞 E →* K))
      (fun ψ₁ ψ₂ h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        (RingHom.ext fun x => DFunLike.congr_fun h x))
    have hc : c φ = 0 := by
      refine Fintype.linearIndependent_iff.mp hli c ?_ φ
      funext a
      rw [Finset.sum_apply, Pi.zero_apply]
      have h₁ := hid a
      rw [_root_.GlobalTheory.TraceSpread.trace_eq_sum, intTrace_cast_eq_sum_embeddings,
        intTrace_cast_eq_sum_embeddings, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun ψ _ => ?_) h₁
      change c ψ * ψ (a : E) = _
      rw [show ((H.rt * a : 𝓞 E) : E) = (H.rt : E) * (a : E) from map_mul (algebraMap (𝓞 E) E) _ _,
        map_mul]
      simp only [c]
      ring
    have hd2 : (2 : K) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
    simp only [c, sub_eq_zero] at hc
    constructor
    · intro h
      have h' : φ (H.rt : E) = s := h
      rw [h'] at hc
      have hm : (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : K)
          = p := mul_left_cancel₀ hd2 (by linear_combination hc)
      exact_mod_cast hm
    · intro h
      have h'' := (hroot (φ.comp (algebraMap (𝓞 E) E))).resolve_left h
      have h' : φ (H.rt : E) = -s := h''
      rw [h'] at hc
      have hm : (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : K)
          = q := mul_left_cancel₀ hd2 (by linear_combination hc)
      exact_mod_cast hm

end GlobalTheory.TraceSpread

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.eigenMult_of_dense : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R]
    (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) →
    Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K)
      (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧
      (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K,
        (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
        (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q)} →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K)
      (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) →
      ∀ τ : 𝓞 E →+* K,
        (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
        (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by
  intro E _ _ _ H p q n R _ _ M r hr hdense K _ _ _ f M' hfM
  let X : 𝓞 E → R := fun a => 2 * r * LinearMap.trace R _ (M a) -
    ((p + q) * r * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : R) +
      (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : R))
  have hfX : ∀ (K₁ : Type) [Field K₁] (f₁ : R →+* K₁)
      (M₁ : 𝓞 E →+* Module.End K₁ (Fin n → K₁)), (∀ a c, f₁ ∘ M a c = M₁ a (f₁ ∘ c)) →
      ∀ a, f₁ (X a) = 2 * f₁ r * LinearMap.trace K₁ _ (M₁ a) -
        ((p + q) * f₁ r * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K₁) +
          (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : K₁)) := by
    intro K₁ _ f₁ M₁ h₁ a
    simp only [X, map_sub, map_add, map_mul, map_natCast, map_intCast, map_ofNat]
    rw [_root_.GlobalTheory.TraceSpread.map_trace f₁ (M a) (M₁ a) (h₁ a)]
  have hX : ∀ a, X a = 0 := by
    intro a
    have hsub : {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K)
        (_ : CharZero K) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)),
        RingHom.ker f = P.asIdeal ∧ (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K,
          (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
          (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q)} ⊆
        PrimeSpectrum.zeroLocus {X a} := by
      rintro P ⟨K₁, _, _, _, f₁, M₁, hker, hcomp, hmult⟩
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, ← hker,
        RingHom.mem_ker, hfX K₁ f₁ M₁ hcomp a]
      have hs : f₁ r ^ 2 = -(H.d : K₁) := by rw [← map_pow, hr, map_neg, map_natCast]
      have := (_root_.GlobalTheory.TraceSpread.finrank_iff_trace H p q M₁ (f₁ r) hs).mp hmult a
      rw [this]; ring
    have hall := closure_minimal hsub (PrimeSpectrum.isClosed_zeroLocus _)
    rw [hdense.closure_eq] at hall
    have hnil : IsNilpotent (X a) := nilpotent_iff_mem_prime.mpr fun J hJ => by
      have := hall (Set.mem_univ ⟨J, hJ⟩)
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at this
      exact this
    exact hnil.eq_zero
  have hs : f r ^ 2 = -(H.d : K) := by rw [← map_pow, hr, map_neg, map_natCast]
  refine (_root_.GlobalTheory.TraceSpread.finrank_iff_trace H p q M' (f r) hs).mpr fun a => ?_
  have h₀ := hfX K f M' hfM a
  rw [hX a, map_zero] at h₀
  linear_combination -h₀
