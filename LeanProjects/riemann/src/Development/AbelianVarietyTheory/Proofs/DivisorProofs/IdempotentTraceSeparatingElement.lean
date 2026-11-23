import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthDvdOfNeZero
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem exists_aut (φ₀ φ : E →+* C) : ∃ g : E ≃ₐ[ℚ] E, φ = φ₀.comp g.toRingHom := by
  let K := AlgebraicClosure C
  let ι := algebraMap C K
  let F : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] K) := fun g => ((ι.comp φ₀).comp g.toRingHom).toRatAlgHom
  have hF : Function.Injective F := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] K => f x) hgh
    simp only [F, RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
    exact φ₀.injective (ι.injective this)
  have hbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hF, ?_⟩
    rw [AlgHom.card, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  obtain ⟨g, hg⟩ := hbij.2 ((ι.comp φ).toRatAlgHom)
  refine ⟨g, ?_⟩
  ext x
  have := congrArg (fun f : E →ₐ[ℚ] K => f x) hg
  simp only [F, RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
  exact (ι.injective this).symm

theorem sum_aut_eq_trace (φ₀ : E →+* C) (x : E) :
    ∑ g : E ≃ₐ[ℚ] E, φ₀ (g x) = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  have h := GlobalTheory.ColengthDifferent.sum_eq_trace (fun g : E ≃ₐ[ℚ] E => φ₀.comp g.toRingHom) ?_
    (by rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]) x
  · simpa using h
  · intro g h hgh
    ext y
    exact φ₀.injective (RingHom.congr_fun hgh y)

theorem comp_eq_iff (φ₀ : E →+* C) (h : E ≃ₐ[ℚ] E) : φ₀.comp h.toRingHom = φ₀ ↔ h = 1 := by
  constructor
  · intro hh
    ext x
    exact φ₀.injective (RingHom.congr_fun hh x)
  · rintro rfl
    ext x
    rfl

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem map_expand (φ₀ : E →+* C) (x : E) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * algebraMap ℚ C (Algebra.trace ℚ E (integralBasis E k * x)) = φ₀ x := by
  set b := integralBasis E
  conv_rhs => rw [← b.traceDual.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul φ₀, mul_comm x (b k),
    mul_comm (φ₀ (b.traceDual k))]
  congr 1
  exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ C) (φ₀.comp (algebraMap ℚ E))) _

theorem orth_aut (φ₀ : E →+* C) (h : E ≃ₐ[ℚ] E) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * φ₀ (h (integralBasis E k)) = if h = 1 then 1 else 0 := by
  set b := integralBasis E
  let f : (E ≃ₐ[ℚ] E) → (E →* C) := fun g => (φ₀.comp g.toRingHom).toMonoidHom
  have hf : Function.Injective f := by
    intro g g' hgg
    ext y
    exact φ₀.injective (DFunLike.congr_fun hgg y)
  have li := (linearIndependent_monoidHom E C).comp f hf
  let c : (E ≃ₐ[ℚ] E) → C := fun g =>
    (∑ k, φ₀ (b.traceDual k) * φ₀ (g (b k))) - if g = 1 then 1 else 0
  have hc : ∑ g, c g • ((fun f : E →* C => (f : E → C)) ∘ f) g = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, f,
      MonoidHom.coe_coe, RingHom.coe_comp, RingHom.toMonoidHom_eq_coe]
    have e1 : ∀ g : E ≃ₐ[ℚ] E, c g * φ₀ (g x) =
        (∑ k, φ₀ (b.traceDual k) * φ₀ (g (b k * x))) - (if g = 1 then φ₀ x else 0) := by
      intro g
      simp only [c, sub_mul, Finset.sum_mul, map_mul, mul_assoc]
      split_ifs with hg
      · subst hg; simp
      · simp
    show ∑ g, c g * φ₀ (g x) = 0
    rw [Finset.sum_congr rfl fun g _ => e1 g, Finset.sum_sub_distrib, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [sum_aut_eq_trace φ₀]
    rw [map_expand φ₀ x]
    simp
  have := Fintype.linearIndependent_iff.mp li c hc h
  simp only [c, sub_eq_zero] at this
  exact this

theorem orth (φ₀ σ : E →+* C) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * σ (integralBasis E k) = if σ = φ₀ then 1 else 0 := by
  obtain ⟨h, rfl⟩ := exists_aut φ₀ σ
  have := orth_aut φ₀ h
  rw [comp_eq_iff]
  exact this

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem trace_mul_traceDual (a : 𝓞 E) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E ((a : E) * (integralBasis E).traceDual k) =
      (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) := by
  have h := ((integralBasis E).traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E a) k
  rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply, Algebra.traceForm_apply] at h
  rw [← eq_intCast (algebraMap ℤ ℚ), h]

theorem base {O : Type} [CommRing O] [Algebra O C] {v : Valuation C ℝ≥0} (hv : v.Integers O)
    (φ₀ : E →+* C) :
    ∃ δ : C, δ ≠ 0 ∧ (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C,
      ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ₀ then δ else 0) ∧
    ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C,
      ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ₀ then s else 0) → v s ≤ v δ := by
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := (integralBasis E).index_nonempty
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ
    (fun k => v (φ₀ ((integralBasis E).traceDual k))) Finset.univ_nonempty
  have hy : φ₀ ((integralBasis E).traceDual k₀) ≠ 0 :=
    (map_ne_zero φ₀).2 ((integralBasis E).traceDual.ne_zero k₀)
  have hvy : v (φ₀ ((integralBasis E).traceDual k₀)) ≠ 0 := (Valuation.ne_zero_iff v).2 hy
  refine ⟨(φ₀ ((integralBasis E).traceDual k₀))⁻¹, inv_ne_zero hy, ?_, ?_⟩
  · have hr : ∀ k, ∃ o : O, algebraMap O C o =
        (φ₀ ((integralBasis E).traceDual k₀))⁻¹ * φ₀ ((integralBasis E).traceDual k) := by
      intro k
      apply hv.exists_of_le_one
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ (pos_iff_ne_zero.2 hvy), mul_one]
      exact hk₀ k (Finset.mem_univ _)
    choose r hr using hr
    let e := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
    refine ⟨Fintype.card _, fun i => r (e.symm i), fun i => RingOfIntegers.basis E (e.symm i),
      fun σ => ?_⟩
    rw [Equiv.sum_comp e.symm (fun k => algebraMap O C (r k) * σ (RingOfIntegers.basis E k))]
    have h2 : ∀ k, σ (RingOfIntegers.basis E k : E) = σ (integralBasis E k) := by
      intro k
      rw [integralBasis_apply]
    simp_rw [hr, h2, mul_assoc, ← Finset.mul_sum]
    rw [orth φ₀ σ]
    split_ifs <;> simp
  · intro n r a s hs
    have h1 : ∀ g : E ≃ₐ[ℚ] E, ∑ k, algebraMap O C (r k) * φ₀ (g ((a k : E) * (integralBasis E).traceDual k₀)) =
        if g = 1 then s * φ₀ ((integralBasis E).traceDual k₀) else 0 := by
      intro g
      have := hs (φ₀.comp g.toRingHom)
      rw [comp_eq_iff] at this
      have e3 : ∀ k, algebraMap O C (r k) * φ₀ (g ((a k : E) * (integralBasis E).traceDual k₀)) =
          (algebraMap O C (r k) * φ₀ (g (a k))) * φ₀ (g ((integralBasis E).traceDual k₀)) := by
        intro k
        rw [map_mul, map_mul, mul_assoc]
      rw [Finset.sum_congr rfl fun k _ => e3 k, ← Finset.sum_mul]
      erw [this]
      split_ifs with hg
      · subst hg; rfl
      · simp
    have h2 := Finset.sum_congr rfl fun g (_ : g ∈ (Finset.univ : Finset (E ≃ₐ[ℚ] E))) => h1 g
    rw [Finset.sum_comm] at h2
    simp_rw [← Finset.mul_sum, sum_aut_eq_trace φ₀, trace_mul_traceDual] at h2
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    have hle : v (s * φ₀ ((integralBasis E).traceDual k₀)) ≤ 1 := by
      rw [← h2]
      have : ∑ k, algebraMap O C (r k) * algebraMap ℚ C (((RingOfIntegers.basis E).repr (a k) k₀ : ℤ) : ℚ) =
          algebraMap O C (∑ k, r k * (((RingOfIntegers.basis E).repr (a k) k₀ : ℤ) : O)) := by
        simp [map_sum, map_mul, map_intCast]
      rw [this]
      exact hv.map_le_one _
    calc v s = v (s * φ₀ ((integralBasis E).traceDual k₀)) * v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := by
          rw [← map_mul, mul_assoc, mul_inv_cancel₀ hy, mul_one]
      _ ≤ 1 * v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := by gcongr
      _ = v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := one_mul _

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

theorem indicator_inverseDifferent : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (C : Type) [Field C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∃ δ : C, δ ≠ 0 ∧ ∀ φ : E →+* C, (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then δ else 0) ∧ ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v δ := by
  intro E _ _ _ C _ _ v O _ _ hv
  by_cases hne : Nonempty (E →+* C)
  swap
  · exact ⟨1, one_ne_zero, fun φ => (hne ⟨φ⟩).elim⟩
  obtain ⟨φ₀⟩ := hne
  obtain ⟨δ, hδ0, ha, hb⟩ := base hv φ₀
  refine ⟨δ, hδ0, fun φ => ?_⟩
  obtain ⟨g, rfl⟩ := exists_aut φ₀ φ
  constructor
  · obtain ⟨n, r, a, h⟩ := ha
    refine ⟨n, r, fun k => RingOfIntegers.mapRingHom g.symm.toRingHom (a k), fun σ => ?_⟩
    have hσ := h (σ.comp g.symm.toRingHom)
    have e1 : σ.comp g.symm.toRingHom = φ₀ ↔ σ = φ₀.comp g.toRingHom := by
      constructor
      · rintro rfl
        ext x
        simp
      · rintro rfl
        ext x
        simp
    rw [if_congr e1 rfl rfl] at hσ
    rw [← hσ]
    rfl
  · intro n r a s hs
    apply hb n r (fun k => RingOfIntegers.mapRingHom g.toRingHom (a k)) s
    intro τ
    have hτ := hs (τ.comp g.toRingHom)
    have e1 : τ.comp g.toRingHom = φ₀.comp g.toRingHom ↔ τ = φ₀ := by
      constructor
      · intro hh
        ext x
        have := RingHom.congr_fun hh (g.symm x)
        simpa using this
      · rintro rfl
        rfl
    rw [if_congr e1 rfl rfl] at hτ
    rw [← hτ]
    rfl

end GlobalTheory.InvDifferentArith
