import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing

namespace UpperTheory.V.Loc

private theorem sc_seq {T : ℕ → Type} (r : ∀ N, T (N + 1) → T N → Prop) (t0 : T 0)
    (hs : ∀ N (a : T N), ∃ b : T (N + 1), r N b a) : ∃ F : ∀ N, T N, F 0 = t0 ∧ ∀ N, r N (F (N + 1)) (F N) := by
  choose s hs using hs
  exact ⟨fun N => Nat.rec t0 s N, rfl, fun N => hs N _⟩

private theorem sc_lim {O R A : Type} [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]
    (m : Ideal A) [IsAdicComplete m A] (F : ∀ N : ℕ, R →ₐ[O] A ⧸ m ^ (N + 2))
    (hs : ∀ N a, Ideal.Quotient.factorPow m (by omega : N + 2 ≤ N + 1 + 2) (F (N + 1) a) = F N a) :
    ∃ φ : R →ₐ[O] A, ∀ N a, Ideal.Quotient.mk (m ^ (N + 2)) (φ a) = F N a := by
  have ha : StrictMono (fun n : ℕ => n + 2) := fun _ _ h => by simpa using h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : R →+* A, ∀ n a, Ideal.Quotient.mk (m ^ (n + 2)) (ψ a) = F n a :=
    ⟨IsAdicComplete.StrictMono.liftRingHom m ha (fun n => (F n).toRingHom) (fun {k} => RingHom.ext (hs k)),
      fun n a => IsAdicComplete.StrictMono.mk_liftRingHom m ha _ _ a⟩
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψ⟩
  refine sub_eq_zero.1 (IsHausdorff.haus (I := m) inferInstance _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (by omega : n ≤ n + 2) (Ideal.Quotient.eq.1 ?_)
  exact (hψ n _).trans ((F n).commutes c)

private theorem sc_chain {O R A : Type} [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]
    (J : ℕ → Ideal A) (hJ : ∀ N, J (N + 1) ≤ J N) (hJ0 : ∀ N, J N ≤ J 0)
    (I : Ideal R) (f₀ : R →ₐ[O] A ⧸ J 0) (h₀ : I ≤ RingHom.ker f₀)
    (step : ∀ (N : ℕ) (f' : R →ₐ[O] A ⧸ J N), I ≤ RingHom.ker f' →
      (∀ a, Ideal.Quotient.factor (hJ0 N) (f' a) = f₀ a) →
      ∃ f : R →ₐ[O] A ⧸ J (N + 1), I ≤ RingHom.ker f ∧ ∀ a, Ideal.Quotient.factor (hJ N) (f a) = f' a) :
    ∃ F : ∀ N, R →ₐ[O] A ⧸ J N, F 0 = f₀ ∧ (∀ N, I ≤ RingHom.ker (F N)) ∧
      ∀ N a, Ideal.Quotient.factor (hJ N) (F (N + 1) a) = F N a := by
  obtain ⟨F, hF0, hF⟩ := sc_seq (T := fun N => {f : R →ₐ[O] A ⧸ J N // I ≤ RingHom.ker f ∧
      ∀ a, Ideal.Quotient.factor (hJ0 N) (f a) = f₀ a})
    (fun N f f' => ∀ a, Ideal.Quotient.factor (hJ N) (f.1 a) = f'.1 a)
    ⟨f₀, h₀, fun a => by
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f₀ a)
      rw [← hb, Ideal.Quotient.factor_mk]⟩
    (fun N f' => by
      obtain ⟨f, h1, h2⟩ := step N f'.1 f'.2.1 f'.2.2
      refine ⟨⟨f, h1, fun a => ?_⟩, h2⟩
      rw [← f'.2.2 a, ← h2 a]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f a)
      rw [← hb, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk])
  exact ⟨fun N => (F N).1, congrArg Subtype.val hF0, fun N => (F N).2.1, hF⟩

theorem sc_tower {O R A : Type} [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]
    (m : Ideal A) [IsAdicComplete m A] (I : Ideal R) (f₀ : R →ₐ[O] A ⧸ m ^ (0 + 2)) (h₀ : I ≤ RingHom.ker f₀)
    (step : ∀ (N : ℕ) (f' : R →ₐ[O] A ⧸ m ^ (N + 2)), I ≤ RingHom.ker f' →
      (∀ a, Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 2 ≤ N + 2)) (f' a) = f₀ a) →
      ∃ f : R →ₐ[O] A ⧸ m ^ (N + 1 + 2), I ≤ RingHom.ker f ∧
        ∀ a, Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2)) (f a) = f' a) :
    ∃ φ : R →ₐ[O] A, I ≤ RingHom.ker φ ∧ ∀ a, Ideal.Quotient.mk (m ^ (0 + 2)) (φ a) = f₀ a := by
  obtain ⟨F, hF0, hI, hF⟩ := sc_chain (fun N => m ^ (N + 2)) (fun N => Ideal.pow_le_pow_right (by omega))
    (fun N => Ideal.pow_le_pow_right (by omega)) I f₀ h₀ step
  obtain ⟨φ, hφ⟩ := sc_lim m F hF
  refine ⟨φ, fun a haI => ?_, fun a => (hφ 0 a).trans (AlgHom.congr_fun hF0 a)⟩
  refine IsHausdorff.haus (I := m) inferInstance (φ a) fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (by omega : n ≤ n + 2) (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
  exact (hφ n a).trans (hI n haI)

theorem sc_max (E : Type) [Field E] (n : ℕ) (g : MvPowerSeries (Fin n) E) :
    g ∈ maximalIdeal (MvPowerSeries (Fin n) E) ↔ MvPowerSeries.constantCoeff g = 0 := by
  rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

theorem sc_span (E : Type) [Field E] (n : ℕ) :
    Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) E)) = maximalIdeal _ := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun g hg => ?_
  · rintro _ ⟨i, rfl⟩
    exact (sc_max E n _).2 (by simp)
  · have := GlobalTheory.algHom_sub_constantCoeff_mem (AlgHom.id E (MvPowerSeries (Fin n) E))
      (K := Ideal.span (Set.range MvPowerSeries.X)) (fun j => Ideal.subset_span ⟨j, rfl⟩) g
    simpa [(sc_max E n g).1 hg] using this

theorem sc_first {O E R : Type} [CommRing O] [Field E] [Algebra O E] [CommRing R] [Algebra O R]
    (x : R →ₐ[O] O) (n : ℕ) (D : Fin n → (R →ₗ[O] E))
    (hD : ∀ i a b, D i (a * b) = algebraMap O E (x a) * D i b + algebraMap O E (x b) * D i a) :
    ∃ f : R →ₐ[O] MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ (0 + 2),
      ∀ a, f a = Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap O E (x a)) + ∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i) := by
  have h1 : ∀ i, D i 1 = 0 := fun i => by simpa using hD i 1 1
  let L : R →ₗ[O] MvPowerSeries (Fin n) E :=
    { toFun := fun a => MvPowerSeries.C (algebraMap O E (x a)) + ∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i
      map_add' := fun a b => by simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        simp only [smul_eq_mul, map_mul, Algebra.smul_def, mul_add, Finset.mul_sum, mul_assoc,
          MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] }
  have hm : ∀ a, ∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) :=
    fun a => (sc_max E n _).2 (by simp)
  refine ⟨AlgHom.ofLinearMap ((Ideal.Quotient.mkₐ O _).toLinearMap ∘ₗ L) ?_ fun a b => ?_, fun a => rfl⟩
  · simp [L, h1]
  · show Ideal.Quotient.mk _ (L (a * b)) = Ideal.Quotient.mk _ (L a) * Ideal.Quotient.mk _ (L b)
    rw [← map_mul, eq_comm, Ideal.Quotient.eq]
    have : L a * L b - L (a * b) = (∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i) * (∑ i, MvPowerSeries.C (D i b) * MvPowerSeries.X i) := by
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hD, map_mul, map_add, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [this, zero_add, pow_two]
    exact Ideal.mul_mem_mul (hm a) (hm b)

end UpperTheory.V.Loc
