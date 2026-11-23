import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem quotient_multiplication_exact {R : Type} [CommRing R] [IsDomain R] (u v w : R) (hv : v ≠ 0)
    (hw : w = v * u) :
    ∃ (f : (R ⧸ Ideal.span {u}) →ₗ[R] (R ⧸ Ideal.span {w}))
      (g : (R ⧸ Ideal.span {w}) →ₗ[R] (R ⧸ Ideal.span {v})),
      Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
      (∀ x, f (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (v * x)) ∧
      (∀ x, g (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x) := by
  subst hw
  have h1 : Ideal.span {u} ≤ Submodule.comap (LinearMap.mulLeft R v) (Ideal.span {v * u}) := by
    intro x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    show v * (t * u) ∈ Ideal.span {v * u}
    rw [Ideal.mem_span_singleton]
    exact ⟨t, by ring⟩
  have h2 : Ideal.span {v * u} ≤ Submodule.comap (LinearMap.id : R →ₗ[R] R) (Ideal.span {v}) := by
    rw [Submodule.comap_id]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right v u)
  let f := Submodule.mapQ (Ideal.span {u}) (Ideal.span {v * u}) (LinearMap.mulLeft R v) h1
  let g := Submodule.mapQ (Ideal.span {v * u}) (Ideal.span {v}) (LinearMap.id : R →ₗ[R] R) h2
  have hf : ∀ x, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (v * x) := fun x => rfl
  have hg : ∀ x, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => rfl
  refine ⟨f, g, ?_, ?_, ?_, fun x => rfl, fun x => rfl⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      rw [hf, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at ha
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      exact (mul_dvd_mul_iff_left hv).mp ha
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [hg, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨Submodule.Quotient.mk t, hf t⟩
      · rintro ⟨a, ha⟩
        induction a using Submodule.Quotient.induction_on with
        | H t =>
          rw [hf, Submodule.Quotient.eq, Ideal.mem_span_singleton] at ha
          obtain ⟨s, hs⟩ := ha
          exact ⟨t - u * s, by linear_combination -hs⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, hg x⟩

theorem UpperTheory.V.Pa.B2.amMaps :
    ∀ (K : Type) [Field K] (e m : ℕ), e ≤ m → ∃ (f : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m - e)}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})) (g : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ e})) (k : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ e}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})) (r : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m - e)})), Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧ Function.Injective k ∧ Function.Exact k r ∧ Function.Surjective r ∧ ∀ y, f (r y) = (PowerSeries.X : PowerSeries K) ^ e • y := by
  intro K _ e m h
  have hX : (PowerSeries.X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  obtain ⟨f, g, hfi, hfg, hgs, hf, -⟩ :=
    quotient_multiplication_exact ((PowerSeries.X : PowerSeries K) ^ (m - e)) (PowerSeries.X ^ e) (PowerSeries.X ^ m)
      (pow_ne_zero _ hX) (by rw [← pow_add, Nat.add_sub_cancel' h])
  obtain ⟨k, r, hki, hkr, hrs, -, hr⟩ :=
    quotient_multiplication_exact ((PowerSeries.X : PowerSeries K) ^ e) (PowerSeries.X ^ (m - e)) (PowerSeries.X ^ m)
      (pow_ne_zero _ hX) (by rw [← pow_add, Nat.sub_add_cancel h])
  refine ⟨f, g, k, r, hfi, hfg, hgs, hki, hkr, hrs, fun y => ?_⟩
  induction y using Submodule.Quotient.induction_on with
  | H x => exact (congrArg f (hr x)).trans (hf x)
