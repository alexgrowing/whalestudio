import Mathlib

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace GlobalTheory.ContinuousValuationExtension

theorem continuous_of_valuation_eq {A B Γ : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (g : A →+* B)
    (hs : Function.Surjective (Valued.v : A → Γ))
    (hg : ∀ x : A, (Valued.v (g x) : Γ) = Valued.v x) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero A Γ).tendsto_iff (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _

  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, ha]
    intro h0
    apply γ.ne_zero
    apply MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
    rw [h0, map_zero]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff, ha] at hx
  show (Valued.v : Valuation B Γ).restrict (g x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx

theorem valuation_eq_of_denseRange {A B Γ ι : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (φ : A →+* B)
    (hφ : Continuous φ) (j : ι → A) (hj : DenseRange j)
    (h : ∀ x : ι, (Valued.v (φ (j x)) : Γ) = Valued.v (j x)) (y : A) :
    (Valued.v (φ y) : Γ) = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hφy : φ y ≠ 0 := (map_ne_zero φ).2 hy

  have h1 : {z : A | (Valued.v z : Γ) = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : {z : A | (Valued.v (φ z) : Γ) = Valued.v (φ y)} ∈ nhds y :=
    hφ.continuousAt.preimage_mem_nhds (Valued.locally_const ((Valuation.ne_zero_iff _).2 hφy))
  obtain ⟨_, ⟨x, rfl⟩, hx1, hx2⟩ := hj.inter_nhds_nonempty (Filter.inter_mem h1 h2)
  have e1 : (Valued.v (j x) : Γ) = Valued.v y := hx1
  have e2 : (Valued.v (φ (j x)) : Γ) = Valued.v (φ y) := hx2
  rw [← e2, h x, e1]

theorem exists_continuous_extension {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] (w : HeightOneSpectrum (RingOfIntegers K))
    (u : HeightOneSpectrum (RingOfIntegers L)) (f : K →+* adicCompletion L u)
    (hf : ∀ x : K, (Valued.v (f x) : WithZero (Multiplicative ℤ)) = valuation K w x) :
    ∃ φ : adicCompletion K w →+* adicCompletion L u, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x) ∧
      ∀ y : adicCompletion K w,
        (Valued.v (φ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* adicCompletion L u :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hgv : ∀ x : WithVal (w.valuation K),
      (Valued.v (g x) : WithZero (Multiplicative ℤ)) = Valued.v x := fun x => hf x.ofVal
  have hsurj : Function.Surjective
      (Valued.v : WithVal (w.valuation K) → WithZero (Multiplicative ℤ)) := fun γ => by
    obtain ⟨a, ha⟩ := w.valuation_surjective K γ
    exact ⟨WithVal.toVal _ a, ha⟩
  have hgc : Continuous g := continuous_of_valuation_eq g hsurj hgv

  let φ : adicCompletion K w →+* adicCompletion L u :=
    (UniformSpace.Completion.extensionHom g hgc).comp (adicCompletion.equiv K w).toRingHom
  have hφc : Continuous φ :=
    UniformSpace.Completion.continuous_extension.comp (adicCompletion.continuous_toCompletion K w)
  have hφf : ∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x := fun x =>
    UniformSpace.Completion.extensionHom_coe g hgc (WithVal.toVal _ x)
  refine ⟨φ, hφc, hφf, fun y => ?_⟩
  refine valuation_eq_of_denseRange φ hφc (algebraMap K (adicCompletion K w))
    (denseRange_algebraMap (K := K) (v := w)) (fun x => ?_) y
  rw [hφf x, hf x]
  exact (adicCompletion.valued_coe K w x).symm

end GlobalTheory.ContinuousValuationExtension
