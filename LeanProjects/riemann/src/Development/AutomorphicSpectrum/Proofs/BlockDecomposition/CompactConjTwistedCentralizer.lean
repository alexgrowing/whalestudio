import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariantStatement
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.LocVan.TNorm

variable {n : ℕ}

theorem uOf_zero' (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : uOf (0 : nilrad W₁ W₂) = 1 :=
  Units.ext (by simp)

theorem uOf_mul_mem_nSet {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (C : Set (GL (Fin n) ℂ)) (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    uOf X * x ∈ nSet W₁ W₂ C ↔ x ∈ nSet W₁ W₂ C := by
  constructor
  · rintro ⟨Y, c, hc, h⟩
    refine ⟨nmul hW (ninv hW X) Y, c, hc, ?_⟩
    rw [uOf_nmul, uOf_ninv, mul_assoc, h, inv_mul_cancel_left]
  · rintro ⟨Y, c, hc, rfl⟩
    exact ⟨nmul hW X Y, c, hc, by rw [uOf_nmul, mul_assoc]⟩

theorem nSet_mono (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C C' : Set (GL (Fin n) ℂ)} (h : C ⊆ C') :
    nSet W₁ W₂ C ⊆ nSet W₁ W₂ C' := by
  rintro _ ⟨X, c, hc, rfl⟩
  exact ⟨X, c, h hc, rfl⟩

theorem isOpen_nSet (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {U : Set (GL (Fin n) ℂ)} (hU : IsOpen U) :
    IsOpen (nSet W₁ W₂ U) := by
  have e : nSet W₁ W₂ U = ⋃ X : nilrad W₁ W₂, (fun g => (uOf X)⁻¹ * g) ⁻¹' U := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      exact ⟨X, by simpa using hc⟩
    · rintro ⟨X, hX⟩
      exact ⟨X, _, hX, by simp⟩
  rw [e]
  exact isOpen_iUnion fun X => hU.preimage (continuous_const.mul continuous_id)

theorem measurableSet_nSet [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C : Set (GL (Fin n) ℂ)} (hC : IsCompact C) :
    MeasurableSet (nSet W₁ W₂ C) := by
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  let K := CompactExhaustion.choice (nilrad W₁ W₂)
  have hcont : Continuous fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => uOf p.1 * p.2 :=
    (continuous_uOf.comp continuous_fst).mul continuous_snd
  have e : nSet W₁ W₂ C =
      ⋃ k, (fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => uOf p.1 * p.2) '' (K k ×ˢ C) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      obtain ⟨k, hk⟩ := K.exists_mem X
      exact ⟨k, (X, c), ⟨hk, hc⟩, rfl⟩
    · rintro ⟨k, ⟨X, c⟩, ⟨_, hc⟩, rfl⟩
      exact ⟨X, c, hc, rfl⟩
  rw [e]
  exact MeasurableSet.iUnion fun k => (((K.isCompact k).prod hC).image hcont).measurableSet

def zSet (T : Subgroup (GL (Fin n) ℂ)) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (U : Set (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ) :=
  {g | ∃ t ∈ T, ∃ X : nilrad W₁ W₂, ∃ c ∈ U, t * uOf X * c = g}

theorem isOpen_zSet (T : Subgroup (GL (Fin n) ℂ)) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    {U : Set (GL (Fin n) ℂ)} (hU : IsOpen U) : IsOpen (zSet T W₁ W₂ U) := by
  have e : zSet T W₁ W₂ U =
      ⋃ t : T, ⋃ X : nilrad W₁ W₂, (fun g => ((t : GL (Fin n) ℂ) * uOf X)⁻¹ * g) ⁻¹' U := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, X, c, hc, rfl⟩
      exact ⟨⟨t, ht⟩, X, by rwa [inv_mul_cancel_left]⟩
    · rintro ⟨t, X, hX⟩
      exact ⟨t, t.2, X, _, hX, mul_inv_cancel_left _ _⟩
  rw [e]
  exact isOpen_iUnion fun t => isOpen_iUnion fun X =>
    hU.preimage (continuous_const.mul continuous_id)

theorem mul_mem_zSet {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    {U : Set (GL (Fin n) ℂ)} {h : GL (Fin n) ℂ} (hh : h ∈ T) (x : GL (Fin n) ℂ) :
    h * x ∈ zSet T W₁ W₂ U ↔ x ∈ zSet T W₁ W₂ U := by
  constructor
  · rintro ⟨t, ht, X, c, hc, e⟩
    refine ⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, X, c, hc, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc t, e, inv_mul_cancel_left]
  · rintro ⟨t, ht, X, c, hc, rfl⟩
    exact ⟨h * t, T.mul_mem hh ht, X, c, hc, by simp only [mul_assoc]⟩

theorem exists_conj {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    (hconj : ∀ t ∈ T, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂)
    {t : GL (Fin n) ℂ} (ht : t ∈ T) (X : nilrad W₁ W₂) :
    ∃ X' : nilrad W₁ W₂, uOf X' = t * uOf X * t⁻¹ := by
  refine ⟨⟨t.val * X.1 * (t⁻¹ : GL (Fin n) ℂ).val, hconj t ht X.1 X.2⟩, Units.ext ?_⟩
  have h1 : t.val * (t⁻¹ : GL (Fin n) ℂ).val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem uOf_mul_mem_zSet {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    (hW : W₁ ≤ W₂)
    (hconj : ∀ t ∈ T, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂)
    (U : Set (GL (Fin n) ℂ)) (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    uOf X * x ∈ zSet T W₁ W₂ U ↔ x ∈ zSet T W₁ W₂ U := by
  have fwd : ∀ (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ), x ∈ zSet T W₁ W₂ U →
      uOf X * x ∈ zSet T W₁ W₂ U := by
    rintro X _ ⟨t, ht, Y, c, hc, rfl⟩
    obtain ⟨X', hX'⟩ := exists_conj hconj (T.inv_mem ht) X
    refine ⟨t, ht, nmul hW X' Y, c, hc, ?_⟩
    rw [uOf_nmul, hX', inv_inv]
    group
  refine ⟨fun h => ?_, fwd X x⟩
  have := fwd (ninv hW X) _ h
  rwa [uOf_ninv, inv_mul_cancel_left] at this

end GlobalTheory.CompanionTheory.LocVan.TNorm

namespace GlobalTheory.CompanionTheory.LocVan

open TNorm in

theorem tNormaliser : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
  (∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) →
  (∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂) →
  (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤) →
  ∃ ρ : GL (Fin n) ℂ → ℝ≥0∞, IsQuotNormaliser (twCent (thC n) d) μd ρ ∧
    ∀ (X : nilrad W₁ W₂) (g : GL (Fin n) ℂ), ρ (uOf X * g) = ρ g := by
  intro n _ _ d μd _ W₁ W₂ hW hc hconj hfin
  haveI := secondCountable_GL n
  haveI := locallyCompact_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SFinite μd := by
    haveI := sigmaFinite_twCent d μd
    infer_instance
  obtain ⟨U, hUo, hUc, hUcov⟩ := exists_open_cover n
  have hact : Measurable fun p : twCent (thC n) d × GL (Fin n) ℂ =>
      (p.1 : GL (Fin n) ℂ) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have hr : ∀ h₀ : twCent (thC n) d,
      MeasurePreserving (fun t : twCent (thC n) d => t * h₀) μd μd := by
    intro h₀
    have e : (fun t : twCent (thC n) d => t * h₀) = fun t => h₀ * t :=
      funext fun t => Subtype.ext (hc t t.2 h₀ h₀.2)
    rw [e]
    exact measurePreserving_mul_left μd h₀
  obtain ⟨ρ, hρm, hρ1, hρS⟩ := GlobalTheory.T.integral_fiber_decomposition_invariant μd
    (fun (t : twCent (thC n) d) (x : GL (Fin n) ℂ) => (t : GL (Fin n) ℂ) * x) hact
    (fun t₀ t => t * t₀) hr
    (fun h₀ h x => by simp only [Subgroup.coe_mul, mul_assoc])
    (fun i => nSet W₁ W₂ (closure (U i))) (fun i => zSet (twCent (thC n) d) W₁ W₂ (U i))
    (fun i => measurableSet_nSet W₁ W₂ (hUc i))
    (fun i => (isOpen_zSet _ W₁ W₂ (hUo i)).measurableSet)
    (fun i h x => mul_mem_zSet h.2 x)
    (fun x => by
      obtain ⟨i, hi⟩ := hUcov x
      exact ⟨i, 1, one_mem _, 0, x, hi, by simp [uOf_zero']⟩)
    (fun i x => hfin _ (hUc i) x)
    (fun i x hx => by
      obtain ⟨t₀, ht₀, X, c, hcU, rfl⟩ := hx
      have hopen : IsOpen {t : twCent (thC n) d |
          (t : GL (Fin n) ℂ) * (t₀ * uOf X * c) ∈ nSet W₁ W₂ (U i)} :=
        (isOpen_nSet W₁ W₂ (hUo i)).preimage (continuous_subtype_val.mul continuous_const)
      have hne : {t : twCent (thC n) d |
          (t : GL (Fin n) ℂ) * (t₀ * uOf X * c) ∈ nSet W₁ W₂ (U i)}.Nonempty :=
        ⟨⟨t₀⁻¹, inv_mem ht₀⟩, X, c, hcU, by simp [mul_assoc]⟩
      have hpos := hopen.measure_ne_zero μd hne
      intro h0
      exact hpos (measure_mono_null
        (fun t ht => nSet_mono W₁ W₂ subset_closure ht) h0))
    {s | ∃ X : nilrad W₁ W₂, s = fun g => uOf X * g}
    (by
      rintro _ ⟨X, rfl⟩ i x
      exact uOf_mul_mem_nSet hW _ X x)
    (by
      rintro _ ⟨X, rfl⟩ i x
      exact uOf_mul_mem_zSet hW hconj _ X x)
    (by
      rintro _ ⟨X, rfl⟩ h
      obtain ⟨X', hX'⟩ := exists_conj hconj h.2 X
      refine ⟨_, ⟨X', rfl⟩, fun x => ?_⟩
      simp only [hX']
      group)
  exact ⟨ρ, ⟨hρm, hρ1⟩, fun X g => hρS _ ⟨X, rfl⟩ g⟩

end GlobalTheory.CompanionTheory.LocVan
end
