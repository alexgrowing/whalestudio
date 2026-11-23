import Formalism.LocalRingCardinality.SpanPowerMembership.NZColD

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical Module

section Desc

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

include hσ in

theorem desc {V W ι : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (B : Submodule A V) (x : V)
    (hx : φ x ∈ Submodule.span O (φ '' (B : Set V))) : ∃ s : A, s ∉ w.asIdeal ∧ s • x ∈ B := by
  have h1 : (1 : A) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  by_cases hx0 : x = 0
  · exact ⟨1, h1, by rw [hx0, smul_zero]; exact B.zero_mem⟩
  have hφx : φ x ≠ 0 :=
    (FBC.li_of_basis_li σ φ hφ b hb (fun _ : Unit => x) (LinearIndependent.of_subsingleton () hx0)).ne_zero ()
  have h2 := (FBC.flat_ext w σ hσ φ hφ b hb).2 B (Submodule.span K {x})
  have h3 : φ x ∈ Submodule.span O (φ '' ((B ⊓ (Submodule.span K {x}).restrictScalars A : Submodule A V) : Set V)) := by
    rw [← h2]
    exact ⟨hx, Submodule.subset_span ⟨x, Submodule.mem_span_singleton_self x, rfl⟩⟩
  by_contra hno
  have hlt : ∀ k : K, k • x ∈ B → w.valuation K k < 1 := by
    intro k hk
    by_contra hge
    rw [not_lt] at hge
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hge
    obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer k⁻¹ (by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge)
    refine hno ⟨d, d.2, ?_⟩
    have : (d : A) • x = n • (k • x) := by
      rw [← algebraMap_smul K (d : A), ← algebraMap_smul K n, smul_smul, ← hnd, mul_assoc, mul_comm _ k, ← mul_assoc,
        inv_mul_cancel₀ hk0, one_mul]
    rw [this]
    exact B.smul_mem _ hk
  have h4 : Submodule.span O (φ '' ((B ⊓ (Submodule.span K {x}).restrictScalars A : Submodule A V) : Set V)) ≤
      IsLocalRing.maximalIdeal O • Submodule.span O {φ x} := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨hyB, hyU⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hyU
    have hk := hlt k hyB
    obtain ⟨o, ho⟩ := (hσ k).1 hk.le
    refine Submodule.mem_smul_span_singleton.mpr ⟨o, ?_, ?_⟩
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨o', ho'⟩ := hu.exists_right_inv
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [map_zero] at ho
        have : o = 0 := IsFractionRing.injective O Kf (by rw [ho, map_zero])
        rw [this, zero_mul] at ho'
        exact zero_ne_one ho'
      have h5 : σ k⁻¹ = algebraMap O Kf o' := by
        have := congrArg (algebraMap O Kf) ho'
        rw [map_mul, map_one, ho] at this
        rw [map_inv₀]
        exact inv_eq_of_mul_eq_one_right this
      have h6 := (hσ k⁻¹).2 ⟨o', h5.symm⟩
      rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff (w.valuation K)).mpr hk0)] at h6
      exact absurd hk (not_lt.mpr h6)
    · rw [hφ, ← ho, algebraMap_smul]
  obtain ⟨m, hm, hmx⟩ := Submodule.mem_smul_span_singleton.mp (h4 h3)
  have hu : IsUnit (1 - m) := by
    by_contra hnu
    have : (1 - m) + m ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.maximalIdeal O).add_mem ((IsLocalRing.mem_maximalIdeal _).mpr hnu) hm
    rw [sub_add_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  have h7 : (1 - m) • φ x = 0 := by rw [sub_smul, one_smul, hmx, sub_self]
  exact hφx ((hu.smul_eq_zero).mp h7)

end Desc

end Formalism.BasicNotions.Examples₂.NZ
