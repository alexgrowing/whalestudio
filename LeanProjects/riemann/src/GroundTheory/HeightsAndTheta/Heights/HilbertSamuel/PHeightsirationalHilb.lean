import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHeightsirationalHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbFnValueSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockBirationalHilbert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def blockSum (γ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, γ ⟨k, i⟩

omit [Fintype K] in
theorem isMultiHomog_monomial {γ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (h : blockSum γ = a) (r : ℤ) :
    IsMultiHomog (monomial γ r : MRing ι) a := by
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  exact congrFun h k

omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b c : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b)
    (habc : a + b = c) : IsMultiHomog (f * g) c := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, ← habc, Pi.add_apply]

omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (d j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h1 := isMultiHomog_monomial (ι := ι) (γ := 0) (a := 0) (by funext k; simp [blockSum]) 1
    simpa using h1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact isMultiHomog_mul (h j (Finset.mem_insert_self j s))
      (ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj')) rfl

open Classical in

def monoSet (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) :=
  (Finset.Icc 0 (Finsupp.equivFunOnFinite.symm fun p : (Σ k, ι k) => a p.1)).filter (blockSum · = a)

theorem mem_monoSet {a : K → ℕ} {γ : (Σ k, ι k) →₀ ℕ} : γ ∈ monoSet a ↔ blockSum γ = a := by
  classical
  unfold monoSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Finset.mem_Icc.mpr ⟨by simp, fun p => ?_⟩, h⟩⟩
  rw [Finsupp.coe_equivFunOnFinite_symm, ← h]
  exact Finset.single_le_sum (f := fun i => γ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem aeval_monomial_int (y : (Σ k, ι k) → Ω) (γ : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    aeval y (monomial γ r : MRing ι) = ((r : ℚ) : Ω) * aeval y (monomial γ (1 : ℤ) : MRing ι) := by
  simp [aeval_monomial]

omit [Fintype K] in

theorem valueSpan_le (y : (Σ k, ι k) → Ω) (a : K → ℕ) (W : Submodule ℚ Ω)
    (hW : ∀ γ : (Σ k, ι k) →₀ ℕ, blockSum γ = a → aeval y (monomial γ (1 : ℤ) : MRing ι) ∈ W) :
    valueSpan y a ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  rw [aeval_monomial_int, ← Rat.smul_def]
  exact W.smul_mem _ (hW γ (funext fun k => hg γ hγ k))

theorem finiteDimensional_valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    FiniteDimensional ℚ (valueSpan y a) := by
  classical
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ
    (((monoSet a).image fun γ => aeval y (monomial γ (1 : ℤ) : MRing ι) : Finset Ω) : Set Ω))
    (valueSpan_le y a _ fun γ hγ => Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨γ, mem_monoSet.mpr hγ, rfl⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in

theorem finrank_le_of_mul [CharZero Ω] {V W : Submodule ℚ Ω} [FiniteDimensional ℚ W] {t : Ω} (ht : t ≠ 0)
    (h : V ≤ W.comap (LinearMap.mulLeft ℚ t)) : Module.finrank ℚ V ≤ Module.finrank ℚ W := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ t) := fun a b hab => mul_left_cancel₀ ht hab
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)]
  exact Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr h)

end BlockBirationalHilbert

open BlockBirationalHilbert in

theorem BlockBirationalHilbert.proof (hV : HilbFnValueSpan.Statement) : BlockBirationalHilbert.Statement := by
  intro K _ _ ι _ Ω _ _ y k₀ hy hbir m
  classical
  choose i hi using hy
  have hV' := hV K ι Ω y
  have := finiteDimensional_valueSpan (Ω := Ω) y

  have L : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else 0) =
      (Module.finrank ℚ (valueSpan y (blockDeg k₀ n)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk, blockDeg]
  have M : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else m k) =
      (Module.finrank ℚ (valueSpan y (fun k => if k = k₀ then n else m k)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk]

  set m₀ : K → ℕ := fun k => if k = k₀ then 0 else m k with hm₀
  let β : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.1 ≠ k₀ ∧ p.2 = i p.1 then m p.1 else 0
  have hβ : blockSum β = m₀ := by
    funext k
    by_cases hk : k = k₀ <;> simp [blockSum, β, hk, m₀]
  set u : Ω := aeval y (monomial β (1 : ℤ) : MRing ι) with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rcases p with ⟨k, j⟩
    have h0 : β ⟨k, j⟩ ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [β, Finsupp.coe_equivFunOnFinite_symm] at h0
    split_ifs at h0 with h
    · obtain ⟨_, rfl⟩ := h
      exact hi k
    · exact absurd rfl h0

  have key : ∀ α ∈ monoSet (ι := ι) m₀, ∃ (c : ℕ) (g h : MRing ι), IsMultiHomog g (blockDeg k₀ c) ∧
      IsMultiHomog h (blockDeg k₀ c) ∧ aeval y h ≠ 0 ∧
      aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y h = aeval y g * u := fun α hα =>
    hbir m₀ _ _ (isMultiHomog_monomial (mem_monoSet.mp hα) 1) (isMultiHomog_monomial hβ 1) hu
  choose c g h hg hh hh0 hgh using key
  refine ⟨∑ a ∈ (monoSet (ι := ι) m₀).attach, c a.1 a.2, fun n => ⟨?_, ?_⟩⟩
  ·
    rw [L, M]
    refine Nat.cast_le.mpr (finrank_le_of_mul hu (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨monomial β 1 * monomial γ 1,
      isMultiHomog_mul (isMultiHomog_monomial hβ 1) (isMultiHomog_monomial hγ 1) ?_, by
        simp only [map_mul, hu_def]⟩
    funext k; by_cases hk : k = k₀ <;> simp [hk, m₀, blockDeg]
  ·
    rw [M, L]
    have hH : aeval y (∏ a ∈ (monoSet (ι := ι) m₀).attach, h a.1 a.2) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hh0 a.1 a.2
    refine Nat.cast_le.mpr (finrank_le_of_mul (mul_ne_zero (inv_ne_zero hu) hH)
      (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]

    set γ₀ := γ.filter (fun p => p.1 = k₀) with hγ₀
    set α := γ.filter (fun p => ¬ p.1 = k₀) with hα_def
    have hsplit : γ₀ + α = γ := Finsupp.filter_add_filter_not γ _
    have hα : blockSum α = m₀ := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, m₀]
    have hγ₀' : blockSum γ₀ = blockDeg k₀ n := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, blockDeg]
    have hαS : α ∈ monoSet (ι := ι) m₀ := mem_monoSet.mpr hα
    have hmem : (⟨α, hαS⟩ : {x // x ∈ monoSet (ι := ι) m₀}) ∈ (monoSet (ι := ι) m₀).attach :=
      Finset.mem_attach _ _
    refine Submodule.subset_span ⟨monomial γ₀ 1 * g α hαS *
      ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, h a.1 a.2,
      isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_monomial hγ₀' 1) (hg α hαS) rfl)
        (isMultiHomog_prod _ _ (fun a => blockDeg k₀ (c a.1 a.2)) fun a _ => hh a.1 a.2) ?_, ?_⟩
    · funext k
      by_cases hk : k = k₀
      · simp only [Pi.add_apply, Finset.sum_apply, blockDeg, hk, if_true]
        rw [← Finset.add_sum_erase _ _ hmem]
        ring
      · simp [blockDeg, hk, Finset.sum_apply]
    · have e1 : aeval y (monomial γ (1 : ℤ) : MRing ι) =
          aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι) := by
        rw [← map_mul, monomial_mul, hsplit, mul_one]
      rw [map_mul, map_mul, e1, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hmem]
      have e2 := hgh α hαS
      calc aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)
          = (u⁻¹ * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by
            rw [inv_mul_cancel₀ hu, one_mul]
        _ = u⁻¹ * (aeval y (g α hαS) * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by ring
        _ = u⁻¹ * (aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y (h α hαS)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by rw [e2]
        _ = u⁻¹ * (aeval y (h α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι)) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
