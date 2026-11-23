import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldCentredAtPrimeStatement

namespace GlobalTheory

theorem exists_valuedField_centred_subalgebra (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K]
    (u : R) (hu : u ≠ 0) (A : Subalgebra R K) (hA : A.FG) (P : Ideal A) (hP : P.IsPrime)
    (huP : algebraMap R A u ∈ P) :
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (gam : K →+* C), (∀ x ∈ A, ‖gam x‖ ≤ 1) ∧
        ∀ x : A, x ∈ P → ‖gam (x : K)‖ < 1 := by
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hinj : Function.Injective (algebraMap R A) := by
    intro a b hab
    apply hinjK
    have := congrArg (fun x : A => (x : K)) hab
    simpa using this
  haveI : IsNoetherianRing A := isNoetherianRing_of_fg hA
  haveI : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.extendScalars hinj
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2 Subtype.val_injective
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at huP
    exact hu (hinj (by rw [huP, map_zero]))
  obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ := GlobalTheory.T.exists_complete_algClosed_field_centred_at_prime A K P hP hne
  exact ⟨C, i1, i2, i3, i4, gam, fun x hx => h1 ⟨x, hx⟩, fun x hx => h2 x hx⟩

theorem exists_valuedField_centre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  intro R K _ _ _ _ _ _ _ _ u hum hu R₁ hfin S hS e
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hR : ∀ r, S.valuation (algebraMap R K r) ≤ 1 := fun r =>
    (S.valuation_le_one_iff _).2 (hS r)
  have hR₁ : ∀ x ∈ R₁, S.valuation x ≤ 1 := by
    intro x hx
    have hint : IsIntegral R x := by
      have h := (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : R₁)).map R₁.val
      simpa using h
    letI : Algebra R S := ((algebraMap R K).codRestrict S.toSubring hS).toAlgebra
    haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint' : IsIntegral S x := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).1 hint'
    rw [← hy]
    exact (S.valuation_le_one_iff _).2 y.2
  have hfg : (Subalgebra.toSubmodule R₁).FG := Module.Finite.iff_fg.1 hfin
  let q : Ideal R₁ :=
    { carrier := {x | S.valuation (x : K) < 1}
      add_mem' := fun {a b} ha hb => by
        simpa using S.valuation.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hx' : S.valuation (x : K) < 1 := hx
        show S.valuation ((c : K) * (x : K)) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ c.2)) hx' }
  have hq : ∀ x : R₁, x ∈ q ↔ S.valuation (x : K) < 1 := fun _ => Iff.rfl
  have hqp : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hq]; simp
    · intro a b hab
      by_contra hcon
      rw [not_or, hq, hq, not_lt, not_lt] at hcon
      rw [hq, Subalgebra.coe_mul, map_mul, le_antisymm (hR₁ _ a.2) hcon.1,
        le_antisymm (hR₁ _ b.2) hcon.2] at hab
      simp at hab
  by_cases hv : S.valuation (algebraMap R K u) = 1
  ·
    set U : K := algebraMap R K u with hU
    have hU0 : U ≠ 0 := fun h => hu (hinjK (by rw [← hU, h, map_zero]))
    let Q : Submodule R K := (q.restrictScalars R).map R₁.val.toLinearMap
    have hQ : Q.FG := by
      haveI : IsNoetherian R R₁ := isNoetherian_of_isNoetherianRing_of_finite R R₁
      exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    let N : Submodule R K := Subalgebra.toSubmodule R₁ ⊔
      Q.map (LinearMap.mulRight R (U ^ (e + 1))⁻¹)
    have hN : N.FG := Submodule.FG.sup hfg (hQ.map _)
    let A : Subalgebra R K := Algebra.adjoin R (N : Set K)
    have hA : A.FG := by
      obtain ⟨s, hs⟩ := hN
      refine ⟨s, ?_⟩
      show _ = Algebra.adjoin R (N : Set K)
      rw [← hs, Algebra.adjoin_span]
    have hinv : ∀ x ∈ A, ∃ a ∈ R₁, S.valuation (x - a) < 1 := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, ha, _, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
        refine ⟨a, ha, ?_⟩
        have hg' : S.valuation (g : K) < 1 := hg
        simpa [hv] using hg'
      | algebraMap r => exact ⟨_, R₁.algebraMap_mem r, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a + b, R₁.add_mem ha hb, ?_⟩
        rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
        exact S.valuation.map_add_lt hx hy
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a * b, R₁.mul_mem ha hb, ?_⟩
        rw [show x * y - a * b = (x - a) * (y - b) + (b * (x - a) + a * (y - b)) by ring]
        refine S.valuation.map_add_lt ?_ (S.valuation.map_add_lt ?_ ?_) <;> rw [map_mul]
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hy
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ hb)) hx
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ ha)) hy
    have hnu : ¬ IsUnit (algebraMap R A u) := by
      intro hun
      obtain ⟨x, hx⟩ := hun.exists_right_inv
      have hx' : U * (x : K) = 1 := by
        have := congrArg (fun x : A => (x : K)) hx
        simpa using this
      obtain ⟨a, ha, hxa⟩ := hinv x x.2
      obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hqp.ne_top
      have hMc : (M.comap (algebraMap R R₁)).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
      have huM : algebraMap R R₁ u ∈ M := by
        rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hMc]; exact hum
      have h1 : (1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) ∈ q := by
        rw [hq]
        have : ((1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) : K) = U * (x - a) := by
          rw [mul_sub, hx']; simp [hU]
        rw [this, map_mul, hv, one_mul]
        exact hxa
      apply hM.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using M.add_mem (hqM h1) (M.mul_mem_right (⟨a, ha⟩ : R₁) huM)
    obtain ⟨P, hP, huP⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu A hA P hP.isPrime huP
    have hgu : ‖gam U‖ < 1 := h2 _ huP
    refine ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (A.algebraMap_mem r), hgu, ?_⟩
    intro f hf hvf
    have hmem : f * (U ^ (e + 1))⁻¹ ∈ A :=
      Algebra.subset_adjoin (Submodule.mem_sup_right
        (Submodule.mem_map.2 ⟨f, Submodule.mem_map.2 ⟨⟨f, hf⟩, hvf, rfl⟩, rfl⟩))
    have hle : ‖gam f‖ ≤ ‖gam U‖ ^ (e + 1) := by
      have hf' : f = f * (U ^ (e + 1))⁻¹ * U ^ (e + 1) := by field_simp
      have h3 := h1 _ hmem
      rw [hf', map_mul, norm_mul, map_pow, norm_pow]
      exact mul_le_of_le_one_left (by positivity) h3
    refine ⟨hle.trans_lt (pow_lt_one₀ (norm_nonneg _) hgu (by omega)), fun _ => hle.trans ?_⟩
    exact pow_le_pow_of_le_one (norm_nonneg _) hgu.le (by omega)
  · have huq : algebraMap R R₁ u ∈ q := lt_of_le_of_ne (hR u) hv
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu R₁ (Subalgebra.fg_of_fg_toSubmodule hfg)
        q hqp huq
    exact ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (R₁.algebraMap_mem r), h2 _ huq,
      fun f hf hvf => ⟨h2 ⟨f, hf⟩ hvf, fun h => absurd h hv⟩⟩

end GlobalTheory
