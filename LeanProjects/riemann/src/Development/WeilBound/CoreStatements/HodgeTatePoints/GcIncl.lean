import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

private theorem mem_range_bc_of_entries_mem_intL {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (k : K)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ c : A, s • k = algebraMap A K c) :
    ∃ c : A, algebraMap A K c = k := by
  have hk : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
    rw [GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof A K]
    refine (Submodule.mem_iInf _).2 fun p => (Submodule.mem_iInf _).2 fun hp => ?_
    obtain ⟨s, hs, c, hc⟩ := h p.asIdeal p.isPrime hp
    refine ⟨s, hs, ?_⟩
    rw [hc, Subalgebra.mem_toSubmodule]
    exact Subalgebra.algebraMap_mem _ c
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, hc⟩

theorem test_incl : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω), M.IsLattice K → Module.Projective A M → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ M) → x ∈ M := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x hlat hproj hloc
  classical
  have hden : ∀ w ∈ Submodule.span K (M : Set Ω), ∃ d ∈ nonZeroDivisors A, d • w ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact ⟨1, one_mem _, by rw [one_smul]; exact hw⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
    | add u w _ _ hu hw =>
      obtain ⟨d1, hd1, h1⟩ := hu
      obtain ⟨d2, hd2, h2⟩ := hw
      refine ⟨d1 * d2, mul_mem hd1 hd2, ?_⟩
      have e1 : (d1 * d2) • u = d2 • (d1 • u) := by rw [mul_comm, mul_smul]
      have e2 : (d1 * d2) • w = d1 • (d2 • w) := by rw [mul_smul]
      rw [smul_add, e1, e2]
      exact M.add_mem (M.smul_mem _ h1) (M.smul_mem _ h2)
    | smul k w _ hw =>
      obtain ⟨d, hd, h1⟩ := hw
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) k
      refine ⟨b * d, mul_mem hb hd, ?_⟩
      have hb0 : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have e : (b * d) • ((algebraMap A K a / algebraMap A K b) • w) = a • (d • w) := by
        rw [← algebraMap_smul K (b * d), smul_smul, smul_smul a d w, ← algebraMap_smul K (a * d) w]
        congr 1
        rw [map_mul, map_mul]
        field_simp
      rw [e]
      exact M.smul_mem a h1
  obtain ⟨d, hd, hdx⟩ := hden x (by rw [hlat.span_eq_top]; trivial)
  have hd0' : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨σ, hσ⟩ := hproj.out
  set z : M := ⟨d • x, hdx⟩ with hzdef
  have hdiv : ∀ m : M, ∃ c : A, σ z m = d * c := by
    intro m
    have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
        ∃ c : A, s • (algebraMap A K (σ z m) / algebraMap A K d) = algebraMap A K c := by
      intro q hq hh
      obtain ⟨s, hs, hsx⟩ := hloc q hq hh
      refine ⟨s, hs, σ ⟨s • x, hsx⟩ m, ?_⟩
      have hz : s • z = d • (⟨s • x, hsx⟩ : M) := Subtype.ext (smul_comm s d x)
      have hm : s * σ z m = d * σ ⟨s • x, hsx⟩ m := by
        have h' := congrArg (fun f => f m) (congrArg σ hz)
        simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hm, map_mul]
      field_simp
    obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := K) _ hl
    refine ⟨c, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hc]
    field_simp
  choose c hc using hdiv
  have hyM : (∑ m ∈ (σ z).support, c m • (m : Ω)) ∈ M :=
    M.sum_mem (fun m _ => M.smul_mem _ m.2)
  have hsum : (∑ m ∈ (σ z).support, (σ z m) • (m : Ω)) = (z : Ω) := by
    have h1 := congrArg Subtype.val (hσ z)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at h1
    simpa using h1
  have hzy : d • (∑ m ∈ (σ z).support, c m • (m : Ω)) = d • x := by
    rw [Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hsum
    rw [hc m, mul_smul]
  have hcancel : ∀ u w : Ω, d • u = d • w → u = w := by
    intro u w huw
    have h1 : (algebraMap A K d) • u = (algebraMap A K d) • w := by
      rw [algebraMap_smul, algebraMap_smul]
      exact huw
    have h2 : (algebraMap A K d)⁻¹ • ((algebraMap A K d) • u) =
        (algebraMap A K d)⁻¹ • ((algebraMap A K d) • w) := by rw [h1]
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hd0', one_smul, one_smul] at h2
    exact h2
  rw [← hcancel _ _ hzy]
  exact hyM

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a t : A} (ha : a ≠ 0)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ a ∣ s * t) : a ∣ t := by
  classical
  have ha' : algebraMap A (FractionRing A) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha
  have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
      ∃ c : A, s • (algebraMap A (FractionRing A) t / algebraMap A (FractionRing A) a) =
        algebraMap A (FractionRing A) c := by
    intro q hq hh
    obtain ⟨s, hs, u, hu⟩ := h q hq hh
    refine ⟨s, hs, u, ?_⟩
    rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hu, map_mul]
    field_simp
  obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := FractionRing A) _ hl
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc]
  field_simp

theorem smul_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {M : Type} [AddCommGroup M] [Module A M] [Module.Projective A M]
    {a : A} (ha : a ≠ 0) (x : M)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ ∃ y : M, s • x = a • y) :
    ∃ y : M, x = a • y := by
  classical
  obtain ⟨σ, hσ⟩ := ‹Module.Projective A M›.out
  have hdiv : ∀ m : M, a ∣ σ x m := by
    intro m
    refine dvd_of_height_one ha (fun q hq hh => ?_)
    obtain ⟨s, hs, y, hy⟩ := h q hq hh
    refine ⟨s, hs, σ y m, ?_⟩
    have h' := congrArg (fun f => f m) (congrArg σ hy)
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
  choose c hc using hdiv
  refine ⟨∑ m ∈ (σ x).support, c m • m, ?_⟩
  conv_lhs => rw [← hσ x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [hc m, mul_smul, id_eq]

theorem test_div : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x a b _ hproj hx ha hab hloc
  have hloc' : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ y : M, s • (⟨x, hx⟩ : M) = a • y := by
    intro q hq hh
    by_cases hb : b ∈ q
    · obtain ⟨s, hs, y, hy, hsy⟩ := hloc q hq hh hb
      exact ⟨s, hs, ⟨y, hy⟩, Subtype.ext hsy⟩
    · exact ⟨a, fun haq => hb (hab q hq haq), ⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy⟩ := smul_of_height_one ha (⟨x, hx⟩ : M) hloc'
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end PositivityTheory.HtPt.Gc
