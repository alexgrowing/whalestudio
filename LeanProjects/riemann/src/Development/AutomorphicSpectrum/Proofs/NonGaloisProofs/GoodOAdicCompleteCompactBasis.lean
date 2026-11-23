import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateH2IffAllFiniteExtensions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.GoodCoeff

section Abstract

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
  [Algebra O LL] [IsFractionRing O LL] [TopologicalSpace LL] [T2Space LL] [IsTopologicalRing LL]

def ball (ϖ : O) (n : ℕ) : Set LL := (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ

theorem map_ne_zero_of_irreducible {ϖ : O} (hϖ : Irreducible ϖ) : algebraMap O LL ϖ ≠ 0 := by
  intro h
  exact hϖ.ne_zero (IsFractionRing.injective O LL (by simpa using h))

theorem ball_eq (ϖ : O) (n : ℕ) :
    (ball ϖ n : Set LL) = (fun x : LL => algebraMap O LL ϖ ^ n * x) '' Set.range (algebraMap O LL) := by
  ext x
  simp [ball]

theorem mem_ball_iff {ϖ : O} {n : ℕ} {x : LL} :
    x ∈ (ball ϖ n : Set LL) ↔ ∃ o : O, algebraMap O LL (ϖ ^ n * o) = x := by
  simp [ball]

theorem isOpen_ball (hop : IsOpen (Set.range (algebraMap O LL))) {ϖ : O} (hϖ : Irreducible ϖ)
    (n : ℕ) : IsOpen (ball ϖ n : Set LL) := by
  rw [ball_eq]
  exact (Homeomorph.mulLeft₀ (algebraMap O LL ϖ ^ n)
    (pow_ne_zero _ (map_ne_zero_of_irreducible hϖ))).isOpenMap _ hop

theorem isCompact_ball (hc : IsCompact (Set.range (algebraMap O LL))) (ϖ : O) (n : ℕ) :
    IsCompact (ball ϖ n : Set LL) := by
  rw [ball_eq]
  exact hc.image (continuous_const.mul continuous_id)

theorem ball_succ_subset (ϖ : O) (n : ℕ) : (ball ϖ (n + 1) : Set LL) ⊆ ball ϖ n := by
  intro x hx
  obtain ⟨o, rfl⟩ := mem_ball_iff.1 hx
  exact mem_ball_iff.2 ⟨ϖ * o, by rw [pow_succ, mul_assoc]⟩

theorem ball_antitone (ϖ : O) : Antitone (ball ϖ : ℕ → Set LL) :=
  antitone_nat_of_succ_le (ball_succ_subset ϖ)

theorem ball_subset_range (ϖ : O) (n : ℕ) : (ball ϖ n : Set LL) ⊆ Set.range (algebraMap O LL) := by
  intro x hx
  obtain ⟨o, rfl⟩ := mem_ball_iff.1 hx
  exact ⟨_, rfl⟩

theorem eq_zero_of_forall_dvd {ϖ : O} (hϖ : Irreducible ϖ) {y : O} (h : ∀ n, ϖ ^ n ∣ y) : y = 0 := by
  have hne : Ideal.span {ϖ} ≠ (⊤ : Ideal O) := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hϖ.not_isUnit
  have h0 := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne
  have : y ∈ (⨅ i : ℕ, Ideal.span {ϖ} ^ i : Ideal O) := by
    rw [Ideal.mem_iInf]
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n
  rw [h0] at this
  simpa using this

theorem basis_nhds (hop : IsOpen (Set.range (algebraMap O LL)))
    (hc : IsCompact (Set.range (algebraMap O LL))) {ϖ : O} (hϖ : Irreducible ϖ) :
    (nhds (0 : LL)).HasBasis (fun _ : ℕ => True) (ball ϖ) := by
  have hzero : ∀ n, (0 : LL) ∈ (ball ϖ n : Set LL) := fun n =>
    mem_ball_iff.2 ⟨0, by simp⟩
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    obtain ⟨U, hUt, hU, h0⟩ := mem_nhds_iff.1 ht
    have hint : (Set.range (algebraMap O LL) \ U) ∩ ⋂ n, (ball ϖ n : Set LL) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨-, hxU⟩, hx⟩
      obtain ⟨y, rfl⟩ := mem_ball_iff.1 (hx 0)
      have hy : ϖ ^ 0 * y = 0 := eq_zero_of_forall_dvd hϖ fun n => by
        obtain ⟨o, ho⟩ := mem_ball_iff.1 (hx n)
        exact ⟨o, (IsFractionRing.injective O LL ho).symm⟩
      rw [hy, map_zero] at hxU
      exact hxU h0
    obtain ⟨n, hn⟩ := (hc.diff hU).elim_directed_family_closed (ball ϖ : ℕ → Set LL)
      (fun n => (isCompact_ball hc ϖ n).isClosed) hint (ball_antitone ϖ).directed_ge
    refine ⟨n, trivial, fun x hx => hUt ?_⟩
    by_contra hxU
    have : x ∈ (Set.range (algebraMap O LL) \ U) ∩ (ball ϖ n : Set LL) :=
      ⟨⟨ball_subset_range ϖ n hx, hxU⟩, hx⟩
    rw [hn] at this
    exact this
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset ((isOpen_ball hop hϖ n).mem_nhds (hzero n)) hn

theorem sModEq_iff {ϖ : O} {n : ℕ} {x y : O} :
    x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule O O)] ↔ ϖ ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem isAdicComplete (hc : IsCompact (Set.range (algebraMap O LL))) {ϖ : O} (hϖ : Irreducible ϖ) :
    IsAdicComplete (Ideal.span {ϖ}) O := by
  have hinj := IsFractionRing.injective O LL
  haveI hH : IsHausdorff (Ideal.span {ϖ}) O := ⟨fun x hx =>
    eq_zero_of_forall_dvd hϖ fun n => by simpa using sModEq_iff.1 (hx n)⟩
  haveI hP : IsPrecomplete (Ideal.span {ϖ}) O := ⟨fun {f} hf => by
    let C : ℕ → Set LL := fun n => (fun x => algebraMap O LL (f n) + x) '' (ball ϖ n : Set LL)
    have hCc : ∀ n, IsCompact (C n) := fun n =>
      (isCompact_ball hc ϖ n).image (continuous_const.add continuous_id)
    have hmem : ∀ {n x}, x ∈ C n ↔ ∃ o : O, algebraMap O LL (f n + ϖ ^ n * o) = x := by
      intro n x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨o, rfl⟩ := mem_ball_iff.1 hy
        exact ⟨o, by simp⟩
      · rintro ⟨o, rfl⟩
        exact ⟨_, mem_ball_iff.2 ⟨o, rfl⟩, by simp⟩
    have hsub : ∀ n, C (n + 1) ⊆ C n := by
      intro n x hx
      obtain ⟨o, rfl⟩ := hmem.1 hx
      obtain ⟨d, hd⟩ := sModEq_iff.1 (hf (Nat.le_succ n))
      refine hmem.2 ⟨ϖ * o - d, ?_⟩
      congr 1
      rw [pow_succ]
      linear_combination hd
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hsub
      (fun n => ⟨algebraMap O LL (f n + ϖ ^ n * 0), hmem.2 ⟨0, rfl⟩⟩) (hCc 0)
      (fun n => (hCc n).isClosed)
    rw [Set.mem_iInter] at hx
    obtain ⟨o₀, rfl⟩ := hmem.1 (hx 0)
    refine ⟨f 0 + ϖ ^ 0 * o₀, fun n => sModEq_iff.2 ?_⟩
    obtain ⟨o, ho⟩ := hmem.1 (hx n)
    have := hinj ho
    exact ⟨-o, by linear_combination this⟩⟩
  exact { }

theorem finite_quotient (hop : IsOpen (Set.range (algebraMap O LL)))
    (hc : IsCompact (Set.range (algebraMap O LL))) {ϖ : O} (hϖ : Irreducible ϖ) :
    Finite (O ⧸ Ideal.span {ϖ}) := by
  have hinj := IsFractionRing.injective O LL
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun o : O => (fun x => algebraMap O LL o + x) '' (ball ϖ 1 : Set LL))
    (fun o => (Homeomorph.addLeft (algebraMap O LL o)).isOpenMap _ (isOpen_ball hop hϖ 1))
    (by
      rintro _ ⟨o, rfl⟩
      exact Set.mem_iUnion.2 ⟨o, 0, mem_ball_iff.2 ⟨0, by simp⟩, by simp⟩)
  refine Finite.of_surjective (fun i : t => Ideal.Quotient.mk (Ideal.span {ϖ}) i.1) ?_
  intro q
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hm := ht ⟨o, rfl⟩
  simp only [Set.mem_iUnion] at hm
  obtain ⟨i, hi, y, hy, hyo⟩ := hm
  obtain ⟨d, rfl⟩ := mem_ball_iff.1 hy
  refine ⟨⟨i, hi⟩, ?_⟩
  have h1 : i + ϖ ^ 1 * d = o := hinj (by simpa using hyo)
  refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨-d, ?_⟩)
  linear_combination h1

end Abstract

section Main

variable {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [CommRing O] [Algebra O LL]

open GlobalTheory.TateTopCompare in

theorem t2_and_compact (h : GoodO (Qp := ℚ_[l]) LL O) :
    T2Space LL ∧ IsCompact (Set.range (algebraMap O LL)) := by
  have hfd : FiniteDimensional ℚ_[l] LL := h.2.1
  obtain ⟨L', ⟨φ⟩⟩ := exists_finExt (l := l) LL
  have hmt : IsModuleTopology ℚ_[l] LL := h.2.2.1
  have htr : IsTopologicalRing LL := h.2.2.2.1
  obtain ⟨-, -, hmt', htr', -⟩ := (GlobalTheory.LocalIntegers.good_integers l L').1
  have hc1 : Continuous φ :=
    IsModuleTopology.continuous_of_linearMap φ.toLinearEquiv.toLinearMap
  have hc2 : Continuous φ.symm :=
    IsModuleTopology.continuous_of_linearMap φ.symm.toLinearEquiv.toLinearMap
  refine ⟨T2Space.of_injective_continuous φ.injective hc1, ?_⟩
  haveI : FiniteDimensional ℚ_[l] ↥L'.1 := L'.2
  haveI : ProperSpace ↥L'.1 := FiniteDimensional.proper ℚ_[l] ↥L'.1
  have hball : IsCompact (Metric.closedBall (0 : ↥L'.1) 1) := isCompact_closedBall 0 1
  have heq : Set.range (algebraMap O LL) = φ.symm '' Metric.closedBall (0 : ↥L'.1) 1 := by
    ext x
    have hn : φ x ∈ OL L' ↔ ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1 :=
      mem_integralClosure_padicInt_iff L'.1 _
    rw [mem_range_iff h L' φ x, hn]
    constructor
    · intro hx
      refine ⟨φ x, ?_, by simp⟩
      rw [mem_closedBall_zero_iff]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      rw [mem_closedBall_zero_iff] at hy
      simpa using hy
  rw [heq]
  exact hball.image hc2

open GlobalTheory.TateTop in

theorem not_isUnit_natCast (h : GoodO (Qp := ℚ_[l]) LL O) : ¬ IsUnit (l : O) := by
  rintro ⟨u, hu⟩
  have hsurj : Function.Surjective (algebraMap O LL) := by
    intro x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem h x
    obtain ⟨o, ho⟩ := hn 1
    refine ⟨(↑u⁻¹ : O) ^ n * o, ?_⟩
    have h1 : algebraMap O LL (↑u⁻¹ : O) * (l : LL) = 1 := by
      rw [← map_natCast (algebraMap O LL), ← map_mul, ← hu, Units.inv_mul, map_one]
    have h2 : algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n * ((1 : ℤ_[l]) : ℚ_[l])) = (l : LL) ^ n := by
      simp
    rw [map_mul, map_pow, ho, h2, ← mul_assoc, ← mul_pow, h1, one_pow, one_mul]
  obtain ⟨⟨hD, hdvr, hfr⟩, -⟩ := h
  exact IsDiscreteValuationRing.not_isField O
    ((RingEquiv.ofBijective (algebraMap O LL)
      ⟨IsFractionRing.injective O LL, hsurj⟩).toMulEquiv.isField (Field.toIsField LL))

theorem exists_pow_mem (h : GoodO (Qp := ℚ_[l]) LL O) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ e : ℕ, (l : O) ∈ Ideal.span {ϖ} ∧ ϖ ^ e ∈ Ideal.span {(l : O)} := by
  have hnu := not_isUnit_natCast h
  obtain ⟨⟨hD, hdvr, hfr⟩, -⟩ := h
  have hl0 : (l : O) ≠ 0 := by
    intro h0
    have h1 : (l : LL) = 0 := by
      rw [← map_natCast (algebraMap O LL), h0, map_zero]
    have h2 : ((l : ℚ_[l]) : ℚ_[l]) = 0 := (algebraMap ℚ_[l] LL).injective (by simpa using h1)
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
  refine ⟨n, ?_, Ideal.mem_span_singleton.2 ⟨u, hu.symm⟩⟩
  rcases n with _ | n
  · exact absurd (IsUnit.of_mul_eq_one _ (by simpa using hu)) hnu
  · refine Ideal.mem_span_singleton.2 ⟨ϖ ^ n * ↑u⁻¹, ?_⟩
    have : (l : O) = ϖ ^ (n + 1) * ↑u⁻¹ := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [this, pow_succ]
    ring

open GlobalTheory.TateTop in

theorem goodO_structure : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∀ ϖ : O, Irreducible ϖ → IsAdicComplete (Ideal.span {ϖ}) O ∧ Finite (O ⧸ Ideal.span {ϖ}) ∧
      IsCompact (Set.range (algebraMap O LL)) ∧
      (∃ e : ℕ, (l : O) ∈ Ideal.span {ϖ} ∧ ϖ ^ e ∈ Ideal.span {(l : O)}) ∧
      (nhds (0 : LL)).HasBasis (fun _ : ℕ => True)
        (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ) ∧
      ∀ u : ℤ_[l], algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ Set.range (algebraMap O LL) := by
  intro l _ LL _ _ _ O _ _ hG ϖ hϖ
  obtain ⟨ht2, hc⟩ := t2_and_compact hG
  have hop := hG.2.2.2.2
  have htr := hG.2.2.2.1
  obtain ⟨ι, hι⟩ := exists_ringHom hG
  have hpow := exists_pow_mem hG hϖ
  obtain ⟨⟨hD, hdvr, hfr⟩, -⟩ := hG
  exact ⟨isAdicComplete (LL := LL) hc hϖ, finite_quotient (LL := LL) hop hc hϖ, hc, hpow,
    basis_nhds hop hc hϖ, fun u => ⟨ι u, hι u⟩⟩

end Main

end GlobalTheory.CompanionTheory.GoodCoeff
