import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

open TopologicalSpace

variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]

def zeroSetIn (A : Set X) (b : α → X → ℂ) (C : Fin d → α → ℂ) : Set X :=
  {z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}

theorem isClosed_meets_compact {K : Set X} (hK : IsCompact K) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) K) :
    IsClosed {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hF : Continuous fun p : (Fin d → α → ℂ) × K => fun k => ∑ j, p.1 k j * b j p.2 := by
    refine continuous_pi fun k => ?_
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun p : (Fin d → α → ℂ) × K => p.1 k j :=
      (continuous_apply j).comp ((continuous_apply k).comp continuous_fst)
    have h2 : Continuous fun p : (Fin d → α → ℂ) × K => b j (p.2 : X) :=
      (hb j).comp_continuous (continuous_subtype_val.comp continuous_snd) fun p => p.2.2
    exact h1.mul h2
  have hclosed : IsClosed {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_eq ((continuous_apply k).comp hF) continuous_const
  have himage : {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} =
      Prod.fst '' {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    ext C
    constructor
    · rintro ⟨z, hz, h⟩
      exact ⟨(C, ⟨z, hz⟩), h, rfl⟩
    · rintro ⟨⟨C', z⟩, h, rfl⟩
      exact ⟨z, z.2, h⟩
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ hclosed

theorem measurableSet_meets_inter [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X]
    {A B : Set X} (hA : IsSigmaCompact A) (hB : IsOpen B) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    MeasurableSet {C : Fin d → α → ℂ | ∃ z ∈ A ∩ B, ∀ k, ∑ j, C k j * b j z = 0} := by
  obtain ⟨K, hK, hKA⟩ := hA
  have hBσ : IsSigmaCompact B := by
    haveI := hB.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨L, hL, hLB⟩ := hBσ
  have hEq : {C : Fin d → α → ℂ | ∃ z ∈ A ∩ B, ∀ k, ∑ j, C k j * b j z = 0} =
      ⋃ n, ⋃ m, {C : Fin d → α → ℂ | ∃ z ∈ K n ∩ L m, ∀ k, ∑ j, C k j * b j z = 0} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨z, ⟨hzA, hzB⟩, h⟩
      rw [← hKA, Set.mem_iUnion] at hzA
      rw [← hLB, Set.mem_iUnion] at hzB
      obtain ⟨n, hn⟩ := hzA
      obtain ⟨m, hm⟩ := hzB
      exact ⟨n, m, z, ⟨hn, hm⟩, h⟩
    · rintro ⟨n, m, z, ⟨hn, hm⟩, h⟩
      refine ⟨z, ⟨?_, ?_⟩, h⟩
      · rw [← hKA]
        exact Set.mem_iUnion.mpr ⟨n, hn⟩
      · rw [← hLB]
        exact Set.mem_iUnion.mpr ⟨m, hm⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m => ?_
  refine (isClosed_meets_compact ((hK n).inter (hL m)) fun j => ?_).measurableSet
  refine (hb j).mono ?_
  intro z hz
  rw [← hKA]
  exact Set.mem_iUnion.mpr ⟨n, hz.1⟩

theorem natCast_le_encard_zeroSetIn_iff [T2Space X] [SecondCountableTopology X] (A : Set X)
    (b : α → X → ℂ) (C : Fin d → α → ℂ) (N : ℕ) :
    (N : ℕ∞) ≤ (zeroSetIn A b C).encard ↔
      ∃ f : Fin N → countableBasis X,
        (∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)) ∧
        ∀ i, ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0 := by
  classical
  constructor
  · intro hN
    obtain ⟨t, htZ, htN⟩ := Set.exists_subset_encard_eq hN
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htN
    haveI : Finite t := htfin.to_subtype
    have hcard : Nat.card t = N := by
      rw [Nat.card_coe_set_eq, Set.ncard_def, htN, ENat.toNat_natCast]
    let e : t ≃ Fin N := (Finite.equivFin t).trans (finCongr hcard)
    obtain ⟨U, hU, hdisj⟩ := htfin.t2_separation
    have hex : ∀ i : Fin N, ∃ v ∈ countableBasis X, (e.symm i : X) ∈ v ∧ v ⊆ U (e.symm i) :=
      fun i => (isBasis_countableBasis X).exists_subset_of_mem_open (hU _).1 (hU _).2
    choose v hvB hpv hvU using hex
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : (e.symm i : X) ≠ e.symm j := by
        intro h
        exact hij (e.symm.injective (Subtype.ext h))
      show Disjoint (v i) (v j)
      exact Disjoint.mono (hvU i) (hvU j) (hdisj (e.symm i).2 (e.symm j).2 hne)
    · intro i
      have hz : (e.symm i : X) ∈ zeroSetIn A b C := htZ (e.symm i).2
      simp only [zeroSetIn, Set.mem_ofPred_eq] at hz
      exact ⟨e.symm i, ⟨hz.1, hpv i⟩, hz.2⟩
  · rintro ⟨f, hdisj, hz⟩
    choose z hzmem hzero using hz
    have hinj : Function.Injective z := by
      intro i j h
      by_contra hij
      have hzj : z i ∈ (f j : Set X) := by
        rw [h]
        exact (hzmem j).2
      exact Set.disjoint_left.mp (hdisj i j hij) (hzmem i).2 hzj
    have hsub : ((Finset.univ.image z : Finset X) : Set X) ⊆ zeroSetIn A b C := by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨i, rfl⟩ := hx
      simp only [zeroSetIn, Set.mem_ofPred_eq]
      exact ⟨(hzmem i).1, hzero i⟩
    calc (N : ℕ∞) = ((Finset.univ.image z : Finset X) : Set X).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (zeroSetIn A b C).encard := Set.encard_le_encard hsub

theorem measurableSet_natCast_le_encard_zeroSetIn [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) (N : ℕ) :
    MeasurableSet {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} := by
  classical
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  have hEq : {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} =
      ⋃ f : Fin N → countableBasis X, ⋃ (_ : ∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)),
        ⋂ i, {C : Fin d → α → ℂ | ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    exact natCast_le_encard_zeroSetIn_iff A b C N
  rw [hEq]
  refine MeasurableSet.iUnion fun f => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun i => ?_
  exact measurableSet_meets_inter hA ((isBasis_countableBasis X).isOpen (f i).2) hb

private theorem measurable_of_natCast_le_lemma {β : Type} [MeasurableSpace β] (g : β → ℕ∞)
    (hg : ∀ N : ℕ, MeasurableSet {x | (N : ℕ∞) ≤ g x}) : Measurable g := by
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have h : g ⁻¹' {⊤} = ⋂ N : ℕ, {x | (N : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => exact ⟨fun _ _ => le_top, fun _ => rfl⟩
      | coe m =>
        constructor
        · intro hy
          exact absurd hy (ENat.natCast_ne_top m)
        · intro hy
          exfalso
          have h1 := hy (m + 1)
          norm_cast at h1
          omega
    rw [h]
    exact MeasurableSet.iInter hg
  | coe n =>
    have h : g ⁻¹' {(n : ℕ∞)} = {x | (n : ℕ∞) ≤ g x} \ {x | ((n + 1 : ℕ) : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => simp
      | coe m =>
        norm_cast
        constructor
        · intro h1
          omega
        · intro h1
          omega
    rw [h]
    exact (hg n).diff (hg (n + 1))

theorem measurable_zeroCnt_of_continuousOn [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  have hg : Measurable fun C : Fin d → α → ℂ => (zeroSetIn A b C).encard :=
    measurable_of_natCast_le_lemma _ fun N => measurableSet_natCast_le_encard_zeroSetIn hA hb N
  exact (Measurable.of_discrete (f := fun n : ℕ∞ => (n : ℝ≥0∞))).comp hg

theorem measurable_zeroCnt : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ),
    (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A →
      Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  intro d α _ U A b hb hAU hA
  exact measurable_zeroCnt_of_continuousOn hA fun j => (hb j).mono hAU

end GlobalTheory.CompanionTheory.FSCrofton
