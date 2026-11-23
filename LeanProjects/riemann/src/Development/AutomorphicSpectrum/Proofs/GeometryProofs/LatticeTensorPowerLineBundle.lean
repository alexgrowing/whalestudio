import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace LatTens

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_mem_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s)
    (ht : Λ.IsGenAt p t) : s / t ∈ regAt ξ p := by
  obtain ⟨_, hsΛ⟩ := hs
  obtain ⟨ht0, htΛ⟩ := ht
  have hmem : s ∈ Submodule.span (regAt ξ p) ({t} : Set Ω) := by
    rw [← htΛ, hsΛ]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hr' : (r : Ω) * t = s := by
    first
    | exact hr
    | simpa [Subring.smul_def] using hr
  rw [← hr', mul_div_assoc, div_self ht0, _root_.mul_one]
  exact r.2

theorem zpow_mem_of_inv_mem {R : Subring Ω} {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (a : ℤ) : u ^ a ∈ R := by
  cases a with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using pow_mem h n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow_mem h' (n + 1)

theorem tens_eq_span {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) :
    Lat.tens Λ a p = Submodule.span (regAt ξ p) {∏ i, s i ^ a i} := by
  rw [show Lat.tens Λ a p = Submodule.span (regAt ξ p)
      {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} from rfl]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨∏ i, (s' i / s i) ^ a i, ?_⟩, ?_⟩
    · refine prod_mem fun i _ => zpow_mem_of_inv_mem (div_mem_of_isGenAt (hs' i) (hs i)) ?_ (a i)
      rw [inv_div]
      exact div_mem_of_isGenAt (hs i) (hs' i)
    · show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem isGenAt_tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, tens_eq_span Λ a p s hs⟩
  exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1

theorem mem_finset_inf {I : Type} (S : Finset I) (U : I → X.Opens) (x : X) :
    x ∈ S.inf U ↔ ∀ i ∈ S, x ∈ U i := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.inf_empty]
    exact ⟨fun _ i hi => by simp at hi, fun _ => TopologicalSpace.Opens.mem_top x⟩
  · intro j S' _ ih
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]
    rw [Finset.forall_mem_insert]

theorem isGenAt_of_isFrameAt {Λ : Lat ξ Ω} {b : Fin 1 → Ω} {p : Cpt ξ} (h : Λ.IsFrameAt b p) :
    Λ.IsGenAt p (b 0) := by
  refine ⟨LinearIndependent.ne_zero 0 h.1, ?_⟩
  rw [h.2, Set.range_unique, Subsingleton.elim (default : Fin 1) 0]

theorem isFrameAt_of_isGenAt {Λ : Lat ξ Ω} {c : Ω} {p : Cpt ξ} (h : Λ.IsGenAt p c) :
    Λ.IsFrameAt (fun _ : Fin 1 => c) p := by
  refine ⟨linearIndependent_unique_iff.mpr h.1, ?_⟩
  rw [h.2, Set.range_const]

theorem tens_isVBOn (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type)
    [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (h : ∀ i, (Λ i).IsVBOn T 1 ⊤) (a : I → ℤ) :
    (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) →
      (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, fun p _ s hs => isGenAt_tens Λ a p s hs⟩
  intro p hp
  choose U hpU b _ hfr using fun i => h i p hp
  refine ⟨Finset.univ.inf U, (mem_finset_inf _ _ _).mpr fun i _ => hpU i,
    fun _ => ∏ i, b i 0 ^ a i, ?_, ?_⟩
  · have hc : (∏ i, b i 0 ^ a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
      zpow_ne_zero _ (LinearIndependent.ne_zero 0 (hfr i p hp (hpU i)).1)
    rw [Set.range_const, eq_top_iff]
    intro y _
    rw [Submodule.mem_span_singleton]
    exact ⟨y / ∏ i, b i 0 ^ a i, by rw [smul_eq_mul, div_mul_cancel₀ _ hc]⟩
  · intro q hq hqU
    rw [mem_finset_inf] at hqU
    exact isFrameAt_of_isGenAt (isGenAt_tens Λ a q (fun i => b i 0) fun i =>
      isGenAt_of_isFrameAt (hfr i q hq (hqU i (Finset.mem_univ i))))

end LatTens

end GlobalTheory.CompanionTheory.Ar
