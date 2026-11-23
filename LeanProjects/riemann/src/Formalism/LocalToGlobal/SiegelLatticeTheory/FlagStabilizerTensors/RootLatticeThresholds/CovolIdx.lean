import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Formalism.L2.SG.Pf.CovolIdx

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem fd_sub (μ : Measure G) (R : Set G) (hR : μ Rᶜ = 0) (A B : Subgroup G) [Countable A]
    (hinv : ∀ s ∈ A, μ.map (fun x => s * x) = μ) (hAR : ∀ s ∈ A, ∀ r ∈ R, s * r ∈ R)
    (KA : Set G) (hKA : MeasurableSet KA) (hKAu : ∀ r ∈ R, ∃! s, s ∈ A ∧ s * r ∈ KA)
    (hfin : B.relIndex A ≠ 0) :
    ∃ KC : Set G, MeasurableSet KC ∧ (∀ r ∈ R, ∃! s, s ∈ A ⊓ B ∧ s * r ∈ KC) ∧
      μ KC = (B.relIndex A : ℝ≥0∞) * μ KA := by
  classical
  haveI : Finite (A ⧸ B.subgroupOf A) :=
    Nat.finite_of_card_ne_zero (by rw [← Subgroup.index_eq_card]; exact hfin)
  letI : Fintype (A ⧸ B.subgroupOf A) := Fintype.ofFinite _
  have hmk : ∀ q : A ⧸ B.subgroupOf A, ((Quotient.out q : A) : A ⧸ B.subgroupOf A) = q :=
    fun q => QuotientGroup.out_eq' q
  refine ⟨⋃ q : A ⧸ B.subgroupOf A, (fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA,
    MeasurableSet.iUnion fun q => measurable_const_mul _ hKA, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, ⟨ha, har⟩, hau⟩ := hKAu r hr
    obtain ⟨q, hq⟩ : ∃ q : A ⧸ B.subgroupOf A, q = ((⟨a, ha⟩ : A) : A ⧸ B.subgroupOf A) := ⟨_, rfl⟩
    have hqB : ((Quotient.out q : A) : G)⁻¹ * a ∈ B := by
      have h1 := QuotientGroup.eq.mp ((hmk q).trans hq)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    refine ⟨((Quotient.out q : A) : G)⁻¹ * a, ⟨⟨A.mul_mem (A.inv_mem (Quotient.out q).2) ha, hqB⟩, ?_⟩, ?_⟩
    · refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      show ((Quotient.out q : A) : G) * (((Quotient.out q : A) : G)⁻¹ * a * r) ∈ KA
      rw [mul_assoc, mul_inv_cancel_left]
      exact har
    · rintro s' ⟨⟨hs'A, hs'B⟩, hs'K⟩
      obtain ⟨q', hq'⟩ := Set.mem_iUnion.mp hs'K
      have hq'' : ((Quotient.out q' : A) : G) * s' * r ∈ KA := by
        rw [mul_assoc]
        exact hq'
      have e1 : ((Quotient.out q' : A) : G) * s' = a :=
        hau _ ⟨A.mul_mem (Quotient.out q').2 hs'A, hq''⟩
      have e2 : q' = q := by
        rw [hq, ← hmk q']
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        have e3 : ((((Quotient.out q' : A))⁻¹ * ⟨a, ha⟩ : A) : G) = s' :=
          (eq_inv_mul_of_mul_eq e1).symm
        rw [e3]
        exact hs'B
      subst e2
      exact eq_inv_mul_of_mul_eq e1
  · have hdisj : Pairwise (fun q q' : A ⧸ B.subgroupOf A =>
        AEDisjoint μ ((fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA)
          ((fun x => ((Quotient.out q' : A) : G) * x) ⁻¹' KA)) := by
      intro q q' hne
      show μ (_ ∩ _) = 0
      refine measure_mono_null (?_ : _ ⊆ Rᶜ) hR
      intro x hx hxR
      apply hne
      have e := (hKAu x hxR).unique ⟨(Quotient.out q).2, hx.1⟩ ⟨(Quotient.out q').2, hx.2⟩
      have e' := congrArg (fun z : A => (z : A ⧸ B.subgroupOf A)) (Subtype.ext e : Quotient.out q = Quotient.out q')
      simp only [hmk] at e'
      exact e'
    have hmeas : ∀ q : A ⧸ B.subgroupOf A,
        μ ((fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA) = μ KA := by
      intro q
      rw [← Measure.map_apply (measurable_const_mul _) hKA, hinv _ (Quotient.out q).2]
    rw [measure_iUnion₀ hdisj (fun q => (measurable_const_mul _ hKA).nullMeasurableSet), tsum_fintype]
    simp only [hmeas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem covol_commens (μ : Measure G) (R : Set G) (hR : μ Rᶜ = 0) (A B : Subgroup G) [Countable A] [Countable B]
    (hinvA : ∀ s ∈ A, μ.map (fun x => s * x) = μ) (hinvB : ∀ s ∈ B, μ.map (fun x => s * x) = μ)
    (hAR : ∀ s ∈ A, ∀ r ∈ R, s * r ∈ R) (hBR : ∀ s ∈ B, ∀ r ∈ R, s * r ∈ R)
    (KA KB : Set G) (hKA : MeasurableSet KA) (hKB : MeasurableSet KB)
    (hKAu : ∀ r ∈ R, ∃! s, s ∈ A ∧ s * r ∈ KA) (hKBu : ∀ r ∈ R, ∃! s, s ∈ B ∧ s * r ∈ KB)
    (hfinA : B.relIndex A ≠ 0) (hfinB : A.relIndex B ≠ 0) :
    μ KA * (B.relIndex A : ℝ≥0∞) = μ KB * (A.relIndex B : ℝ≥0∞) := by
  classical
  obtain ⟨K1, hK1m, hK1u, hK1μ⟩ := fd_sub μ R hR A B hinvA hAR KA hKA hKAu hfinA
  obtain ⟨K2, hK2m, hK2u, hK2μ⟩ := fd_sub μ R hR B A hinvB hBR KB hKB hKBu hfinB
  rw [inf_comm] at hK2u
  haveI : Countable ↥(A ⊓ B) :=
    Function.Injective.countable (Subgroup.inclusion_injective (inf_le_left : A ⊓ B ≤ A))
  letI : MeasurableSpace ↥(A ⊓ B) := ⊤
  haveI : MeasurableSMul ↥(A ⊓ B) G :=
    { measurable_const_smul := fun c => measurable_const_mul (c : G)
      measurable_smul_const := fun _ => measurable_from_top }
  haveI : SMulInvariantMeasure ↥(A ⊓ B) G μ := ⟨fun c s hs => by
    show μ ((fun x => (c : G) * x) ⁻¹' s) = μ s
    rw [← Measure.map_apply (measurable_const_mul _) hs, hinvA _ c.2.1]⟩
  have hRa : ∀ᵐ x ∂μ, x ∈ R := ae_iff.mpr hR
  have mkfd : ∀ K : Set G, MeasurableSet K → (∀ r ∈ R, ∃! s, s ∈ A ⊓ B ∧ s * r ∈ K) →
      IsFundamentalDomain ↥(A ⊓ B) K μ := by
    intro K hK hu
    refine ⟨hK.nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hRa] with x hx
      obtain ⟨s, ⟨hs, hsK⟩, -⟩ := hu x hx
      exact ⟨⟨s, hs⟩, hsK⟩
    · intro g h hgh
      show μ (((fun x => g • x) '' K) ∩ ((fun x => h • x) '' K)) = 0
      refine measure_mono_null (?_ : _ ⊆ Rᶜ) hR
      intro y hy hyR
      apply hgh
      obtain ⟨x1, hx1, e1⟩ := hy.1
      obtain ⟨x2, hx2, e2⟩ := hy.2
      have k1 : (g : G)⁻¹ * y ∈ K := by
        rw [← e1]
        show (g : G)⁻¹ * ((g : G) * x1) ∈ K
        rw [inv_mul_cancel_left]
        exact hx1
      have k2 : (h : G)⁻¹ * y ∈ K := by
        rw [← e2]
        show (h : G)⁻¹ * ((h : G) * x2) ∈ K
        rw [inv_mul_cancel_left]
        exact hx2
      have e := (hu y hyR).unique ⟨(A ⊓ B).inv_mem g.2, k1⟩ ⟨(A ⊓ B).inv_mem h.2, k2⟩
      exact Subtype.ext (inv_injective e)
  have key : μ K1 = μ K2 := (mkfd K1 hK1m hK1u).measure_eq (mkfd K2 hK2m hK2u)
  rw [mul_comm, ← hK1μ, key, hK2μ, mul_comm]

end Formalism.L2.SG.Pf.CovolIdx
