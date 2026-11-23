import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubmodules
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubmodules

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_of_weighted {q : MRingOver S ι} {c : K → ℤ}
    (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) :
    IsMultiHomog q (fun k => (c k).toNat) := by
  by_cases h0 : q = 0
  · intro m hm
    simp [h0] at hm
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    refine (QuotPartGraded.isMultiHomog_iff q _).2 ?_
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rw [hcc]
    exact hq

theorem smul_mem_of_weighted {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    {c e : K → ℤ} (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) {m : M} (hm : m ∈ 𝓜 e) :
    q • m ∈ 𝓜 (e + c) := by
  by_cases h0 : q = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    have h := hM.2 _ e q m (isMultiHomog_of_weighted hq) hm
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical in

theorem component_smul_eq_zero {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜)
    {f : MRingOver S ι} (hf : f ∈ Module.annihilator (MRingOver S ι) M) (i : K → ℤ) {e : K → ℤ} {m : M}
    (hm : m ∈ 𝓜 e) :
    ((DirectSum.decompose (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)) f i :
      MRingOver S ι)) • m = 0 := by
  set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
  set s := (DirectSum.decompose 𝒜 f).support
  have hsum : ∑ c ∈ s, ((DirectSum.decompose 𝒜 f c : MRingOver S ι)) • m = 0 := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 f]
    exact Module.mem_annihilator.1 hf m
  obtain ⟨g, hg⟩ : ∃ g : (K → ℤ) → MRingOver S ι, ∀ c, g c = (DirectSum.decompose 𝒜 f c : MRingOver S ι) :=
    ⟨_, fun _ => rfl⟩
  have hgm : ∀ c, g c ∈ 𝒜 c := fun c => (hg c).symm ▸ (DirectSum.decompose 𝒜 f c).2
  simp only [← hg] at hsum
  suffices h : g i • m = 0 by rw [hg] at h; exact h
  by_cases hi : i ∈ s
  · have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero 𝓜).1 hM.1.submodule_iSupIndep
    have hinj : Set.InjOn (fun c : K → ℤ => e + c) s := fun a _ b _ h => add_left_cancel h
    have key := hind (s.image fun c => e + c)
      (fun d => g (d - e) • m)
      (by
        intro d hd
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hd
        rw [add_sub_cancel_left]
        exact smul_mem_of_weighted hM ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (hgm c)) hm)
      (by
        rw [Finset.sum_image hinj]
        simpa only [add_sub_cancel_left] using hsum)
      (e + i) (Finset.mem_image_of_mem _ hi)
    simpa only [add_sub_cancel_left] using key
  · rw [hg, DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero, zero_smul]

theorem mem_annihilator_of_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    (hq : ∀ e, ∀ m ∈ 𝓜 e, q • m = 0) : q ∈ Module.annihilator (MRingOver S ι) M := by
  refine Module.mem_annihilator.2 fun m => ?_
  have hm : m ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction 𝓜 (motive := fun x => q • x = 0) hm (fun e x hx => hq e x hx) (smul_zero q) ?_
  intro x y hx hy
  rw [smul_add, hx, hy, add_zero]

def prodSet (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) : Set M :=
  {y | ∃ (p : MRingOver S ι) (a : K → ℕ) (m : M) (c : K → ℤ), IsMultiHomog p a ∧ p ∈ P ∧ m ∈ 𝓜 c ∧ y = p • m}

theorem prodSet_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) :
    ∀ y ∈ prodSet 𝓜 P, ∃ c, y ∈ 𝓜 c := by
  rintro _ ⟨p, a, m, c, hp, -, hm, rfl⟩
  exact ⟨_, hM.2 a c p m hp hm⟩

theorem smul_top_eq_span {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)}
    (hP : IsMultiHomogIdeal P) :
    (P • ⊤ : Submodule (MRingOver S ι) M) = Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
  apply le_antisymm
  · obtain ⟨T, hT, hPT⟩ := hP
    rw [Submodule.smul_le]
    intro r hr n _
    rw [hPT] at hr
    induction hr using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha⟩ := hT t ht
      have htP : t ∈ P := hPT ▸ Ideal.subset_span ht
      have hn : n ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
      have h0 : t • (0 : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
        rw [smul_zero]
        exact Submodule.zero_mem _
      refine Submodule.iSup_induction 𝓜
        (motive := fun x => t • x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P))
        hn (fun e x hx => Submodule.subset_span ⟨t, a, x, e, ha, htP, hx, rfl⟩) h0 ?_
      intro x y hx hy
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_le]
    rintro _ ⟨p, a, m, c, -, hp, -, rfl⟩
    exact Submodule.smul_mem_smul hp Submodule.mem_top

theorem mem_iSup_span_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {x : M} (hx : x ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, (Submodule.span (MRingOver S ι) H).restrictScalars S ⊓ 𝓜 c := by
  have hx' := GradedSubquot.span_le_span_monTimes (S := S) (ι := ι) H hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := GradedSubquot.monTimes_homog hM hH hy
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.2 ⟨GradedSubquot.monTimes_subset_span H hy, hc⟩)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul s y _ hy => exact Submodule.smul_mem _ s hy

end GradedSubmodules

open GradedSubmodules in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in
open Classical in

theorem GradedSubmodules.proof : GradedSubmodules.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hM
  refine ⟨?_, fun P hP => ?_⟩
  ·
    set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
    refine ⟨{q | (∃ a, IsMultiHomog q a) ∧ q ∈ Module.annihilator (MRingOver S ι) M}, fun q hq => hq.1, ?_⟩
    apply le_antisymm
    · intro f hf
      rw [← DirectSum.sum_support_decompose 𝒜 f]
      refine Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨⟨_, isMultiHomog_of_weighted
        ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (DirectSum.decompose 𝒜 f i).2)⟩, ?_⟩
      exact mem_annihilator_of_homog hM fun e m hm => component_smul_eq_zero hM hf i hm
    · exact Ideal.span_le.2 fun q hq => hq.2
  · have hspan := smul_top_eq_span hM hP
    refine ⟨?_, ?_⟩
    · have hind1 : iSupIndep (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) :=
        GradedSubquot.iSupIndep_comap hM.1.submodule_iSupIndep
          ((P • ⊤ : Submodule (MRingOver S ι) M).subtype.restrictScalars S) (fun a b h => Subtype.ext h)
      have hsup1 : ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ?_
        have hx : (x : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ x.2
        have h := GradedSubquot.mem_iSup_inf hM (prodSet_homog hM P) hspan.ge x hx
        exact (show (⨆ c, ((Submodule.span (MRingOver S ι) (prodSet 𝓜 P)).comap
            (P • ⊤ : Submodule (MRingOver S ι) M).subtype).restrictScalars S ⊓
            subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c) ≤
              ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c from
          iSup_mono fun c => inf_le_right) h
      exact ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind1 hsup1,
        fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩
    · set L := (P • ⊤ : Submodule (MRingOver S ι) M) with hLdef
      set f := L.mkQ.restrictScalars S with hfdef
      have hker : LinearMap.ker f = L.restrictScalars S := by
        ext x
        simp [hfdef]
      have hind := hM.1.submodule_iSupIndep
      have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ 𝓜 c) := by
        rw [hker]
        intro x hx
        have hx' : x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ hx
        have := mem_iSup_span_inf hM (prodSet_homog hM P) hx'
        rwa [← hspan] at this
      have hind2 := GradedSubquot.iSupIndep_map_of_ker_le hind f hL
      have hsup2 : ⨆ c, quotGrading 𝓜 L c = ⊤ := by
        change ⨆ c, (𝓜 c).map f = ⊤
        rw [← Submodule.map_iSup, hM.1.submodule_iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact Submodule.mkQ_surjective L
      refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
      rintro a c p _ hp ⟨x, hx, rfl⟩
      exact ⟨p • x, hM.2 a c p x hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
