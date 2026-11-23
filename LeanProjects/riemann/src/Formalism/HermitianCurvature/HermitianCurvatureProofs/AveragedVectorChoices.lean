import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses

set_option maxHeartbeats 400000

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace PositiveSemidefiniteClosure

theorem psd_congr {X : Type} {F : Finset X} {k k' : X → X → ℂ}
    (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : IsPSD F k) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]
  rw [this]; exact hk a

theorem psd_add {X : Type} {F : Finset X} {k k' : X → X → ℂ} (hk : IsPSD F k) (hk' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [this]
  obtain ⟨h1, h2⟩ := hk a
  obtain ⟨h3, h4⟩ := hk' a
  exact ⟨by rw [Complex.add_im, h1, h3, add_zero], by rw [Complex.add_re]; exact add_nonneg h2 h4⟩

theorem psd_sum {X ι : Type} {F : Finset X} (T : Finset ι) (k : ι → X → X → ℂ)
    (h : ∀ i ∈ T, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ T, k i x y) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact A5x6.isPSD_zero F _ (fun _ _ _ _ => by simp)
  | insert i T hi ih =>
    have h1 := psd_add (h i (Finset.mem_insert_self i T))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact psd_congr (fun x _ y _ => by rw [Finset.sum_insert hi]) h1

theorem psd_scale {X : Type} {F : Finset X} {k : X → X → ℂ} (c : X → ℝ) (hk : IsPSD F k) :
    IsPSD F (fun x y => ((c x * c y : ℝ) : ℂ) * k x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (((c x * c y : ℝ) : ℂ) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, (a x * (c x : ℂ)) * conj (a y * (c y : ℂ)) * k x y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [this]; exact hk _

theorem finite_cosets {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K)) (C : Set K) (hC : IsCompact C) :
    {y : K ⧸ Λ | (Quotient.out y : K) ∈ C}.Finite := by
  have : DiscreteTopology (K ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  have h1 : (((↑) : K → K ⧸ Λ) '' C).Finite :=
    (hC.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine h1.subset ?_
  intro y hy
  exact ⟨Quotient.out y, hy, QuotientAddGroup.out_eq' y⟩

theorem out_sub_mem {K : Type} [CommRing K] (Λ : AddSubgroup K) (z : K) :
    (Quotient.out ((z : K) : K ⧸ Λ) : K) - z ∈ Λ := by
  have h : ((Quotient.out ((z : K) : K ⧸ Λ) : K) : K ⧸ Λ) = (z : K ⧸ Λ) := QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq] at h
  have := Λ.neg_mem h
  simpa [sub_eq_add_neg, add_comm] using this

theorem nat_tri (m : ℕ) : m * (m + 1) / 2 = m * (m - 1) / 2 + m := by
  cases m with
  | zero => simp
  | succ k =>
    have : (k + 1) * (k + 1 + 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

open Classical in
theorem uGram_eq_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K) (h h' : Point K) (t t' : Kˣ)
    (T : Finset (K ⧸ R.toAddSubgroup))
    (hT : ∀ x, x ∉ T → Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0) :
    uGram R ψ m cr S h h' t t' =
      ((modK R ((t : K) * (t' : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
        ∑ x ∈ T.filter (fun x => (cr x : K) ∈ S),
          Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) := by
  unfold uGram
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := T), Finset.sum_filter]
  intro x hx
  by_contra hxT
  apply hx
  simp only [Finset.mem_coe] at hxT
  show (if (cr x : K) ∈ S then Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) else 0) = 0
  rw [hT x hxT]; simp

theorem cutPSD_main : CutPSD := by
  intro hG hP hM K _ _ _ R ψ hD m cr S F hcr hsz
  classical

  have hfin : (⋃ p ∈ F, ⋃ p' ∈ F, Function.support (fun x =>
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)))).Finite := by
    refine Set.Finite.biUnion F.finite_toSet fun p hp => Set.Finite.biUnion F.finite_toSet
      fun p' hp' => ?_
    have hs : (addBlock p.1 m p.2).1.sum = (addBlock p'.1 m p'.2).1.sum := by
      simp [addBlock, hsz p hp p' hp']
    have := (hP K R ψ hD (addBlock p.1 m p.2) (addBlock p'.1 m p'.2) hs cr hcr).1
    refine this.subset ?_
    intro x hx
    simpa [Ns, pt2] using hx
  set T := hfin.toFinset with hTdef
  have hT : ∀ p ∈ F, ∀ p' ∈ F, ∀ x, x ∉ T →
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)) = 0 := by
    intro p hp p' hp' x hx
    by_contra hne
    apply hx
    rw [hTdef, Set.Finite.mem_toFinset]
    simp only [Set.mem_iUnion]
    exact ⟨p, hp, p', hp', hne⟩
  have hk : ∀ x, IsPSD F (fun p p' : Point K × Kˣ =>
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x))) := fun x =>
    A5x6.psd_comap (Kp R ψ) (fun p : Point K × Kˣ => pt2 p.1 m p.2 (cr x)) F (hG K R ψ hD _)
  have hgen : ∀ T' : Finset (K ⧸ R.toAddSubgroup), IsPSD F (fun p p' : Point K × Kˣ =>
      ((modK R (p.2 : K) ^ (m * (m + 1) / 2) * modK R (p'.2 : K) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
        ∑ x ∈ T', Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x))) := fun T' =>
    psd_scale (fun p : Point K × Kˣ => modK R (p.2 : K) ^ (m * (m + 1) / 2))
      (psd_sum T' _ fun x _ => hk x)
  constructor
  · refine psd_congr ?_ (hgen (T.filter fun x => (cr x : K) ∈ S))
    intro p hp p' hp'
    rw [uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'), (hM K R ψ hD p.2 p'.2).2,
      mul_pow]
  · refine psd_congr ?_ (hgen (T.filter fun x => ¬ (cr x : K) ∈ S))
    intro p hp p' hp'
    rw [uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'),
      uGram_eq_sum R ψ m cr Set.univ p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'),
      (hM K R ψ hD p.2 p'.2).2, mul_pow, ← mul_sub]
    congr 1
    simp only [Set.mem_univ, Finset.filter_true]
    rw [← Finset.sum_filter_add_sum_filter_not T (fun x => (cr x : K) ∈ S)]
    ring

theorem uBlock_main : UBlock := by
  intro hB hC hM K _ _ _ R ψ hD m cr S h h' t t' ht hdet
  unfold uGram
  have : ∀ x : K ⧸ R.toAddSubgroup, Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0 := by
    intro x
    by_contra hne
    have h1 := hB K R ψ hD _ _ hne
    have c1 := hC K R ψ hD (addBlock h m t) 1 (cr x)
    have c2 := hC K R ψ hD (addBlock h' m t') 1 (cr x)
    rw [hC K R ψ hD h m t] at c1
    rw [hC K R ψ hD h' m t'] at c2
    have h3 : cSize R (pt2 h m t (cr x)) = cSize R (pt2 h' m t' (cr x)) := by
      unfold cSize; rw [h1]
    unfold pt2 at h3
    rw [c1, c2, ht] at h3
    obtain ⟨hb, _⟩ := hM K R ψ hD t' t
    obtain ⟨hc, _⟩ := hM K R ψ hD (cr x) t
    have : cSize R h = cSize R h' := by
      have hb' := ne_of_gt hb
      have hc' := ne_of_gt hc
      have k1 : ((modK R (t' : K)) ^ m)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hb')
      have k2 : ((modK R ((cr x : Kˣ) : K)) ^ 1)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc')
      exact mul_right_cancel₀ k1 (mul_right_cancel₀ k2 h3)
    unfold cSize at this
    exact hdet (inv_injective this)
  simp [this]

theorem uNormBound_main : UNormBound := by
  intro hU hP hC hM _ K _ _ _ R ψ hD m n₀ F Θ hF hA t cr hcr
  classical
  obtain ⟨h1, h2, ⟨L, _, hLc, hL0⟩, h4, h5, _, _⟩ := hA
  have hfin := finite_cosets R.toAddSubgroup hD.isOpen (L : Set K) hLc
  set x₀ : K ⧸ R.toAddSubgroup := ((t : K) : K ⧸ R.toAddSubgroup) with hx₀
  set T := insert x₀ hfin.toFinset with hTdef
  have hsum : ∀ h ∈ F, ∀ h' ∈ F, ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
      Θ (t : K) h h' + ∑ x ∈ T.erase x₀, Θ (Quotient.out x) h h' := by
    intro h hh h' hh'
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · rw [← Finset.add_sum_erase T _ (Finset.mem_insert_self x₀ _)]
      congr 1
      have hr := out_sub_mem R.toAddSubgroup (t : K)
      have := h1 (t : K) _ hr
      rw [add_sub_cancel] at this
      rw [this]
    · intro x hx
      by_contra hxT
      apply hx
      apply hL0 _ _ h hh h' hh'
      intro hxL
      apply hxT
      rw [hTdef]
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Set.Finite.mem_toFinset]
      exact Or.inr hxL
  have key := psd_scale (fun h : Point K => cSize R h)
    (psd_add (psd_add h5 (psd_sum (T.erase x₀) (fun x => Θ (Quotient.out x)) fun x _ => h2 _)) (h4 t))
  refine psd_congr ?_ key
  intro h hh h' hh'
  rw [hU hP hC hM K R ψ hD m h h' t t cr ((hF h hh).trans (hF h' hh').symm) hcr, hsum h hh h' hh']
  push_cast
  ring

theorem exists_reps {K : Type} [CommRing K] (L M : AddSubgroup K) (h : M.relIndex L ≠ 0) :
    ∃ S : Finset K, IsReps S L M := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨h⟩
  have hfin : Finite (L ⧸ M.addSubgroupOf L) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : L ⧸ M.addSubgroupOf L => ((Quotient.out q : L) : K)), ?_, ?_⟩
  · intro a ha
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Quotient.out q : L).2
  · intro l hl
    have key : ∀ q : L ⧸ M.addSubgroupOf L, l - ((Quotient.out q : L) : K) ∈ M ↔
        q = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) := by
      intro q
      have e : q = ((Quotient.out q : L) : L ⧸ M.addSubgroupOf L) := (QuotientAddGroup.out_eq' q).symm
      constructor
      · intro hm
        rw [e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simpa [sub_eq_add_neg, add_comm] using hm
      · intro hq
        rw [e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hq
        simpa [sub_eq_add_neg, add_comm] using hq
    refine ⟨((Quotient.out ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) : L) : K),
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro a ⟨ha, hm⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
    rw [(key q).1 hm]

theorem card_reps {K : Type} [CommRing K] (L M : AddSubgroup K) (S : Finset K) (h : IsReps S L M) :
    S.card = M.relIndex L := by
  classical
  obtain ⟨h1, h2⟩ := h
  let f : S → L ⧸ M.addSubgroupOf L := fun a => ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L)
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have haa' : ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L) =
        ((⟨a'.1, h1 a'.1 a'.2⟩ : L) : L ⧸ M.addSubgroupOf L) := haa
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at haa'
      have hm : a'.1 - a.1 ∈ M := by simpa [sub_eq_add_neg, add_comm] using haa'
      obtain ⟨b, _, hb⟩ := h2 a'.1 (h1 a'.1 a'.2)
      have e1 := hb a.1 ⟨a.2, hm⟩
      have e2 := hb a'.1 ⟨a'.2, by simp⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        obtain ⟨a, ⟨ha, hm⟩, _⟩ := h2 l.1 l.2
        refine ⟨⟨a, ha⟩, ?_⟩
        show ((⟨a, h1 a ha⟩ : L) : L ⧸ M.addSubgroupOf L) = (l : L ⧸ M.addSubgroupOf L)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simpa [sub_eq_add_neg, add_comm] using hm
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  rw [this]; rfl

theorem lat_mem_nhds {K : Type} [CommRing K] [TopologicalSpace K] {L : AddSubgroup K}
    (h : IsLat L) : (L : Set K) ∈ 𝓝 (0 : K) := h.1.mem_nhds L.zero_mem

theorem avgDataExists_main : AvgDataExists := by
  intro hLC hKH hML hCh hLF K _ _ _ R ψ hD hn s F Om Lc hs hOm hLc
  classical
  obtain ⟨hOo, hOc, hOu, _⟩ := hOm
  have hRlat : IsLat R.toAddSubgroup := ⟨hD.isOpen, hD.isCompact⟩
  obtain ⟨L₁, hl₁, hle₁, hp₁⟩ := (hCh K R ψ hD hn).1 (Om ∪ Lc) (hOc.union hLc)
  obtain ⟨V₀, hV₀, hV₀s⟩ := compact_open_separated_add_right hOc hOo (subset_refl Om)
  obtain ⟨Λ₀, hΛ₀, hΛ₀p⟩ := hML K R ψ hD hn Om hOc hOu Set.univ Filter.univ_mem
  choose Λ hΛ hΛp using fun h : Point K => hLC K R ψ hD hn s h Om hs hOc hOu
  have hV : (V₀ ∩ (Λ₀ : Set K)) ∩ ⋂ h ∈ F, (Λ h : Set K) ∈ 𝓝 (0 : K) :=
    Filter.inter_mem (Filter.inter_mem hV₀ (lat_mem_nhds hΛ₀))
      ((Filter.biInter_finset_mem F).2 fun h _ => lat_mem_nhds (hΛ h))
  obtain ⟨L₂, hl₂, hle₂, hp₂⟩ := (hCh K R ψ hD hn).2 _ hV
  obtain ⟨A, hA⟩ := exists_reps L₂ R.toAddSubgroup (hLF K L₂ R.toAddSubgroup hl₂ hRlat)
  obtain ⟨B, hB⟩ := exists_reps R.toAddSubgroup L₁ (hLF K R.toAddSubgroup L₁ hRlat hl₁)
  refine ⟨{ L₁ := L₁, L₂ := L₂, A := A, B := B, lat₁ := hl₁, lat₂ := hl₂, le₁ := hle₁, le₂ := hle₂,
            omPerp := fun z hz => hp₁ z (Or.inl hz), cutPerp := fun z hz => hp₁ z (Or.inr hz),
            omStable := ?_, nsInv := ?_, repsA := hA, repsB := hB }⟩
  · intro z hz l hl
    exact hV₀s (Set.add_mem_add hz (hp₂ l hl).1.1)
  · intro h hh h' hh' z hz l hl
    have hlV := hp₂ l hl
    obtain ⟨hu', hmod, _⟩ := hΛ₀p z hz l hlV.1.2
    have hu := hOu z hz
    have hlh : l ∈ Λ h := by
      have := hlV.2; simp only [Set.mem_iInter] at this; exact this h hh
    have hlh' : l ∈ Λ h' := by
      have := hlV.2; simp only [Set.mem_iInter] at this; exact this h' hh'
    unfold NsK
    rw [dif_pos hu', dif_pos hu]
    unfold Ns
    have hz0 : ((hu.unit : Kˣ) : K) ∈ Om := by rw [IsUnit.unit_spec]; exact hz
    have hd : ((hu'.unit : Kˣ) : K) - ((hu.unit : Kˣ) : K) = l := by
      rw [IsUnit.unit_spec, IsUnit.unit_spec]; ring
    have e1 : modK R (((hu'.unit : Kˣ) : K) * ((hu'.unit : Kˣ) : K)) =
        modK R (((hu.unit : Kˣ) : K) * ((hu.unit : Kˣ) : K)) := by
      rw [(modulus_positive_multiplicative K R ψ hD hu'.unit hu'.unit).2,
        (modulus_positive_multiplicative K R ψ hD hu.unit hu.unit).2, IsUnit.unit_spec, IsUnit.unit_spec, hmod]
    have e2 : Kp R ψ (addBlock h s hu'.unit) (addBlock h' s hu'.unit) =
        Kp R ψ (addBlock h s hu.unit) (addBlock h' s hu.unit) := by
      rw [hΛp h hu.unit hu'.unit hz0 (by rw [hd]; exact hlh) _,
        hKH K R ψ (addBlock h' s hu'.unit) (addBlock h s hu.unit),
        hΛp h' hu.unit hu'.unit hz0 (by rw [hd]; exact hlh') _,
        ← hKH K R ψ (addBlock h' s hu.unit) (addBlock h s hu.unit)]
    rw [e1, e2]

open Classical in
theorem intLat_eq_sum {K : Type} [CommRing K] (R : Subring K) (Λ : AddSubgroup K) (Om : Set K)
    (hfin : {y : K ⧸ Λ | (Quotient.out y : K) ∈ Om}.Finite) (g : K → ℂ) :
    intLat R Λ Om g = (volL R Λ : ℂ) * ∑ y ∈ hfin.toFinset, g (Quotient.out y) := by
  unfold intLat
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    exact if_pos hy
  · intro y hy
    by_contra hyT
    apply hy
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hyT
    exact if_neg hyT

open Classical in
theorem mean_prod {K : Type} [CommRing K] (hCM : CharMean) (R : Subring K) (ψ : AddChar K ℂ)
    (L₁ L₂ : AddSubgroup K) (A B : Finset K) (le₁ : L₁ ≤ R.toAddSubgroup)
    (le₂ : R.toAddSubgroup ≤ L₂) (hA : IsReps A L₂ R.toAddSubgroup)
    (hB : IsReps B R.toAddSubgroup L₁) (a : K) (ha : a ∈ perp ψ L₁) :
    ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) =
      if a ∈ perp ψ L₂ then 1 else 0 := by
  have e : ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) =
      ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ψ (a * ρ)) * ((B.card : ℂ)⁻¹ * ∑ b ∈ B, ψ (a * b)) := by
    rw [Finset.sum_product, mul_inv]
    simp only [mul_add, AddChar.map_add_eq_mul]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [e, hCM K ψ L₁ R.toAddSubgroup B le₁ hB a ha]
  by_cases hR : a ∈ perp ψ R.toAddSubgroup
  · rw [if_pos hR, mul_one, hCM K ψ R.toAddSubgroup L₂ A le₂ hA a hR]
  · rw [if_neg hR, mul_zero, if_neg]
    intro h2
    exact hR fun l hl => h2 l (le₂ hl)

theorem cutNormEval_main : CutNormEval := by
  intro hCM hPL K _ _ _ R ψ hD hn s F Om Lc D hOc z₁ hz₁ h hh h' hh'
  classical
  obtain ⟨hPlat, _, hvol⟩ := hPL K R ψ hD hn D.L₂ D.lat₂
  have hfin := finite_cosets (perp ψ D.L₂) hPlat.1 Om hOc
  set T := hfin.toFinset with hT
  set f := NsK R ψ s h h' with hf
  set c : ℂ := ((D.A.card : ℂ) * (D.B.card : ℂ))⁻¹ with hc
  have hcc : conj c = c := by
    rw [hc, map_inv₀, map_mul, Complex.conj_natCast, Complex.conj_natCast]

  have hv : (volL R (perp ψ D.L₂) : ℂ) = (D.A.card : ℂ)⁻¹ := by
    have h1 : volL R D.L₂ = (D.A.card : ℝ) := by
      unfold volL
      rw [← card_reps D.L₂ R.toAddSubgroup D.A D.repsA, AddSubgroup.relIndex_eq_one.2 D.le₂]
      simp
    rw [h1] at hvol
    have : volL R (perp ψ D.L₂) = (D.A.card : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right hvol
    rw [this]; push_cast; rfl

  have step : ∀ p p' : K × K, ψ (-(z₁ * (p.1 + p.2))) * conj (ψ (-(z₁ * (p'.1 + p'.2)))) *
      intLat R (perp ψ D.L₂) Om (fun z => f z * ψ (z * ((p.1 + p.2) - (p'.1 + p'.2)))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          conj (ψ (((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))) := by
    intro p p'
    rw [intLat_eq_sum R _ Om hfin, mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have : ψ (-(z₁ * (p.1 + p.2))) * ψ (-(-(z₁ * (p'.1 + p'.2)))) *
        ψ ((Quotient.out y : K) * ((p.1 + p.2) - (p'.1 + p'.2))) =
        ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          ψ (-(((Quotient.out y : K) - z₁) * (p'.1 + p'.2))) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1; ring
    rw [hD.unitary, hD.unitary, ← this]
    ring
  simp only [step]
  have swap : ∑ p ∈ D.A ×ˢ D.B, ∑ p' ∈ D.A ×ˢ D.B, (volL R (perp ψ D.L₂) : ℂ) *
      ∑ y ∈ T, f (Quotient.out y) * (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          conj (ψ (((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        ((∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))) *
          conj (∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)))) := by
    simp only [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [map_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  rw [swap]
  have ind : ∀ y ∈ T, c * ∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) =
      if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then 1 else 0 := by
    intro y hy
    rw [hT, Set.Finite.mem_toFinset] at hy
    exact mean_prod hCM R ψ D.L₁ D.L₂ D.A D.B D.le₁ D.le₂ D.repsA D.repsB _
      ((perp ψ D.L₁).sub_mem (D.omPerp _ hy) (D.omPerp _ hz₁))
  have e3 : c ^ 2 * ((volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        ((∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))) *
          conj (∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then 1 else 0) := by
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    have h1 := ind y hy
    have h3 : (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) =
        (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) *
          conj (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) := by
      split_ifs <;> simp
    rw [h3, ← h1, map_mul, hcc]
    ring
  rw [e3, hv]
  congr 1
  have hout := out_sub_mem (perp ψ D.L₂) z₁
  have houteq : (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) =
      z₁ + ((Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) - z₁) := by ring
  rw [Finset.sum_eq_single ((z₁ : K) : K ⧸ perp ψ D.L₂)]
  · rw [if_pos hout, mul_one, houteq]
    exact D.nsInv h hh h' hh' z₁ hz₁ _ hout
  · intro y _ hy
    rw [if_neg, mul_zero]
    intro hm
    apply hy
    rw [← QuotientAddGroup.out_eq' y, QuotientAddGroup.eq]
    have := (perp ψ D.L₂).neg_mem hm
    simpa [sub_eq_add_neg, add_comm] using this
  · intro hn'
    exfalso
    apply hn'
    rw [hT, Set.Finite.mem_toFinset]
    show (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) ∈ Om
    rw [houteq]
    exact D.omStable z₁ hz₁ _ hout

end PositiveSemidefiniteClosure

theorem averaged_vector_norm_bound : Formalism.FourierDecayAlt.A6.UNormBound := PositiveSemidefiniteClosure.uNormBound_main

theorem cut_posSemidef : Formalism.FourierDecayAlt.A6.CutPSD := PositiveSemidefiniteClosure.cutPSD_main

theorem heads_distinct_determinant_orthogonal : Formalism.FourierDecayAlt.A6.UBlock := PositiveSemidefiniteClosure.uBlock_main

theorem averaged_vector_choices_exist : Formalism.FourierDecayAlt.A6.AvgDataExists := PositiveSemidefiniteClosure.avgDataExists_main

theorem truncated_average_norm_formula : Formalism.FourierDecayAlt.A6.CutNormEval := PositiveSemidefiniteClosure.cutNormEval_main

end Formalism.FourierDecayAlt.P
