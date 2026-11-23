import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma memSum_cls {X : Type} [Group X] {K KM K₀ : Subgroup X} {h : X}
    (hc : ∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) (k₁ k₂ : K)
    (e : (QuotientGroup.mk k₁ : K ⧸ KM.subgroupOf K) = QuotientGroup.mk k₂) (y : X) :
    h * (k₁ : X) * y ∈ K₀ ↔ h * (k₂ : X) * y ∈ K₀ := by
  have hu : k₁⁻¹ * k₂ ∈ KM.subgroupOf K := QuotientGroup.eq.1 e
  have hu' : (k₁ : X)⁻¹ * k₂ ∈ KM := by simpa [Subgroup.mem_subgroupOf] using hu
  have hm := hc k₁ k₁.2 _ hu'
  have e2 : h * (k₂ : X) * y = (h * k₁ * ((k₁ : X)⁻¹ * k₂) * (h * k₁)⁻¹) * (h * k₁ * y) := by group
  rw [e2]
  exact (K₀.mul_mem_cancel_left hm).symm

private lemma memSum_eq {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X)
    [Fintype (K ⧸ KM.subgroupOf K)] :
    memFn K KM K₀ h y =
      ∑ q : K ⧸ KM.subgroupOf K, if h * (q.out : X) * y ∈ K₀ then (1 : ℂ) else 0 := by
  unfold memFn
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [Finset.sum_boole]

theorem UpperTheory.Gal.W2.Seed.pMemSum :
    MemSum := by
  intro X _ K KM K₀ h hK0 hidx hnorm hc
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hex : ∀ y, memFn K KM K₀ h y ≠ 0 →
      ∃ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∈ K₀ := by
    intro y hy
    by_contra hne
    apply hy
    have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K₀} :=
      ⟨fun ⟨q, hq⟩ => hne ⟨q, hq⟩⟩
    unfold memFn
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
  have hP : ∀ (a : K) (q : K ⧸ KM.subgroupOf K) (y : X),
      h * (q.out : X) * ((a : X) * y) ∈ K₀ ↔
        h * ((q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out : X) * y ∈ K₀ := by
    intro a q y
    have e : (QuotientGroup.mk (q.out * a) : K ⧸ KM.subgroupOf K) =
        QuotientGroup.mk (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have hcls := memSum_cls hc (q.out * a) (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out e y
    have e2 : h * (q.out : X) * ((a : X) * y) = h * ((q.out * a : K) : X) * y := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e2]
    exact hcls
  refine ⟨?_, ?_, ?_⟩
  · show IsBiInv K₀ (memFn K KM K₀ h) ∧ FinDosetSupp K₀ (memFn K KM K₀ h)
    refine ⟨?_, ?_⟩
    · intro a b g
      unfold memFn
      congr 1
      apply Nat.card_congr
      refine (Equiv.mulRight (QuotientGroup.mk (⟨a, hK0 a.2⟩ : K) : K ⧸ KM.subgroupOf K)).subtypeEquiv ?_
      intro q
      have e1 : h * (q.out : X) * ((a : X) * g * (b : X)) =
          h * (q.out : X) * (((⟨a, hK0 a.2⟩ : K) : X) * g) * (b : X) := by
        rw [← mul_assoc (h * (q.out : X))] <;> rfl
      rw [e1, Subgroup.mul_mem_cancel_right _ b.2]
      exact hP ⟨a, hK0 a.2⟩ q g
    · refine ⟨Finset.univ.image (fun q : K ⧸ KM.subgroupOf K => (h * (q.out : X))⁻¹), fun y hy => ?_⟩
      obtain ⟨q, hq⟩ := hex y hy
      refine ⟨(h * (q.out : X))⁻¹, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, 1, ⟨_, hq⟩, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      group
  · intro y hy
    obtain ⟨q, hq⟩ := hex y hy
    exact ⟨_, (q.out).2, hq⟩
  · intro V _ _ Φ hΦ g
    unfold hAct
    have hpt : ∀ x : X ⧸ K₀, memFn K KM K₀ h x.out • Φ (g * x.out) =
        ∑ q : K ⧸ KM.subgroupOf K,
          (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
      intro x
      rw [memSum_eq, Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x ↔ h * (q.out : X) * x.out ∈ K₀ := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K₀
      · rw [if_pos hm, if_pos (hiff.mpr hm), one_smul]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg]
        exact hΦ _ hm _
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e)), zero_smul]
    rw [finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
      finsum_congr hpt, finsum_sum_comm]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀)]
      · simp
      · intro x hx
        rw [if_neg (Ne.symm hx)]
    · intro q _
      apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀))
      intro x hx
      by_contra hne
      exact hx (if_neg (Ne.symm hne))
