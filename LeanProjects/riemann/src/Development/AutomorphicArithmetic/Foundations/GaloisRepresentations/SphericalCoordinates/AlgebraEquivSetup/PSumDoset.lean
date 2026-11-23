import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem card_fibre {G : Type} [Group G] (N P : Subgroup G) [N.Normal] (hNP : N ≤ P) (w : G) :
    Nat.card {q : G ⧸ N // (q.out : G) * w⁻¹ ∈ P} = N.relIndex P := by
  have hk := Subgroup.relIndex_ker P (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk'] at hk
  rw [hk]
  apply Nat.card_congr
  refine (Equiv.mulRight (QuotientGroup.mk w⁻¹ : G ⧸ N)).subtypeEquiv ?_
  intro q
  rw [Equiv.coe_mulRight, Subgroup.mem_map]
  beta_reduce
  have hq : q * (QuotientGroup.mk w⁻¹ : G ⧸ N) = QuotientGroup.mk ((q.out : G) * w⁻¹) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [hq]
  constructor
  · intro hp
    exact ⟨_, hp, rfl⟩
  · rintro ⟨p, hp, e⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at e
    have hm := P.mul_mem hp (hNP e)
    simpa using hm

theorem UpperTheory.Gal.W2.Seed.pSumDoset :
    SumDoset := by
  intro X _ K KM h hKM hidx hhK V _ _ Φ hΦ hnorm g
  obtain ⟨L, hL⟩ : ∃ L : Subgroup X, L = K ⊓ Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj h)) K :=
    ⟨_, rfl⟩
  rw [← hL]
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm k k.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hLK : L ≤ K := by
    rw [hL]
    exact inf_le_left
  have hKML : KM ≤ L := by
    intro u hu
    rw [hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨hKM hu, hhK u hu⟩
  have hmemL : ∀ k : K, k ∈ L.subgroupOf K ↔ h * (k : X) * h⁻¹ ∈ K := by
    intro k
    rw [Subgroup.mem_subgroupOf, hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact ⟨fun hh => hh.2, fun hh => ⟨k.2, hh⟩⟩
  have hNP : KM.subgroupOf K ≤ L.subgroupOf K := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKML hk
  have hcard : ∀ y : X, y ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      Nat.card {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K} = KM.relIndex L := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    rw [← Subgroup.relIndex_subgroupOf hLK,
      ← card_fibre (KM.subgroupOf K) (L.subgroupOf K) hNP (⟨a, ha⟩ : K)⁻¹]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro q
    rw [inv_inv, hmemL]
    have e : h * (q.out : X) * (a * h⁻¹ * b) = h * ((q.out * ⟨a, ha⟩ : K) : X) * h⁻¹ * b := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, Subgroup.mul_mem_cancel_right _ hb]
  have hnot : ∀ y : X, y ∉ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      ∀ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∉ K := by
    intro y hy q hq
    apply hy
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨((q.out : K) : X)⁻¹, K.inv_mem q.out.2, h * (q.out : X) * y, hq, by group⟩
  have hpt : ∀ x : X ⧸ K, ((KM.relIndex L : ℕ) : ℂ) •
      ((DoubleCoset.doubleCoset h⁻¹ (K : Set X) K).indicator (1 : X → ℂ) x.out • Φ (g * x.out)) =
      ∑ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
    intro x
    have hterm : ∀ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) =
          if h * (q.out : X) * x.out ∈ K then Φ (g * x.out) else 0 := by
      intro q
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x ↔ h * (q.out : X) * x.out ∈ K := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K
      · rw [if_pos hm, if_pos (hiff.mpr hm)]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg, hΦ _ hm]
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e))]
    rw [Finset.sum_congr rfl (fun q _ => hterm q), ← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    by_cases hy : x.out ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K
    · rw [Set.indicator_of_mem hy, Pi.one_apply, one_smul, hcard _ hy, Nat.cast_smul_eq_nsmul ℂ]
    · have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * x.out ∈ K} :=
        ⟨fun ⟨q, hq⟩ => hnot _ hy q hq⟩
      rw [Set.indicator_of_notMem hy, zero_smul, smul_zero, Nat.card_of_isEmpty, zero_smul]
  unfold hAct dosetInd
  rw [smul_finsum, finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
    finsum_congr hpt, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K)]
    · simp
    · intro x hx
      rw [if_neg (Ne.symm hx)]
  · intro q _
    apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K))
    intro x hx
    by_contra hne
    exact hx (if_neg (Ne.symm hne))
