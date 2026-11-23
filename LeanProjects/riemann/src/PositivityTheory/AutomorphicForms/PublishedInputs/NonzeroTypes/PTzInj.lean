import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem KC_anti {n r r' : ℕ} (h : r ≤ r') : KC k n r' ⊆ KC k n r := by
  rintro g ⟨hg, hP⟩
  refine ⟨hg, fun i j => ?_⟩
  obtain ⟨y, hy, e⟩ := hP i j
  exact ⟨y, Ideal.pow_le_pow_right h hy, e⟩

theorem eq_zero_of_inPow {x : k} (hx : ∀ r, InPow r x) : x = 0 := by
  obtain ⟨y, -, rfl⟩ := hx 0
  have hy : ∀ r : ℕ, y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
    intro r
    obtain ⟨z, hz, e⟩ := hx r
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  have hmem : y ∈ ⨅ r : ℕ, IsLocalRing.maximalIdeal 𝒪[k] ^ r := (Submodule.mem_iInf _).2 hy
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top] at hmem
  rw [(Ideal.mem_bot).1 hmem, map_zero]

theorem eq_one_of_KC {n : ℕ} {g : GL (Fin n) k} (hg : ∀ r, g ∈ KC k n r) : g = 1 := by
  ext i j
  have h := eq_zero_of_inPow (fun r => (hg r).2 i j)
  rw [sub_eq_zero] at h
  rw [h]
  simp [Matrix.one_apply]

theorem exists_KC_subset {n : ℕ} (hsub : ∀ r, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r))
    (hop : ∀ r, IsOpen (KC k n r)) (U : Set (GL (Fin n) k)) (hU : IsOpen U) (h1 : (1 : GL (Fin n) k) ∈ U) :
    ∃ r, KC k n r ⊆ U := by
  have hcl : ∀ r, IsClosed (KC k n r) := by
    intro r
    have := Subgroup.isClosed_of_isOpen (KCg k n r) (by rw [hsub r]; exact hop r)
    rwa [hsub r] at this
  have hst : (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ r, (KC k n r ∩ Uᶜ) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg.2
    have h1' : g = 1 := eq_one_of_KC fun r => (hg' r).1
    exact (hg' 0).2 (h1' ▸ h1)
  have hdt : Directed (· ⊇ ·) (fun r => KC k n r ∩ Uᶜ) := by
    intro a b
    exact ⟨max a b, Set.inter_subset_inter_left _ (KC_anti (le_max_left a b)),
      Set.inter_subset_inter_left _ (KC_anti (le_max_right a b))⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).elim_directed_family_closed
    (fun r => KC k n r ∩ Uᶜ) (fun r => (hcl r).inter hU.isClosed_compl) hst hdt
  refine ⟨r, fun g hg => ?_⟩
  by_contra hgU
  have : g ∈ (KO k (Fin n) : Set (GL (Fin n) k)) ∩ (KC k n r ∩ Uᶜ) := ⟨hg.1, hg, hgU⟩
  rw [hr] at this
  exact this

variable {n : ℕ} (G : Grp k n)

theorem conj_unip (ϖ : kˣ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    (G.zEl ϖ)⁻¹ * u * G.zEl ϖ ∈ unipRad k G.e := by
  have hz : G.zEl ϖ ∈ Subgroup.normalizer (unipRad k G.e : Set (GL (Fin n) k)) :=
    leviEmb_mem_normalizer k G.e _
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hz) u).1 hu
  simpa using this

theorem mem_zN (ϖ : kˣ) (u : ↥G.NO) :
    u ∈ G.zN ϖ 1 ↔ ∃ w ∈ G.NO, G.zEl ϖ * w * (G.zEl ϖ)⁻¹ = (u : GL (Fin n) k) := by
  simp [Grp.zN, Subgroup.mem_subgroupOf, Subgroup.mem_map, MulAut.conj_apply]

theorem PJ_zero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) :
    G.PJ π r 0 = 0 := by
  simp [Grp.PJ]

end UpperTheory.TNZ.Grp.P_TzInj

namespace UpperTheory.TNZ.Grp

open P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_TzInj {n : ℕ} (G : Grp k n) : TorusCentreInjectiveProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V _ _ π hs x hx hT
  have h3 : ∀ a b c : GL (Fin n) k, ∀ v : V, π (a * b * c) v = π a (π b (π c v)) := fun a b c v => by
    rw [map_mul, map_mul]; rfl
  have hQfin : Finite (↥G.NO ⧸ G.zN ϖ 1) := (hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw ϖ hϖ 1).1
  let _ : Fintype (↥G.NO ⧸ G.zN ϖ 1) := Fintype.ofFinite _

  have hsum : ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = 0 := by
    have e0 : π (G.zEl ϖ)⁻¹ (G.Tz π ϖ 1 x) = 0 := by rw [hT, map_zero]
    have e1 : G.Tz π ϖ 1 x = ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
        π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ 1) x) := by
      unfold Grp.Tz
      exact finsum_eq_sum_of_fintype _
    rw [e1, map_sum] at e0
    rw [← e0]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h3, pow_one]

  let U : Set (GL (Fin n) k) := {g | π g x = x} ∩ ⋂ c : ↥G.NO ⧸ G.zN ϖ 1,
    {g | π g (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x}
  have hUo : IsOpen U := (hs x).inter (isOpen_iInter_of_finite fun c => hs _)
  have hU1 : (1 : GL (Fin n) k) ∈ U := by
    refine ⟨by simp, Set.mem_iInter.2 fun c => ?_⟩
    simp
  obtain ⟨r0, hr0⟩ := exists_KC_subset (fun r => (hKC hccB r).1) (fun r => (hKC hccB r).2.2.1) U hUo hU1
  set r := max r0 G.lev with hr
  have hrl : G.lev ≤ r := le_max_right _ _
  have hKCr : KC k n r ⊆ U := (KC_anti (le_max_left _ _)).trans hr0
  have hPJ' := hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC V π r hrl
  have hJfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := hPJ'.1
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hlin : ∀ f : ↥G.NO ⧸ G.zN ϖ 1 → V,
      G.PJ π r (∑ c, f c) = ∑ c, G.PJ π r (f c) := by
    intro f
    simp only [Grp.PJ, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  have hsum' := congrArg (G.PJ π r) hsum
  rw [hlin, PJ_zero] at hsum'
  let c1 : ↥G.NO ⧸ G.zN ϖ 1 := QuotientGroup.mk (1 : ↥G.NO)
  rw [Finset.sum_eq_single c1] at hsum'
  ·
    have hu1 : (Quotient.out c1 : ↥G.NO) ∈ G.zN ϖ 1 := by
      have h : (QuotientGroup.mk (Quotient.out c1) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        Quotient.out_eq c1
      have := QuotientGroup.eq.1 h
      simpa using this
    obtain ⟨w, hw, hwe⟩ := (mem_zN G ϖ _).1 hu1
    have hyw : (G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ = w := by
      rw [← hwe]; group
    have hfix1 : π ((G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = x := by
      rw [hyw, hx w (hlU.1 w hw).1, (hlU.1 w hw).2, one_smul]
    rw [hfix1] at hsum'
    have hxfix : ∀ u ∈ KC k n r, π u x = x := fun u hu => (hKCr hu).1
    rw [(hPJ'.2 x hxfix).2.2 hx] at hsum'
    have hcard : (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact (smul_eq_zero.1 hsum').resolve_left hcard
  ·
    intro c _ hc
    have hfix : ∀ u ∈ KC k n r, π u (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
        π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x :=
      fun u hu => Set.mem_iInter.1 (hKCr hu).2 c
    have hmem : ((Quotient.out c : ↥G.NO) : GL (Fin n) k) ∈ unipRad k G.e ⊓ KO k (Fin n) := (Quotient.out c).2
    have hyU := conj_unip G ϖ (Subgroup.mem_inf.1 hmem).1
    have hyK : (G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ ∉ KO k (Fin n) := by
      intro hK
      apply hc
      have hin : (Quotient.out c : ↥G.NO) ∈ G.zN ϖ 1 := by
        refine (mem_zN G ϖ _).2 ⟨_, Subgroup.mem_inf.2 ⟨hyU, hK⟩, ?_⟩
        group
      have h : (QuotientGroup.mk (Quotient.out c) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        QuotientGroup.eq.2 (by simpa using inv_mem hin)
      exact (Quotient.out_eq c).symm.trans h
    exact hkill hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC hPJ V π r hrl x hx _ hfix
      (hni hcb hccB _ hyU hyK)
  · intro h
    exact absurd (Finset.mem_univ c1) h

end UpperTheory.TNZ.Grp
