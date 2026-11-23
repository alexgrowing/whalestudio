import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

namespace GlobalTheory.CompanionTheory.TwistedAverage

open GlobalTheory.PRep

section Coset

variable {H V : Type} [Group H] [AddCommGroup V]

theorem sum_out_refine {N K : Subgroup H} (hNK : N ≤ K) [Fintype (H ⧸ N)] [Fintype (H ⧸ K)]
    [Fintype (K ⧸ N.subgroupOf K)] (f : H → V) (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ q : H ⧸ N, f q.out = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
  have h1 : ∀ q : H ⧸ N, f q.out = f ((Subgroup.quotientEquivProdOfLE hNK q).1).out := by
    intro q
    have hq : (Subgroup.quotientEquivProdOfLE hNK q).1 = (QuotientGroup.mk q.out : H ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K q.out
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f q.out
      = ∑ q : H ⧸ N, f ((Subgroup.quotientEquivProdOfLE hNK q).1).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ p : (H ⧸ K) × (K ⧸ N.subgroupOf K), f p.1.out :=
        Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hNK) (fun p => f p.1.out)
    _ = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ]
        rw [Finset.smul_sum]

theorem sum_out_mul_right (N : Subgroup H) [N.Normal] [Fintype (H ⧸ N)] (f : H → V)
    (hf : ∀ x, ∀ k ∈ N, f (x * k) = f x) (l : H) :
    ∑ q : H ⧸ N, f (q.out * l) = ∑ q : H ⧸ N, f q.out := by
  have h1 : ∀ q : H ⧸ N, f (q.out * l) = f (q * (QuotientGroup.mk l : H ⧸ N)).out := by
    intro q
    have hq : q * (QuotientGroup.mk l : H ⧸ N) = QuotientGroup.mk (q.out * l) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (q.out * l)
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f (q.out * l)
      = ∑ q : H ⧸ N, f (q * (QuotientGroup.mk l : H ⧸ N)).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ q : H ⧸ N, f q.out :=
        Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk l : H ⧸ N)) (fun q => f q.out)

end Coset

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def twOrbit (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) (t : L) : V :=
  (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) x

def stabKer (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) : Subgroup L where
  carrier := {l | ρ (l : G) x = x ∧ θ l = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, by rw [map_mul, ha', hb', one_mul]⟩
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, by rw [map_inv, ha', inv_one]⟩
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem twOrbit_mul_right (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V)
    (t k : L) (hk : k ∈ stabKer ρ L θ x) : twOrbit ρ L θ x (t * k) = twOrbit ρ L θ x t := by
  obtain ⟨h1, h2⟩ := hk
  simp only [twOrbit]
  rw [map_mul, h2, mul_one, Subgroup.coe_mul, map_mul, Module.End.mul_apply, h1]

theorem twOrbit_gen (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (w : V) (l t : L) :
    twOrbit ρ L θ (ρ (l : G) w - (θ l : ℂ) • w) t =
      (θ l : ℂ) • (twOrbit ρ L θ w (t * l) - twOrbit ρ L θ w t) := by
  simp only [twOrbit]
  have h : (θ l : ℂ) * (((θ (t * l))⁻¹ : ℂˣ) : ℂ) = (((θ t)⁻¹ : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, map_mul, mul_inv, mul_comm (θ t)⁻¹, mul_inv_cancel_left]
  rw [smul_sub, smul_smul, h, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub, map_smul,
    smul_sub, smul_smul, smul_smul, mul_comm]

theorem twOrbit_add (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x y : V) (t : L) :
    twOrbit ρ L θ (x + y) t = twOrbit ρ L θ x t + twOrbit ρ L θ y t := by
  simp only [twOrbit, map_add, smul_add]

theorem twOrbit_smul (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (c : ℂ) (x : V)
    (t : L) : twOrbit ρ L θ (c • x) t = c • twOrbit ρ L θ x t := by
  simp only [twOrbit, map_smul]
  rw [smul_comm]

section Top

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (L : Subgroup G)
    (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    IsOpen (stabKer ρ L θ x : Set L) := by
  have h1 : IsOpen {l : L | ρ (l : G) x = x} := (hρ x).preimage continuous_subtype_val
  have h2 : (stabKer ρ L θ x : Set L) = {l : L | ρ (l : G) x = x} ∩ (θ.ker : Set L) := by
    ext l
    simp [stabKer, MonoidHom.mem_ker]
  rw [h2]
  exact h1.inter hθ

theorem finiteIndex_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    (stabKer ρ L θ x).FiniteIndex := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  haveI : Finite (L ⧸ stabKer ρ L θ x) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_stabKer hρ L θ hθ x)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_sum_eq_zero {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {v : V}
    (hv : v ∈ twKer ρ L θ) :
    ∃ M : Subgroup L, M.FiniteIndex ∧ ∀ (N : Subgroup L) [N.Normal] [Fintype (L ⧸ N)], N ≤ M →
      ∑ q : L ⧸ N, twOrbit ρ L θ v q.out = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, w, rfl⟩ := hx
    refine ⟨stabKer ρ L θ w, finiteIndex_stabKer hρ hL θ hθ w, ?_⟩
    intro N _ _ hN
    have hf : ∀ x, ∀ k ∈ N, twOrbit ρ L θ w (x * k) = twOrbit ρ L θ w x :=
      fun x k hk => twOrbit_mul_right ρ L θ w x k (hN hk)
    simp only [twOrbit_gen]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib,
      sum_out_mul_right N (twOrbit ρ L θ w) hf l, sub_self, smul_zero]
  | zero =>
    refine ⟨⊤, inferInstance, ?_⟩
    intro N _ _ _
    simp [twOrbit]
  | add x y _ _ hx hy =>
    obtain ⟨M₁, h₁, s₁⟩ := hx
    obtain ⟨M₂, h₂, s₂⟩ := hy
    refine ⟨M₁ ⊓ M₂, inferInstance, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_add]
    rw [Finset.sum_add_distrib, s₁ N (hN.trans inf_le_left), s₂ N (hN.trans inf_le_right), add_zero]
  | smul c x _ hx =>
    obtain ⟨M, h, s⟩ := hx
    refine ⟨M, h, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_smul]
    rw [← Finset.smul_sum, s N hN, smul_zero]

theorem mem_twKer_iff_average (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (v : V) :
    v ∈ twKer ρ L θ ↔ ∃ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) ∧
      (∀ x ∈ K, ρ (x : G) v = v) ∧ (∀ x ∈ K, θ x = 1) ∧
      (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) ∧
      ∑ t ∈ T, (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ t v = 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hθ hv
    haveI hK : (stabKer ρ L θ v).FiniteIndex := finiteIndex_stabKer hρ hL θ hθ v
    haveI : Fintype (L ⧸ stabKer ρ L θ v) := Fintype.ofFinite _
    refine ⟨stabKer ρ L θ v, (Finset.univ : Finset (L ⧸ stabKer ρ L θ v)).image Quotient.out,
      isOpen_stabKer hρ L θ hθ v,
      fun x hx => hx.1, fun x hx => hx.2, ?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk x : L ⧸ stabKer ρ L θ v).out, ⟨Finset.mem_image_of_mem _
        (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      · rintro t ⟨ht, hx⟩
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        have : q = (QuotientGroup.mk x : L ⧸ stabKer ρ L θ v) := by
          rw [← QuotientGroup.out_eq' q]
          exact QuotientGroup.eq.2 hx
        rw [this]
    · rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
      set C : Subgroup L := (M ⊓ stabKer ρ L θ v).normalCore with hC
      haveI : C.Normal := Subgroup.normalCore_normal _
      haveI : C.FiniteIndex := inferInstance
      haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
      have hCM : C ≤ M ⊓ stabKer ρ L θ v := Subgroup.normalCore_le _
      haveI : Finite (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := inferInstance
      haveI : Fintype (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := Fintype.ofFinite _
      have h0 := hsum C (hCM.trans inf_le_left)
      rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
        (fun x k hk => twOrbit_mul_right ρ L θ v x k hk)] at h0
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      · exact h0
  · rintro ⟨K, T, -, -, -, hT, hsum⟩
    have hne : T.Nonempty := by
      obtain ⟨t, ⟨ht, -⟩, -⟩ := hT 1
      exact ⟨t, ht⟩
    have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne.card_pos.ne'
    have hmem : ∀ t : L, v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v ∈ twKer ρ L θ := by
      intro t
      have hg : ρ (t : G) v - (θ t : ℂ) • v ∈ twKer ρ L θ := Submodule.subset_span ⟨t, v, rfl⟩
      have := (twKer ρ L θ).smul_mem (-(((θ t)⁻¹ : ℂˣ) : ℂ)) hg
      convert this using 1
      rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
        neg_smul, one_smul]
      abel
    have hs : (T.card : ℂ) • v = ∑ t ∈ T, (v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have h1 : (T.card : ℂ) • v ∈ twKer ρ L θ := hs ▸ Submodule.sum_mem _ fun t _ => hmem t
    exact ((twKer ρ L θ).smul_mem_iff hc).1 h1

end Top

end GlobalTheory.CompanionTheory.TwistedAverage
