import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelMoves

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]

section bichar
variable {c : B → A → k}

theorem IsBichar.map_zero_right (hc : IsBichar c) (b : B) : c b 0 = 1 := by
  have h := hc.2.2 b 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hc.1 b 0) (by rw [mul_one]; exact h.symm)

theorem IsBichar.map_zero_left (hc : IsBichar c) (a : A) : c 0 a = 1 := by
  have h := hc.2.1 0 0 a
  rw [add_zero] at h
  exact mul_left_cancel₀ (hc.1 0 a) (by rw [mul_one]; exact h.symm)

theorem IsBichar.map_neg_right (hc : IsBichar c) (b : B) (a : A) : c b (-a) = (c b a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hc.2.2, neg_add_cancel, hc.map_zero_right]

theorem IsBichar.map_neg_left (hc : IsBichar c) (b : B) (a : A) : c (-b) a = (c b a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hc.2.1, neg_add_cancel, hc.map_zero_left]

theorem IsBichar.map_sub_right (hc : IsBichar c) (b : B) (a a' : A) : c b (a - a') = c b a * (c b a')⁻¹ := by
  rw [sub_eq_add_neg, hc.2.2, hc.map_neg_right]

theorem IsBichar.map_sub_left (hc : IsBichar c) (b b' : B) (a : A) : c (b - b') a = c b a * (c b' a)⁻¹ := by
  rw [sub_eq_add_neg, hc.2.1, hc.map_neg_left]

end bichar

theorem ind_of_mem {S : Set A} {t : A} (h : t ∈ S) : ind (k := k) S t = 1 := by
  unfold ind; exact if_pos h

theorem ind_of_not_mem {S : Set A} {t : A} (h : t ∉ S) : ind (k := k) S t = 0 := by
  unfold ind; exact if_neg h

theorem gen_apply (c : B → A → k) (A₀ : AddSubgroup A) (a : A) (b : B) (t : A) :
    gen c A₀ a b t = c b (t + a) * ind (A₀ : Set A) (t + a) := rfl

theorem sum_reps_eq_zero {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S)
    (f : G → k) (hadd : ∀ x y, f (x + y) = f x * f y) (hM : ∀ x ∈ M, f x = 1) (g₀ : G) (hg₀ : g₀ ∈ N)
    (hne : f g₀ ≠ 1) : ∑ x ∈ S, f x = 0 := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  choose! σ hσ using hSsurj
  have hfσ : ∀ y ∈ N, f (σ y) = f y := by
    intro y hy
    have h1 : y = (y - σ y) + σ y := by abel
    conv_rhs => rw [h1, hadd, hM _ (hσ y hy).2, one_mul]
  have key : ∑ x ∈ S, f g₀ * f x = ∑ x ∈ S, f x := by
    refine Finset.sum_nbij (fun x => σ (g₀ + x)) ?_ ?_ ?_ ?_
    · intro x hx
      exact (hσ _ (N.add_mem hg₀ (hSN x hx))).1
    · intro x hx y hy hxy
      have hx' := (hσ _ (N.add_mem hg₀ (hSN x hx))).2
      have hy' := (hσ _ (N.add_mem hg₀ (hSN y hy))).2
      simp only at hxy
      rw [hxy] at hx'
      apply hSinj x hx y hy
      have := M.sub_mem hx' hy'
      have e : g₀ + x - σ (g₀ + y) - (g₀ + y - σ (g₀ + y)) = x - y := by abel
      rwa [e] at this
    · intro y hy
      have hyN : y - g₀ ∈ N := N.sub_mem (hSN y hy) hg₀
      have h1 := hσ _ hyN
      refine ⟨σ (y - g₀), h1.1, ?_⟩
      have h2 := hσ _ (N.add_mem hg₀ (hSN _ h1.1))
      simp only
      symm
      apply hSinj y hy _ h2.1
      have := M.add_mem h1.2 h2.2
      have e : y - g₀ - σ (y - g₀) + (g₀ + σ (y - g₀) - σ (g₀ + σ (y - g₀))) = y - σ (g₀ + σ (y - g₀)) := by abel
      rwa [e] at this
    · intro x hx
      rw [hfσ _ (N.add_mem hg₀ (hSN x hx)), hadd]
  rw [← Finset.mul_sum] at key
  have h2 : (f g₀ - 1) * ∑ x ∈ S, f x = 0 := by rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

theorem sum_reps_ind {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S) (t : G) :
    ∑ a ∈ S, ind (k := k) (M : Set G) (t + a) * ind (k := k) (N : Set G) (t + a) = ind (k := k) (N : Set G) t := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  by_cases ht : t ∈ N
  · obtain ⟨x, hxS, hx⟩ := hSsurj (-t) (N.neg_mem ht)
    have hxM : t + x ∈ M := by
      have := M.neg_mem hx
      have e : -(-t - x) = t + x := by abel
      rwa [e] at this
    rw [Finset.sum_eq_single x]
    · rw [ind_of_mem (show t + x ∈ (M : Set G) from hxM),
        ind_of_mem (show t + x ∈ (N : Set G) from N.add_mem ht (hSN x hxS)),
        ind_of_mem (show t ∈ (N : Set G) from ht), one_mul]
    · intro a haS hax
      have : t + a ∉ (M : Set G) := by
        intro h
        apply hax
        apply hSinj a haS x hxS
        have := M.add_mem h hx
        have e : t + a + (-t - x) = a - x := by abel
        rwa [e] at this
      rw [ind_of_not_mem this, zero_mul]
    · intro h; exact absurd hxS h
  · rw [ind_of_not_mem (show t ∉ (N : Set G) from ht)]
    apply Finset.sum_eq_zero
    intro a ha
    have : t + a ∉ (N : Set G) := by
      intro h
      apply ht
      have := N.sub_mem h (hSN a ha)
      rwa [add_sub_cancel_right] at this
    rw [ind_of_not_mem this, mul_zero]

theorem model_moves_hold : ModelMoves := by
  intro k _ A B _ _ c hc A₁ A₂ B₁ B₂ hB₁ h22 hA SA SB hSA hSB
  funext t
  have hL : (∑ a ∈ SA, ∑ b ∈ SB, rhoA a (rhoB c b (ind (A₁ : Set A)))) t
      = ∑ a ∈ SA, ∑ b ∈ SB, c b (t + a) * ind (A₁ : Set A) (t + a) := by
    simp only [Finset.sum_apply]; rfl
  have inner : ∀ u : A, ∑ b ∈ SB, c b u * ind (A₁ : Set A) u
      = (SB.card : k) * (ind (A₁ : Set A) u * ind (A₂ : Set A) u) := by
    intro u
    by_cases hu1 : u ∈ A₁
    · rw [ind_of_mem (show u ∈ (A₁ : Set A) from hu1)]
      by_cases hu2 : u ∈ A₂
      · rw [ind_of_mem (show u ∈ (A₂ : Set A) from hu2)]
        rw [Finset.sum_congr rfl (fun b hb => by rw [h22 b (hSB.1 b hb) u hu2])]
        simp
      · rw [ind_of_not_mem (show u ∉ (A₂ : Set A) from hu2)]
        have hex : ∃ b₀ ∈ B₂, c b₀ u ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hu2 (hA u hu1 hcon)
        obtain ⟨b₀, hb₀, hne⟩ := hex
        have := sum_reps_eq_zero B₁ B₂ SB hSB (fun b => c b u) (fun x y => hc.2.1 x y u)
          (fun x hx => (hB₁ x).mp hx u hu1) b₀ hb₀ hne
        simp only [mul_one, mul_zero]
        exact this
    · rw [ind_of_not_mem (show u ∉ (A₁ : Set A) from hu1)]
      simp
  rw [hL, Finset.sum_congr rfl (fun a _ => inner (t + a)), ← Finset.mul_sum, sum_reps_ind A₁ A₂ SA hSA t]
  rfl

section Heisenberg₂
variable {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T}

theorem IsHeis.WA_zero (hW : IsHeis c WA WB) (x : T) : WA 0 x = x := by rw [hW.1]; rfl

theorem IsHeis.WB_zero (hW : IsHeis c WA WB) (x : T) : WB 0 x = x := by rw [hW.2.2.1]; rfl

theorem IsHeis.WA_add (hW : IsHeis c WA WB) (a a' : A) (x : T) : WA (a + a') x = WA a (WA a' x) := by
  rw [hW.2.1]; rfl

theorem IsHeis.WB_add (hW : IsHeis c WA WB) (b b' : B) (x : T) : WB (b + b') x = WB b (WB b' x) := by
  rw [hW.2.2.2.1]; rfl

theorem IsHeis.comm (hW : IsHeis c WA WB) (a : A) (b : B) (x : T) : WA a (WB b x) = c b a • WB b (WA a x) :=
  LinearMap.congr_fun (hW.2.2.2.2 a b) x

end Heisenberg₂

theorem Sch_ext {c : B → A → k} {A₀ : AddSubgroup A} {f g : Sch c A₀ →ₗ[k] T}
    (h : ∀ a b, f ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = g ⟨gen c A₀ a b, gen_mem c A₀ a b⟩) : f = g := by
  ext ⟨Φ, hΦ⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact h a b
  | zero =>
    have e : (⟨0, Submodule.zero_mem _⟩ : Sch c A₀) = 0 := rfl
    rw [e, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Sch c A₀) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add, map_add, ihx, ihy]
  | smul r x hx ih =>
    have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : Sch c A₀) = r • ⟨x, hx⟩ := rfl
    rw [e, map_smul, map_smul, ih]

def chi (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) : Multiplicative A₀ →* k where
  toFun s := c b ((Multiplicative.toAdd s : A₀) : A)
  map_one' := hc.map_zero_right b
  map_mul' _ _ := hc.2.2 b _ _

theorem chi_apply (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) (s : A₀) :
    chi c hc A₀ b (Multiplicative.ofAdd s) = c b (s : A) := rfl

def eFam (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : A → k := by
  classical exact fun t => if h : t + i.1.out ∈ A₀ then i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) else 0

theorem eFam_of_mem (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∈ A₀) :
    eFam A₀ i t = i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) := by
  unfold eFam; exact dif_pos h

theorem eFam_of_not_mem (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∉ A₀) :
    eFam A₀ i t = 0 := by
  unfold eFam; exact dif_neg h

theorem out_sub_mem (A₀ : AddSubgroup A) (a : A) : a - (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add A₀ a
  rw [hh]
  have e : a - (a + (h : A)) = -(h : A) := by abel
  rw [e]
  exact A₀.neg_mem h.2

theorem eq_of_out_sub_mem (A₀ : AddSubgroup A) (q q' : A ⧸ A₀) (h : q.out - q'.out ∈ A₀) : q = q' := by
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
  symm
  rw [QuotientAddGroup.eq]
  have e : -q'.out + q.out = q.out - q'.out := by abel
  rwa [e]

theorem eFam_li (A₀ : AddSubgroup A) : LinearIndependent k (eFam (k := k) A₀) := by
  classical
  rw [linearIndependent_iff']
  rintro s g hg ⟨q₀, χ₀⟩ hi₀
  have hli := linearIndependent_monoidHom (Multiplicative A₀) k
  rw [linearIndependent_iff'] at hli
  refine hli ((s.filter (fun i => i.1 = q₀)).image Prod.snd) (fun χ => g (q₀, χ)) ?_ χ₀ ?_
  · funext x
    have h1 := congrFun hg (((Multiplicative.toAdd x : A₀) : A) - q₀.out)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    rw [Finset.sum_image, Finset.sum_filter]
    · refine (Finset.sum_congr rfl ?_).trans h1
      rintro ⟨q, χ⟩ _
      by_cases hq : q = q₀
      · subst hq
        have hm : ((Multiplicative.toAdd x : A₀) : A) - q.out + q.out ∈ A₀ := by
          rw [sub_add_cancel]; exact (Multiplicative.toAdd x).2
        rw [if_pos rfl, eFam_of_mem A₀ (q, χ) _ hm]
        congr 2
        apply Subtype.ext
        simp
      · have hm : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out ∉ A₀ := by
          intro hm
          apply hq
          apply eq_of_out_sub_mem A₀
          have := A₀.sub_mem hm (Multiplicative.toAdd x).2
          have e : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out - ((Multiplicative.toAdd x : A₀) : A)
              = q.out - q₀.out := by abel
          rwa [e] at this
        rw [if_neg hq, eFam_of_not_mem A₀ (q, χ) _ hm, mul_zero]
    · rintro ⟨q, χ⟩ h ⟨q', χ'⟩ h' hh
      rw [Finset.mem_coe, Finset.mem_filter] at h h'
      simp only at hh
      exact Prod.ext (h.2.trans h'.2.symm) hh
  · exact Finset.mem_image.mpr ⟨(q₀, χ₀), Finset.mem_filter.mpr ⟨hi₀, rfl⟩, rfl⟩

theorem gen_eq_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (a : A) (b : B) :
    gen c A₀ a b = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  funext t
  have h0 := out_sub_mem A₀ a
  rw [gen_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : t + (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀
  · have h' : t + a ∈ A₀ := by
      have := A₀.add_mem h h0
      have e : t + (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + a := by abel
      rwa [e] at this
    rw [ind_of_mem (show t + a ∈ (A₀ : Set A) from h'), mul_one,
      eFam_of_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, chi_apply, ← hc.2.2]
    congr 1
    change t + a = a - (QuotientAddGroup.mk a : A ⧸ A₀).out + (t + (QuotientAddGroup.mk a : A ⧸ A₀).out)
    abel
  · have h' : t + a ∉ (A₀ : Set A) := by
      intro h'
      apply h
      have := A₀.sub_mem h' h0
      have e : t + a - (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + (QuotientAddGroup.mk a : A ⧸ A₀).out := by abel
      rwa [e] at this
    rw [ind_of_not_mem h', eFam_of_not_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, mul_zero, mul_zero]

def wFam (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (A₀ : AddSubgroup A) (θ : T)
    (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : T := by
  classical exact if h : ∃ b, chi c hc A₀ b = i.2 then WA i.1.out (WB h.choose θ) else 0

theorem W_eq_wFam (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (hW : IsHeis c WA WB)
    (A₀ : AddSubgroup A) (θ : T) (hA : ∀ a ∈ A₀, WA a θ = θ) (hB : ∀ b, (∀ a ∈ A₀, c b a = 1) → WB b θ = θ)
    (a : A) (b : B) :
    WA a (WB b θ) = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  have h0 := out_sub_mem A₀ a
  have hex : ∃ b', chi c hc A₀ b' = chi c hc A₀ b := ⟨b, rfl⟩
  have hw : wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b)
      = WA (QuotientAddGroup.mk a : A ⧸ A₀).out (WB hex.choose θ) := by
    unfold wFam; exact dif_pos hex
  have hb' : ∀ s ∈ A₀, c hex.choose s = c b s := by
    intro s hs
    have := DFunLike.congr_fun hex.choose_spec (Multiplicative.ofAdd (⟨s, hs⟩ : A₀))
    rwa [chi_apply, chi_apply] at this
  have hθ : WB b θ = WB hex.choose θ := by
    have e : b = hex.choose + (b - hex.choose) := by abel
    conv_lhs => rw [e, hW.WB_add]
    rw [hB (b - hex.choose)]
    intro s hs
    rw [hc.map_sub_left, hb' s hs, mul_inv_cancel₀ (hc.1 b s)]
  rw [hw, hθ]
  have e : a = (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) := by abel
  conv_lhs => rw [e, hW.WA_add, hW.comm, hA _ h0, map_smul, hb' _ h0]

theorem Sch_le_span_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) :
    Sch c A₀ ≤ Submodule.span k (Set.range (eFam (k := k) A₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, b⟩, rfl⟩
  simp only
  rw [gen_eq_eFam c hc A₀ a b]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem xi_existence_holds : XiExists := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ hA hB
  refine ⟨(Finsupp.linearCombination k (wFam c hc WA WB A₀ θ)) ∘ₗ (eFam_li (k := k) A₀).repr ∘ₗ
    Submodule.inclusion (Sch_le_span_eFam c hc A₀), ?_, ?_⟩
  · intro a b
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact (W_eq_wFam c hc WA WB hW A₀ θ hA hB a b).symm
  · intro Xi' hXi'
    apply Sch_ext
    intro a b
    rw [hXi' a b]
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact W_eq_wFam c hc WA WB hW A₀ θ hA hB a b

theorem rhoA_gen (c : B → A → k) (A₀ : AddSubgroup A) (a' a : A) (b : B) :
    rhoA a' (gen c A₀ a b) = gen c A₀ (a' + a) b := by
  funext t
  change gen c A₀ a b (t + a') = _
  rw [gen_apply, gen_apply, add_assoc]

theorem rhoB_gen (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b' : B) (a : A) (b : B) :
    rhoB c b' (gen c A₀ a b) = (c b' a)⁻¹ • gen c A₀ a (b' + b) := by
  funext t
  change c b' t * gen c A₀ a b t = (c b' a)⁻¹ * gen c A₀ a (b' + b) t
  rw [gen_apply, gen_apply, hc.2.1, hc.2.2 b' t a]
  have h := hc.1 b' a
  field_simp

theorem rhoA_mem (c : B → A → k) (A₀ : AddSubgroup A) (a : A) : ∀ Φ ∈ Sch c A₀, rhoA a Φ ∈ Sch c A₀ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a', b⟩, rfl⟩ := hx
    simp only
    rw [rhoA_gen]
    exact gen_mem c A₀ _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

theorem rhoB_mem (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) :
    ∀ Φ ∈ Sch c A₀, rhoB c b Φ ∈ Sch c A₀ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b'⟩, rfl⟩ := hx
    simp only
    rw [rhoB_gen c hc]
    exact Submodule.smul_mem _ _ (gen_mem c A₀ _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

theorem xi_intersection_holds : XiInter := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ Xi hXi Φ hΦ
  constructor
  · intro a
    refine ⟨rhoA_mem c A₀ a Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoA a).restrict (rhoA_mem c A₀ a) = WA a ∘ₗ Xi := by
      apply Sch_ext
      intro a' b
      have e : (rhoA a).restrict (rhoA_mem c A₀ a) ⟨gen c A₀ a' b, gen_mem c A₀ a' b⟩
          = ⟨gen c A₀ (a + a') b, gen_mem c A₀ (a + a') b⟩ := Subtype.ext (rhoA_gen c A₀ a a' b)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, hXi, hW.WA_add]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩
  · intro b
    refine ⟨rhoB_mem c hc A₀ b Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoB c b).restrict (rhoB_mem c hc A₀ b) = WB b ∘ₗ Xi := by
      apply Sch_ext
      intro a b'
      have e : (rhoB c b).restrict (rhoB_mem c hc A₀ b) ⟨gen c A₀ a b', gen_mem c A₀ a b'⟩
          = (c b a)⁻¹ • ⟨gen c A₀ a (b + b'), gen_mem c A₀ a (b + b')⟩ := Subtype.ext (rhoB_gen c hc A₀ b a b')
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, map_smul, hXi, hW.WB_add, hW.comm, smul_smul,
        inv_mul_cancel₀ (hc.1 b a), one_smul]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩

theorem Xi_of_eq_sum {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) {ι : Type*} (s : Finset ι) (r : ι → k) (a : ι → A)
    (b : ι → B) (Φ : A → k) (hΦ : Φ = ∑ i ∈ s, r i • gen c A₀ (a i) (b i)) :
    ∃ h : Φ ∈ Sch c A₀, Xi ⟨Φ, h⟩ = ∑ i ∈ s, r i • WA (a i) (WB (b i) θ) := by
  subst hΦ
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _), ?_⟩
  have e : (⟨∑ i ∈ s, r i • gen c A₀ (a i) (b i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _)⟩ : Sch c A₀)
      = ∑ i ∈ s, r i • ⟨gen c A₀ (a i) (b i), gen_mem c A₀ (a i) (b i)⟩ := by
    apply Subtype.ext
    simp
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hXi]

theorem lattice_moves_hold : Moves := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ A₁ B₀ B₁ θ Xi hXi hB₀ h11 hA SA SB hSA hSB hcard
  have hM : ∑ a ∈ SA, ∑ b ∈ SB, gen c A₀ a b = (SB.card : k) • ind (A₁ : Set A) :=
    model_moves_hold k A B c hc A₀ A₁ B₀ B₁ hB₀ h11 hA SA SB hSA hSB
  have hexp : ind (A₁ : Set A) = ∑ i ∈ SA ×ˢ SB, (SB.card : k)⁻¹ • gen c A₀ i.1 i.2 := by
    rw [← Finset.smul_sum, Finset.sum_product, hM, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  obtain ⟨h, hval⟩ := Xi_of_eq_sum hXi (SA ×ˢ SB) (fun _ => (SB.card : k)⁻¹) Prod.fst Prod.snd _ hexp
  refine ⟨h, ?_⟩
  rw [hval, ← Finset.smul_sum, smul_smul, mul_inv_cancel₀ hcard, one_smul, Finset.sum_product]

theorem IsXi.fixed {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) (hc : IsBichar c) (hW : IsHeis c WA WB) (a : A)
    (ha : a ∈ A₀) : WA a θ = θ := by
  have e : gen c A₀ a 0 = gen c A₀ 0 0 := by
    funext t
    rw [gen_apply, gen_apply, hc.map_zero_left, hc.map_zero_left, add_zero]
    by_cases ht : t ∈ A₀
    · rw [ind_of_mem (show t ∈ (A₀ : Set A) from ht), ind_of_mem (show t + a ∈ (A₀ : Set A) from A₀.add_mem ht ha)]
    · have : t + a ∉ (A₀ : Set A) := by
        intro h
        apply ht
        have := A₀.sub_mem h ha
        rwa [add_sub_cancel_right] at this
      rw [ind_of_not_mem (show t ∉ (A₀ : Set A) from ht), ind_of_not_mem this]
  have h1 := hXi a 0
  have h2 := hXi 0 0
  have e' : (⟨gen c A₀ a 0, gen_mem c A₀ a 0⟩ : Sch c A₀) = ⟨gen c A₀ 0 0, gen_mem c A₀ 0 0⟩ := Subtype.ext e
  rw [e', h2, hW.WB_zero, hW.WA_zero] at h1
  exact h1.symm

theorem fourier_transform_identity_holds : Fourier := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ A₂ B₀ B₂ θ Xi hXi h20 hB₀ hB₂ hA SA SB hSA hSB hcard Φ hsupp hinv
  have hreps0 : IsRepsG A₀ A₂ ({0} : Finset A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact A₂.zero_mem
    · intro x hx y hy _
      rw [Finset.mem_singleton] at hx hy
      rw [hx, hy]
    · intro y hy
      exact ⟨0, Finset.mem_singleton_self 0, by rw [sub_zero]; exact h20 hy⟩
  have hM : ∑ b ∈ SB, gen c A₀ 0 b = (SB.card : k) • ind (A₂ : Set A) := by
    have := model_moves_hold k A B c hc A₀ A₂ B₀ B₂ hB₀ (fun b hb a ha => (hB₂ b).mp hb a ha) hA {0} SB hreps0 hSB
    rwa [Finset.sum_singleton] at this
  have hexp : Φ = ∑ i ∈ SA ×ˢ SB, (Φ i.1 * (SB.card : k)⁻¹) • gen c A₀ (-i.1) i.2 := by
    funext u
    rw [Finset.sum_product, Finset.sum_apply]
    have hin : ∀ t : A, (∑ b ∈ SB, (Φ t * (SB.card : k)⁻¹) • gen c A₀ (-t) b) u = Φ t * ind (A₂ : Set A) (u - t) := by
      intro t
      have h1 := congrFun hM (u - t)
      rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [← Finset.smul_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have h2 : ∑ b ∈ SB, gen c A₀ (-t) b u = ∑ b ∈ SB, gen c A₀ 0 b (u - t) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gen_apply, gen_apply, add_zero, sub_eq_add_neg]
      rw [h2, h1, mul_assoc, ← mul_assoc _ (SB.card : k), inv_mul_cancel₀ hcard, one_mul]
    rw [Finset.sum_congr rfl (fun t _ => hin t)]
    by_cases hu : u ∈ A₀
    · obtain ⟨x, hxS, hx⟩ := hSA.2.2 u hu
      rw [Finset.sum_eq_single x]
      · rw [ind_of_mem (show u - x ∈ (A₂ : Set A) from hx), mul_one]
        have := hinv x (u - x) hx
        rwa [add_sub_cancel] at this
      · intro t htS htx
        have : u - t ∉ (A₂ : Set A) := by
          intro h
          apply htx
          apply hSA.2.1 t htS x hxS
          have := A₂.sub_mem hx h
          have e : u - x - (u - t) = t - x := by abel
          rwa [e] at this
        rw [ind_of_not_mem this, mul_zero]
      · intro h; exact absurd hxS h
    · rw [hsupp u hu]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      have : u - t ∉ (A₂ : Set A) := by
        intro h
        apply hu
        have := A₀.add_mem (h20 h) (hSA.1 t ht)
        rwa [sub_add_cancel] at this
      rw [ind_of_not_mem this, mul_zero]
  obtain ⟨h, hval⟩ := Xi_of_eq_sum hXi (SA ×ˢ SB) (fun i => Φ i.1 * (SB.card : k)⁻¹) (fun i => -i.1) Prod.snd _ hexp
  refine ⟨h, ?_⟩
  rw [hval, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hW.comm, hXi.fixed hc hW (-t) (A₀.neg_mem (hSA.1 t ht)), hc.map_neg_right, smul_smul]
  congr 1
  ring

theorem Moves_of (_h1 : ModelMoves) (_h3 : XiInter) : Moves := lattice_moves_hold

theorem Fourier_of (_h1 : ModelMoves) (_h3 : XiInter) : Fourier := fourier_transform_identity_holds

end Formalism.L2.PairingIndexBounds.Mv
