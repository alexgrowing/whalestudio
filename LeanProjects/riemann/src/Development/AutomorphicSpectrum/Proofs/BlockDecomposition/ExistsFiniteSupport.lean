import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

open GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.JacExact

section Finite

variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def avg (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] : V →ₗ[ℂ] V :=
  ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q)

theorem avg_apply (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] (x : V) :
    avg τ χ M x = ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) x := by
  simp [avg, LinearMap.sum_apply]

theorem avg_translate (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [M.Normal]
    [Fintype (L ⧸ M)] (hχ : M ≤ χ.ker) (x : V) (hx : ∀ m ∈ M, τ m x = x) (n : L) :
    avg τ χ M (τ n x) = ((χ n : ℂˣ) : ℂ) • avg τ χ M x := by
  set F : L → V := fun t => (((χ t)⁻¹ : ℂˣ) : ℂ) • τ t x with hFdef
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ M) = QuotientGroup.mk b → F a = F b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ M := QuotientGroup.eq.1 hab
    have hb : b = a * (a⁻¹ * b) := by group
    have hc : χ (a⁻¹ * b) = 1 := hχ hm
    have ht : τ b x = τ a x := by
      rw [hb, map_mul, Module.End.mul_apply, hx _ hm]
    have hcb : χ b = χ a := by
      rw [hb, map_mul, hc, mul_one]
    simp only [hFdef, ht, hcb]
  have h1 : ∀ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) (τ n x)
      = ((χ n : ℂˣ) : ℂ) • F (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
    intro q
    have hq : (QuotientGroup.mk (Quotient.out q * n) : L ⧸ M)
        = QuotientGroup.mk (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [← hF _ _ hq]
    simp only [hFdef, map_mul, mul_inv, Units.val_mul, smul_smul, Module.End.mul_apply]
    congr 1
    have : ((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)
        = (((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ)) * (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [avg_apply, avg_apply, Finset.sum_congr rfl (fun q _ => h1 q), ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk n : L ⧸ M))
    (fun q => F (Quotient.out q))

theorem mem_span_of_normal (ρ : Representation ℂ L V) (σ : Representation ℂ L W) (χ : L →* ℂˣ)
    (M : Subgroup L) [M.Normal] [Finite (L ⧸ M)] (hχ : M ≤ χ.ker)
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hfi : ∀ g v, f (ρ g v) = σ g (f v))
    (v : V) (hfv : f v ∈ Submodule.span ℂ
      {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}) :
    v ∈ Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} := by
  haveI := Fintype.ofFinite (L ⧸ M)
  set S := Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} with hS
  have h1 : f (avg ρ χ M v) = avg σ χ M (f v) := by
    simp only [avg_apply, map_sum, map_smul, hfi]
  have h2 : avg σ χ M (f v) = 0 := by
    have hle : Submodule.span ℂ
        {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}
        ≤ LinearMap.ker (avg σ χ M) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨n, w, hw, rfl⟩
      show avg σ χ M _ = 0
      rw [map_sub, avg_translate σ χ M hχ w hw, map_smul, sub_self]
    exact hle hfv
  have h3 : avg ρ χ M v = 0 := hf (by rw [h1, h2, map_zero])
  have h4 : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v ∈ S := by
    have : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v
        = ∑ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v) := by
      have hq : ∀ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v)
          = v - (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ (Quotient.out q) v := by
        intro q
        rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
          neg_smul, one_smul]
        abel
      rw [Finset.sum_congr rfl (fun q _ => hq q), Finset.sum_sub_distrib, avg_apply]
      simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  rw [h3, sub_zero] at h4
  have hc : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (Submodule.smul_mem_iff _ hc).1 h4

end Finite

section Top

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_finite_support (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ) (x : W)
    (hx : x ∈ twKer σ N θ) :
    ∃ (s : Finset N) (t : Finset W), x ∈ Submodule.span ℂ
      {y | ∃ n ∈ s, ∃ w ∈ t, y = σ (n : G) w - ((θ n : ℂˣ) : ℂ) • w} := by
  classical
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, w, rfl⟩ := hy
    exact ⟨{n}, {w}, Submodule.subset_span ⟨n, by simp, w, by simp, rfl⟩⟩
  | zero => exact ⟨∅, ∅, Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, h⟩ := ha
    obtain ⟨s', t', h'⟩ := hb
    refine ⟨s ∪ s', t ∪ t', Submodule.add_mem _ ?_ ?_⟩
    · refine Submodule.span_mono ?_ h
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_left _ hn, w, Finset.mem_union_left _ hw, rfl⟩
    · refine Submodule.span_mono ?_ h'
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_right _ hn, w, Finset.mem_union_right _ hw, rfl⟩
  | smul c a _ ha =>
    obtain ⟨s, t, h⟩ := ha
    exact ⟨s, t, Submodule.smul_mem _ _ h⟩

def stabIn (τ : Representation ℂ G V) (L : Subgroup G) (x : V) : Subgroup L where
  carrier := {l | τ (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem isOpen_stabIn [TopologicalSpace G] (τ : Representation ℂ G V) (hτ : IsSmooth τ)
    (L : Subgroup G) (x : V) : IsOpen (stabIn τ L x : Set L) :=
  (hτ x).preimage continuous_subtype_val

theorem exists_open_fixing [TopologicalSpace G] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (L : Subgroup G) (O : Subgroup L)
    (hO : IsOpen (O : Set L)) (v : V) (t : Finset W) :
    ∃ M : Subgroup L, IsOpen (M : Set L) ∧ M ≤ O ∧ (∀ m ∈ M, ρ (m : G) v = v) ∧
      ∀ w ∈ t, ∀ m ∈ M, σ (m : G) w = w := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨O ⊓ stabIn ρ L v, ?_, inf_le_left, fun m hm => hm.2, by simp⟩
    rw [Subgroup.coe_inf]
    exact hO.inter (isOpen_stabIn ρ hρ L v)
  | insert a t _ ih =>
    obtain ⟨M, hM, hMO, hMv, hMt⟩ := ih
    refine ⟨M ⊓ stabIn σ L a, ?_, inf_le_left.trans hMO, fun m hm => hMv m hm.1, ?_⟩
    · rw [Subgroup.coe_inf]
      exact hM.inter (isOpen_stabIn σ hσ L a)
    · intro w hw m hm
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hm.2
      · exact hMt w hw m hm.1

theorem twKer_reflect : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W), IsSmooth ρ → IsSmooth σ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V →ₗ[ℂ] W), Function.Injective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    ∀ v : V, f v ∈ twKer σ N θ → v ∈ twKer ρ N θ := by
  intro G V W _ _ _ _ _ _ _ ρ σ hρ hσ N θ hθ hN f hf hfi v hv
  classical
  obtain ⟨s, t, hst⟩ := exists_finite_support σ N θ (f v) hv
  obtain ⟨L, hLN, hsL, hLc⟩ := hN (s.image Subtype.val) (by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact n.2)
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  let ι : L →* N := Subgroup.inclusion hLN
  have hι : Continuous ι := by
    exact Continuous.subtype_mk continuous_subtype_val _
  let χ : L →* ℂˣ := θ.comp ι
  have hχ : IsOpen (χ.ker : Set L) := by
    have : (χ.ker : Set L) = ι ⁻¹' (θ.ker : Set N) := by
      ext l
      simp [χ, MonoidHom.mem_ker]
    rw [this]
    exact hθ.preimage hι
  obtain ⟨M, hMo, hMχ, hMv, hMt⟩ := exists_open_fixing ρ σ hρ hσ L χ.ker hχ v t
  haveI : Finite (L ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo
  haveI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let C : Subgroup L := M.normalCore
  haveI : C.Normal := Subgroup.normalCore_normal M
  haveI : C.FiniteIndex := inferInstance
  haveI : Finite (L ⧸ C) := inferInstance
  have hCM : C ≤ M := Subgroup.normalCore_le M
  have hmain := mem_span_of_normal (ρ.comp L.subtype) (σ.comp L.subtype) χ C (hCM.trans hMχ) f hf
    (fun g x => hfi g x) v (by
      refine Submodule.span_mono ?_ hst
      rintro y ⟨n, hn, w, hw, rfl⟩
      have hnL : (n : G) ∈ L := hsL (by
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨n, hn, rfl⟩)
      refine ⟨⟨n, hnL⟩, w, fun m hm => hMt w hw m (hCM hm), ?_⟩
      rfl)
  refine Submodule.span_le.2 ?_ hmain
  rintro y ⟨n, u, rfl⟩
  exact Submodule.subset_span ⟨ι n, u, rfl⟩

end Top

end GlobalTheory.CompanionTheory.PRep.JacExact
