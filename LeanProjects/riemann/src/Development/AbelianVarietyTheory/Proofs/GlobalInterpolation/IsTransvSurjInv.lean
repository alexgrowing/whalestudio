import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Step

open GlobalTheory.ThetaInter

section Transversal

variable {G : Type*} [AddCommGroup G]

def IsTransv {I : Type*} (A B : AddSubgroup G) (r : I → G) : Prop :=
  (∀ i, r i ∈ A) ∧ (∀ i j, r i - r j ∈ B → i = j) ∧ ∀ a ∈ A, ∃ i, a - r i ∈ B

theorem IsTransv.finsum_eq {I J M : Type*} [AddCommMonoid M] {A B : AddSubgroup G} {r : I → G} {r' : J → G}
    (h : IsTransv A B r) (h' : IsTransv A B r') (F : G → M) (hF : ∀ a ∈ A, ∀ a' ∈ A, a - a' ∈ B → F a = F a') :
    ∑ᶠ i, F (r i) = ∑ᶠ j, F (r' j) := by
  choose e he using fun i => h'.2.2 (r i) (h.1 i)
  refine finsum_eq_of_bijective e ⟨fun i j hij => h.2.1 i j ?_, fun j => ?_⟩ fun i => hF _ (h.1 i) _ (h'.1 _) (he i)
  · have := B.sub_mem (he i) (he j)
    rwa [hij, sub_sub_sub_cancel_right] at this
  · obtain ⟨i, hi⟩ := h.2.2 (r' j) (h'.1 j)
    refine ⟨i, (h'.2.1 _ _ ?_).symm⟩
    have := B.add_mem hi (he i)
    rwa [sub_add_sub_cancel] at this

theorem IsTransv.finite {I : Type*} {A B : AddSubgroup G} {r : I → G} (h : IsTransv A B r) (hf : B.relIndex A ≠ 0) :
    Finite I := by
  have : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hf
  refine Finite.of_injective (fun i => ((⟨r i, h.1 i⟩ : A) : A ⧸ B.addSubgroupOf A)) fun i j hij => h.2.1 i j ?_
  have := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hij.symm)
  simpa [neg_add_eq_sub] using this

theorem isTransv_out (A B : AddSubgroup G) :
    IsTransv A B fun c : A ⧸ B.addSubgroupOf A => ((Quotient.out c : A) : G) := by
  refine ⟨fun c => (Quotient.out c).2, fun c c' h => ?_, fun a ha => ⟨((⟨a, ha⟩ : A) : A ⧸ B.addSubgroupOf A), ?_⟩⟩
  · rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  · have := AddSubgroup.mem_addSubgroupOf.1
      (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' ((⟨a, ha⟩ : A) : A ⧸ B.addSubgroupOf A)))
    simpa [neg_add_eq_sub] using this

theorem isTransv_surjInv {R : Type*} [Ring R] [Module R G] (A B : Submodule R G) :
    IsTransv A.toAddSubgroup B.toAddSubgroup fun z : ↥A ⧸ B.comap A.subtype =>
      ((Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z : ↥A) : G) := by
  have hs := Function.surjInv_eq (Submodule.Quotient.mk_surjective (B.comap A.subtype))
  refine ⟨fun c => Subtype.prop _, fun c c' h => ?_, fun a ha => ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩⟩
  · rw [← hs c, ← hs c', Submodule.Quotient.eq]
    exact h
  · exact (Submodule.Quotient.eq (B.comap A.subtype)).1 (hs (Submodule.Quotient.mk ⟨a, ha⟩)).symm

end Transversal

section Heis

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ}

theorem alpha_neg (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {x : V} (hx : x ∈ A) : α (-x) = α x := by
  have h0 : α 0 = 1 := by
    have h := hs.2 0 A.zero_mem 0 A.zero_mem
    rw [alpha_sq hs A.zero_mem] at h
    simpa [altE] using h
  have h1 : altE H x (-x) = 0 := by
    have := altE_swap hH x x
    simp only [altE, map_neg, Complex.neg_im] at this ⊢
    linarith
  have h := hs.2 x hx (-x) (A.neg_mem hx)
  rw [add_neg_cancel, h0, h1] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  linear_combination α (-x) * alpha_sq hs hx * (-1) - α x * h

theorem alpha_opU_congr (hH : IsHerm H) {A B : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α B) {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hxy : x - y ∈ B) (z : V) :
    α x * opU H x F z = α y * opU H y F z := by
  have h := alpha_opU_add hH hd hs hy (A.sub_mem hx hy) F z
  rw [add_sub_cancel, ← opU_mul y (α (x - y))] at h
  rw [h]
  congr 2
  funext w
  exact hF _ hxy w

end Heis

theorem cosSum_inter (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W] (V : Type)
    [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (ι : W →+ V) (As L₁ L₂ : Submodule (𝓞 E) W) (θ : V → ℂ)
    (Ξ : W → ℂ) (hH : IsHerm H) (hι : Function.Injective ι) (hdA : IsSelfDual H (As.toAddSubgroup.map ι))
    (hsA : IsSemiChar H (As.toAddSubgroup.map ι) α) (hd₁ : IsSelfDual H (L₁.toAddSubgroup.map ι))
    (hs₁ : IsSemiChar H (L₁.toAddSubgroup.map ι) α) (hθ : θ ∈ fixedBy H α (L₂.toAddSubgroup.map ι))
    (h21 : L₂ ⊓ As ≤ L₁) (h1 : L₁ ≤ (L₁ ⊓ As) ⊔ (L₁ ⊓ L₂))
    (hfin : L₂.toAddSubgroup.relIndex As.toAddSubgroup ≠ 0)
    (hΞ : ∀ t ∈ As, ∀ y ∈ L₁ ⊓ As, Ξ (t + y) = Ξ t) (z : V) :
    cosSum H α ι As L₁ (inter H α (L₂.toAddSubgroup.map ι) (L₁.toAddSubgroup.map ι) θ) Ξ z =
      ((Real.sqrt (L₂.toAddSubgroup.relIndex L₁.toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ * cosSum H α ι As L₂ θ Ξ z := by
  classical
  obtain ⟨I, r, hr, hI⟩ : ∃ (I : Type) (r : I → W), IsTransv As.toAddSubgroup L₁.toAddSubgroup r ∧
      ∀ F : W → ℂ, latSum As L₁ F = ∑ᶠ i, F (r i) := ⟨_, _, isTransv_surjInv As L₁, fun _ => rfl⟩
  obtain ⟨J, y, hy⟩ : ∃ (J : Type) (y : J → W), IsTransv (L₁ ⊓ As).toAddSubgroup L₂.toAddSubgroup y :=
    ⟨_, _, isTransv_out _ _⟩
  have hy₁ : ∀ j, y j ∈ L₁ := fun j => (hy.1 j).1
  have hyA : ∀ j, y j ∈ As := fun j => (hy.1 j).2
  have hrA : ∀ i, r i ∈ As := hr.1
  have hp : IsTransv As.toAddSubgroup L₂.toAddSubgroup fun p : I × J => r p.1 - y p.2 := by
    refine ⟨fun p => As.sub_mem (hrA _) (hyA _), fun p q h => ?_, fun a ha => ?_⟩
    · have h2 : r p.1 - y p.2 - (r q.1 - y q.2) ∈ L₁ :=
        h21 ⟨h, As.sub_mem (As.sub_mem (hrA _) (hyA _)) (As.sub_mem (hrA _) (hyA _))⟩
      have h3 : p.1 = q.1 := hr.2.1 _ _ (by
        have := L₁.add_mem h2 (L₁.sub_mem (hy₁ p.2) (hy₁ q.2))
        have e : r p.1 - y p.2 - (r q.1 - y q.2) + (y p.2 - y q.2) = r p.1 - r q.1 := by abel
        rwa [e] at this)
      refine Prod.ext h3 (hy.2.1 _ _ ?_).symm
      have e : r p.1 - y p.2 - (r q.1 - y q.2) = y q.2 - y p.2 := by rw [h3]; abel
      rw [← e]
      exact h
    · obtain ⟨i, hi⟩ := hr.2.2 a ha
      obtain ⟨j, hj⟩ := hy.2.2 (-(a - r i)) ⟨L₁.neg_mem hi, As.neg_mem (As.sub_mem ha (hrA i))⟩
      refine ⟨(i, j), ?_⟩
      have := L₂.neg_mem hj
      have e : -(-(a - r i) - y j) = a - (r i - y j) := by abel
      rwa [e] at this
  have hq : IsTransv (L₁.toAddSubgroup.map ι) (L₂.toAddSubgroup.map ι) fun j => ι (y j) := by
    refine ⟨fun j => ⟨_, hy₁ j, rfl⟩, fun i j h => hy.2.1 i j ?_, ?_⟩
    · obtain ⟨s, hs, e⟩ := h
      rw [← map_sub] at e
      rw [← hι e]
      exact hs
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (h1 ha)
      obtain ⟨j, hj⟩ := hy.2.2 u hu
      refine ⟨j, u - y j + v, L₂.add_mem hj hv.2, ?_⟩
      rw [← map_sub]
      congr 1
      abel
  have hfp := hp.finite hfin
  have : Nonempty I := let ⟨i, _⟩ := hr.2.2 0 As.zero_mem; ⟨i⟩
  have : Nonempty J := let ⟨i, _⟩ := hy.2.2 0 (L₁ ⊓ As).zero_mem; ⟨i⟩
  have : Finite I := Finite.prod_left J
  have : Finite J := Finite.prod_right I
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have mA : ∀ {t : W}, t ∈ As → ι t ∈ As.toAddSubgroup.map ι := fun ht => ⟨_, ht, rfl⟩
  have hint : inter H α (L₂.toAddSubgroup.map ι) (L₁.toAddSubgroup.map ι) θ = fun w =>
      ((Real.sqrt (L₂.toAddSubgroup.relIndex L₁.toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ j, α (ι (y j)) * opU H (ι (y j)) θ w := by
    funext w
    rw [inter, relIdx, AddSubgroup.relIndex_map_map_of_injective _ _ hι,
      (isTransv_out _ _).finsum_eq hq (fun x => α x * opU H x θ w)
        fun a ha a' ha' h => alpha_opU_congr hH hd₁ hs₁ hθ ha ha' h w, finsum_eq_sum_of_fintype]
  have hR : cosSum H α ι As L₂ θ Ξ z =
      ∑ p : I × J, Ξ (r p.1 - y p.2) * (α (ι (r p.1 - y p.2)) * opU H (-(ι (r p.1 - y p.2))) θ z) := by
    rw [← finsum_eq_sum_of_fintype]
    refine (isTransv_surjInv As L₂).finsum_eq hp (fun t => Ξ t * (α (ι t) * opU H (-(ι t)) θ z)) fun a ha a' ha' h => ?_
    have h2 := hΞ a' ha' (a - a') ⟨h21 ⟨h, As.sub_mem ha ha'⟩, As.sub_mem ha ha'⟩
    rw [add_sub_cancel] at h2
    rw [h2, ← alpha_neg hH hsA (mA ha), ← alpha_neg hH hsA (mA ha'),
      alpha_opU_congr hH hdA hsA hθ (neg_mem (mA ha)) (neg_mem (mA ha'))]
    refine ⟨-(a - a'), L₂.neg_mem h, ?_⟩
    rw [map_neg, map_sub]
    abel
  rw [hR, hint, cosSum, hI, finsum_eq_sum_of_fintype, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [opU_mul, opU_sum, mul_left_comm (α _), mul_left_comm, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := hΞ (r i) (hrA i) (-y j) (neg_mem (hy.1 j))
  rw [← sub_eq_add_neg] at h2
  have e : -ι (r i - y j) = -ι (r i) + ι (y j) := by rw [map_sub]; abel
  rw [h2, ← alpha_neg hH hsA (mA (As.sub_mem (hrA i) (hyA j))), e,
    alpha_opU_add hH hdA hsA (neg_mem (mA (hrA i))) (mA (hyA j)), alpha_neg hH hsA (mA (hrA i)), opU_mul]

end GlobalTheory.ThetaMove.Step
