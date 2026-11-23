import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical Pointwise

noncomputable section
namespace GlobalTheory.CrossOrbit

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ]

def crossTerm (φ : Γ →* MulAut G) (a b : G → ℂ) (S : Finset Γ) (g : G) : ℂ :=
  ∏ t : Γ, if t ∈ S then a (φ t⁻¹ g) else b (φ t⁻¹ g)

theorem crossTerm_shift (φ : Γ →* MulAut G) (a b : G → ℂ) (S : Finset Γ) (u : Γ) (g : G) :
    crossTerm φ a b S (φ u⁻¹ g) = crossTerm φ a b (u • S) g := by
  unfold crossTerm
  refine Fintype.prod_equiv (Equiv.mulLeft u) _ _ fun t => ?_
  have hm : u * t ∈ u • S ↔ t ∈ S := by rw [← smul_eq_mul]; exact Finset.smul_mem_smul_finset_iff u
  have hφ : ∀ x : G, φ (u * t)⁻¹ x = φ t⁻¹ (φ u⁻¹ x) := fun x => by
    rw [mul_inv_rev, map_mul, MulAut.mul_apply]
  simp only [Equiv.coe_mulLeft, hm, hφ]

theorem prod_inv_reindex (f : Γ → ℂ) : ∏ t : Γ, f t = ∏ t : Γ, f t⁻¹ :=
  Fintype.prod_equiv (Equiv.inv Γ) _ _ fun t => by simp

theorem prod_add_eq_sum (φ : Γ →* MulAut G) (a b : G → ℂ) (g : G) :
    ∏ t : Γ, (a (φ t g) + b (φ t g)) = ∑ S : Finset Γ, crossTerm φ a b S g := by
  rw [prod_inv_reindex, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold crossTerm
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext t; simp
  · congr 1; ext t; simp

theorem crossTerm_univ (φ : Γ →* MulAut G) (a b : G → ℂ) (g : G) :
    crossTerm φ a b Finset.univ g = ∏ t : Γ, a (φ t g) := by
  unfold crossTerm
  rw [prod_inv_reindex (fun t => a (φ t g))]
  simp

theorem crossTerm_empty (φ : Γ →* MulAut G) (a b : G → ℂ) (g : G) :
    crossTerm φ a b ∅ g = ∏ t : Γ, b (φ t g) := by
  unfold crossTerm
  rw [prod_inv_reindex (fun t => b (φ t g))]
  simp

theorem eq_one_of_smul_eq (hp : (Nat.card Γ).Prime) {S : Finset Γ} {w : Γ} (hw : w • S = S)
    (h0 : S ≠ ∅) (h1 : S ≠ Finset.univ) : w = 1 := by
  by_contra hne
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have htop : Subgroup.zpowers w = ⊤ := zpowers_eq_top_of_prime_card rfl hne
  have hst : MulAction.stabilizer Γ S = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.zpowers_le]; exact hw
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 h0
  apply h1
  ext v
  simp only [Finset.mem_univ, iff_true]
  have hv : (v * t⁻¹) • S = S := by
    have : v * t⁻¹ ∈ MulAction.stabilizer Γ S := by rw [hst]; trivial
    exact this
  rw [← hv]
  have := Finset.smul_mem_smul_finset (a := v * t⁻¹) ht
  rwa [smul_eq_mul, inv_mul_cancel_right] at this

theorem smul_ne_empty_univ {S : Finset Γ} (u : Γ) :
    (u • S ≠ ∅ ∧ u • S ≠ Finset.univ) ↔ (S ≠ ∅ ∧ S ≠ Finset.univ) := by
  have h2 : u • S = Finset.univ ↔ S = Finset.univ := by
    constructor
    · intro h
      have := congrArg (fun T : Finset Γ => u⁻¹ • T) h
      simpa [inv_smul_smul, Finset.smul_finset_univ] using this
    · intro h; rw [h, Finset.smul_finset_univ]
  rw [Ne, Ne, Finset.smul_finset_eq_empty, h2]

end GlobalTheory.CrossOrbit

namespace GlobalTheory.CrossOrbit
variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ]

theorem sum_orbits (hp : (Nat.card Γ).Prime) (F : Finset Γ → ℂ) :
    ∑ S : Finset Γ, (if S ≠ ∅ ∧ S ≠ Finset.univ then F S else 0) =
      ∑ q : MulAction.orbitRel.Quotient Γ (Finset Γ),
        if q.out ≠ ∅ ∧ q.out ≠ Finset.univ then ∑ u : Γ, F (u • q.out) else 0 := by
  rw [← (MulAction.selfEquivSigmaOrbits Γ (Finset Γ)).symm.sum_comp, Fintype.sum_sigma]
  have key : ∀ q (y : MulAction.orbit Γ (Quotient.out q)), (MulAction.selfEquivSigmaOrbits Γ (Finset Γ)).symm ⟨q, y⟩ = (y : Finset Γ) := fun q y => rfl
  simp only [key]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hP
  · symm
    refine Fintype.sum_bijective (fun u : Γ => (⟨u • q.out, MulAction.mem_orbit _ _⟩ : MulAction.orbit Γ q.out)) ⟨?_, ?_⟩ _ _ ?_
    · intro u v huv
      have h : u • q.out = v • q.out := congrArg Subtype.val huv
      have : (v⁻¹ * u) • q.out = q.out := by rw [mul_smul, h, inv_smul_smul]
      have := eq_one_of_smul_eq hp this hP.1 hP.2
      rw [inv_mul_eq_one] at this; exact this.symm
    · rintro ⟨x, hx⟩
      obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 hx
      exact ⟨u, rfl⟩
    · intro u
      rw [if_pos ((smul_ne_empty_univ u).2 hP)]
  · refine Finset.sum_eq_zero fun y _ => ?_
    obtain ⟨y, hy⟩ := y
    obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    rw [if_neg]
    rwa [smul_ne_empty_univ u]

end GlobalTheory.CrossOrbit

namespace GlobalTheory.CrossOrbit
variable {G Γ : Type} [Group G] [Group Γ]

def sdEquiv (φ : Γ →* MulAut G) : G ⋊[φ] Γ ≃ G × Γ :=
  ⟨fun x => (x.left, x.right), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem mem_range_inl_iff (φ : Γ →* MulAut G) (y : G ⋊[φ] Γ) :
    y ∈ (inl : G →* G ⋊[φ] Γ).range ↔ y.right = 1 := by
  rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker, rightHom_eq_right]

theorem conj_inl_left (φ : Γ →* MulAut G) (x : G ⋊[φ] Γ) (g : G) :
    (x⁻¹ * inl g * x).left = (φ x.right⁻¹ x.left)⁻¹ * φ x.right⁻¹ g * φ x.right⁻¹ x.left := by
  simp [map_mul, map_inv, mul_assoc]

theorem conj_inl_right (φ : Γ →* MulAut G) (x : G ⋊[φ] Γ) (g : G) :
    (x⁻¹ * inl g * x).right = 1 := by
  simp

theorem conj_off_right (φ : Γ →* MulAut G) (x : G ⋊[φ] Γ) (δ : G) (s : Γ) :
    (x⁻¹ * (inl δ * inr s) * x).right = x.right⁻¹ * s * x.right := by
  simp

end GlobalTheory.CrossOrbit

namespace GlobalTheory.CrossOrbit
variable {G Γ : Type} [Group G] [Group Γ]

def inlEquiv (φ : Γ →* MulAut G) : G ≃* (inl : G →* G ⋊[φ] Γ).range :=
  MonoidHom.ofInjective inl_injective

theorem inlEquiv_symm_apply (φ : Γ →* MulAut G) (y : (inl : G →* G ⋊[φ] Γ).range) :
    (inlEquiv φ).symm y = (y : G ⋊[φ] Γ).left := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  have h := (mem_range_inl_iff φ y.1).1 y.2
  show y.1 = inl y.1.left
  exact SemidirectProduct.ext (by simp) (by simp [h])

theorem ind_off (φ : Γ →* MulAut G) (ψ : (inl : G →* G ⋊[φ] Γ).range → ℂ) (δ : G) {s : Γ} (hs : s ≠ 1) :
    ind (inl : G →* G ⋊[φ] Γ).range ψ (inl δ * inr s) = 0 := by
  unfold ind
  have : ∀ x : G ⋊[φ] Γ, ext0 (inl : G →* G ⋊[φ] Γ).range ψ (x⁻¹ * (inl δ * inr s) * x) = 0 := by
    intro x
    unfold ext0
    rw [dif_neg]
    rw [mem_range_inl_iff, conj_off_right]
    intro h
    apply hs
    have := congrArg (fun y => x.right * y * x.right⁻¹) h
    simpa [mul_assoc] using this
  simp [this]

theorem ind_inl (φ : Γ →* MulAut G) [Fintype G] [Fintype Γ] (c : G → ℂ)
    (hc : ∀ g x : G, c (x⁻¹ * g * x) = c g) (g : G) :
    ind (inl : G →* G ⋊[φ] Γ).range (fun n => c ((inlEquiv φ).symm n)) (inl g) =
      ∑ u : Γ, c (φ u⁻¹ g) := by
  letI : Fintype (G ⋊[φ] Γ) := Fintype.ofEquiv _ (sdEquiv φ).symm
  unfold ind
  have hterm : ∀ x : G ⋊[φ] Γ, ext0 (inl : G →* G ⋊[φ] Γ).range (fun n => c ((inlEquiv φ).symm n))
      (x⁻¹ * inl g * x) = c (φ x.right⁻¹ g) := by
    intro x
    unfold ext0
    rw [dif_pos ((mem_range_inl_iff φ _).2 (conj_inl_right φ x g))]
    dsimp only
    rw [inlEquiv_symm_apply]
    show c ((x⁻¹ * inl g * x).left) = _
    rw [conj_inl_left]
    exact hc _ _
  simp only [hterm]
  rw [finsum_eq_sum_of_fintype, ← (sdEquiv φ).symm.sum_comp, Fintype.sum_prod_type]
  have hr : ∀ (h : G) (u : Γ), ((sdEquiv φ).symm (h, u)).right = u := fun _ _ => rfl
  simp only [hr]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : Nat.card (inl : G →* G ⋊[φ] Γ).range = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card]; exact (Nat.card_congr (inlEquiv φ).toEquiv).symm
  rw [hN]
  have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

end GlobalTheory.CrossOrbit

namespace GlobalTheory.CrossOrbit

theorem virt_crossTerm {G Γ : Type} [Group G] [Group Γ] [Fintype Γ] [Finite G] (φ : Γ →* MulAut G)
    {a b : G → ℂ} (ha : a ∈ Virt ℂ ℂ G) (hb : b ∈ Virt ℂ ℂ G) (S : Finset Γ) :
    crossTerm φ a b S ∈ Virt ℂ ℂ G := by
  have hV := virt_mul_comap_conj_ind_linear G
  have heq : crossTerm φ a b S = ∏ t : Γ, (fun g => if t ∈ S then a (φ t⁻¹ g) else b (φ t⁻¹ g)) := by
    funext g; rw [Finset.prod_apply]; rfl
  rw [heq]
  refine Finset.prod_induction _ (· ∈ Virt ℂ ℂ G) (fun x y hx hy => hV.1 x hx y hy) ?_ ?_
  · exact isChar_mem_virt_complex (isChar_one ℂ ℂ G)
  · intro t _
    by_cases ht : t ∈ S
    · simp only [ht, if_true]; exact hV.2.1 a ha G (φ t⁻¹).toMonoidHom
    · simp only [ht, if_false]; exact hV.2.1 b hb G (φ t⁻¹).toMonoidHom

theorem cross_terms_induced : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ a b : G → ℂ, a ∈ Virt ℂ ℂ G → b ∈ Virt ℂ ℂ G → ∃ Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, Z (inl g) = ∏ t : Γ, (a (φ t g) + b (φ t g)) - ∏ t : Γ, a (φ t g) - ∏ t : Γ, b (φ t g)) ∧ ∀ δ, Z (inl δ * inr s) = 0 := by
  intro G Γ _ _ _ _ φ s hp hs a b ha hb
  letI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ (sdEquiv φ).symm
  have hVG := virt_mul_comap_conj_ind_linear G
  have hVS := virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
  refine ⟨∑ q : MulAction.orbitRel.Quotient Γ (Finset Γ),
    if q.out ≠ ∅ ∧ q.out ≠ Finset.univ then
      ind (inl : G →* G ⋊[φ] Γ).range (fun n => crossTerm φ a b q.out ((inlEquiv φ).symm n)) else 0,
    ?_, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ fun q _ => ?_
    split_ifs
    · exact hVS.2.2.2.1 _ _ (hVG.2.1 _ (virt_crossTerm φ ha hb _) _ (inlEquiv φ).symm.toMonoidHom)
    · exact zero_mem _
  · intro g
    rw [Finset.sum_apply]
    have hq : ∀ q : MulAction.orbitRel.Quotient Γ (Finset Γ),
        (if q.out ≠ ∅ ∧ q.out ≠ Finset.univ then
          ind (inl : G →* G ⋊[φ] Γ).range (fun n => crossTerm φ a b q.out ((inlEquiv φ).symm n)) else 0) (inl g) =
        if q.out ≠ ∅ ∧ q.out ≠ Finset.univ then ∑ u : Γ, crossTerm φ a b (u • q.out) g else 0 := by
      intro q
      split_ifs
      · rw [ind_inl φ _ (hVG.2.2.1 _ (virt_crossTerm φ ha hb _))]
        exact Finset.sum_congr rfl fun u _ => crossTerm_shift φ a b _ u g
      · rfl
    simp only [hq]
    rw [← sum_orbits hp (fun S => crossTerm φ a b S g), prod_add_eq_sum, ← crossTerm_univ φ a b g,
      ← crossTerm_empty φ a b g, eq_sub_iff_add_eq, eq_sub_iff_add_eq]
    have hne : (∅ : Finset Γ) ≠ Finset.univ := Finset.univ_nonempty.ne_empty.symm
    have hsplit : ∀ S : Finset Γ, crossTerm φ a b S g =
        (if S ≠ ∅ ∧ S ≠ Finset.univ then crossTerm φ a b S g else 0) +
          (if S = ∅ then crossTerm φ a b S g else 0) + (if S = Finset.univ then crossTerm φ a b S g else 0) := by
      intro S
      by_cases h1 : S = ∅
      · subst h1; simp [hne]
      · by_cases h2 : S = Finset.univ
        · subst h2; simp [hne.symm]
        · simp [h1, h2]
    conv_rhs => rw [Finset.sum_congr rfl fun S _ => hsplit S]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
  · intro δ
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs
    · exact ind_off φ _ δ hs
    · rfl

end GlobalTheory.CrossOrbit
