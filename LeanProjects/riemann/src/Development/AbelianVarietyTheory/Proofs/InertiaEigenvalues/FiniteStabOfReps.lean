import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.LocalToGlobal.IndefiniteReal.Bridge

noncomputable section

open Formalism.IndefR.Bridge

namespace GlobalTheory.ClassTrace

variable {O Γ Hf P : Type} [CommRing O] [Group Γ] [Group Hf] [AddCommGroup P] [Module O P]
  (ι : Γ →* Hf) (J : Subgroup Hf) (lam : J →* Oˣ) (ρ : Representation O Γ P)

def intForms (LL : Hf → Submodule O P) : Submodule O (Hf → P) where
  carrier := {f | (∀ (γ : Γ) (h : Hf) (k : J), f (ι γ * h * k) = (lam k : O) • ρ γ (f h)) ∧ ∀ h, f h ∈ LL h}
  add_mem' := fun {f g} hf hg =>
    ⟨fun γ h k => by simp only [Pi.add_apply, hf.1 γ h k, hg.1 γ h k, map_add, smul_add],
      fun h => Submodule.add_mem _ (hf.2 h) (hg.2 h)⟩
  zero_mem' := ⟨fun γ h k => by simp, fun h => Submodule.zero_mem _⟩
  smul_mem' := fun a f hf =>
    ⟨fun γ h k => by simp only [Pi.smul_apply, hf.1 γ h k, map_smul]; rw [smul_comm],
      fun h => Submodule.smul_mem _ _ (hf.2 h)⟩

def LatticeLaw (LL : Hf → Submodule O P) : Prop :=
  (∀ γ h, (LL h).map (ρ γ) = LL (ι γ * h)) ∧ ∀ h (k : J), LL (h * k) = LL h

def tr (h : Hf) (p : P) : P := ∑ᶠ γ : stab ι J h, (lam (stabK ι γ) : O) • ρ (γ : Γ) p

open Classical in

def lamExt (x : Hf) : O := if hx : x ∈ J then (lam ⟨x, hx⟩ : O) else 0

theorem lamExt_coe (k : J) : lamExt J lam (k : Hf) = (lam k : O) := by
  simp [lamExt]

theorem lamExt_of_not_mem {x : Hf} (hx : x ∉ J) : lamExt J lam x = 0 := by
  simp [lamExt, hx]

theorem lamExt_mul (x : Hf) (k : J) : lamExt J lam (x * k) = lamExt J lam x * (lam k : O) := by
  by_cases hx : x ∈ J
  · have hxk : x * (k : Hf) ∈ J := J.mul_mem hx k.2
    unfold lamExt
    rw [dif_pos hxk, dif_pos hx, ← Units.val_mul, ← map_mul]
    rfl
  · have hxk : x * (k : Hf) ∉ J := fun hm => hx (by simpa using J.mul_mem hm (J.inv_mem k.2))
    rw [lamExt_of_not_mem J lam hx, lamExt_of_not_mem J lam hxk, zero_mul]

def traceForm (h : Hf) (p : P) (x : Hf) : P := ∑ᶠ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p

def link (h x : Hf) : Set Γ := {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}

theorem mem_link_iff {h x : Hf} {γ : Γ} : γ ∈ link ι J h x ↔ ∃ k : J, x = ι γ * h * k := by
  constructor
  · intro hγ
    refine ⟨⟨h⁻¹ * (ι γ)⁻¹ * x, hγ⟩, ?_⟩
    show x = ι γ * h * (h⁻¹ * (ι γ)⁻¹ * x)
    group
  · rintro ⟨k, rfl⟩
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    rw [show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) = (k : Hf) by group]
    exact k.2

def linkEquiv {h x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) : stab ι J x ≃ link ι J h x where
  toFun δ := ⟨δ * γ₀, by
    have h1 := J.mul_mem h0 (J.inv_mem ((mem_stab ι).1 δ.2))
    simpa [link, mul_assoc] using h1⟩
  invFun γ := ⟨γ * γ₀⁻¹, by
    have h1 := J.mul_mem (J.inv_mem γ.2) h0
    rw [mem_stab]
    simpa [link, mul_assoc] using h1⟩
  left_inv δ := by simp
  right_inv γ := by simp

theorem link_finite (hfin : ∀ x, Finite (stab ι J x)) (h x : Hf) : (link ι J h x).Finite := by
  rcases (link ι J h x).eq_empty_or_nonempty with he | ⟨γ₀, h0⟩
  · rw [he]
    exact Set.finite_empty
  · have := hfin x
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (linkEquiv ι J h0))

theorem support_subset (h : Hf) (p : P) (x : Hf) :
    (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) ⊆ link ι J h x := by
  intro γ hγ
  rw [Function.mem_support] at hγ
  by_contra hn
  have hn' : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hn
  exact hγ (by rw [lamExt_of_not_mem J lam hn', zero_smul])

theorem traceForm_eq_zero (h : Hf) (p : P) {x : Hf} (hx : ¬ ∃ (γ : Γ) (k : J), x = ι γ * h * k) :
    traceForm ι J lam ρ h p x = 0 := by
  unfold traceForm
  have hz : ∀ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p = 0 := by
    intro γ
    have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := fun hm =>
      hx ⟨γ, (mem_link_iff ι J (h := h) (x := x) (γ := γ)).1 hm⟩
    rw [lamExt_of_not_mem J lam hn, zero_smul]
  simp only [hz, finsum_zero]

theorem traceForm_law (hfin : ∀ x, Finite (stab ι J x)) (h : Hf) (p : P) (γ₀ : Γ) (x : Hf) (k : J) :
    traceForm ι J lam ρ h p (ι γ₀ * x * k) = (lam k : O) • ρ γ₀ (traceForm ι J lam ρ h p x) := by
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    (link_finite ι J hfin h x).subset (support_subset ι J lam ρ h p x)
  unfold traceForm
  conv_rhs => rw [← LinearMap.smul_apply]
  rw [map_finsum _ hf, ← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft]
  have e : h⁻¹ * (ι (γ₀ * γ))⁻¹ * (ι γ₀ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
    rw [map_mul]
    group
  rw [e, lamExt_mul, map_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

variable {C W : Type} [Field C] [AddCommGroup W] [Module C W] {e : O →+* C}

def classSum (θ : Hf → P →ₛₗ[e] W) {I : Type} [Fintype I] (y : I → Hf) (f : Hf → P) : W :=
  ∑ i, (Nat.card (stab ι J (y i)) : C)⁻¹ • θ (y i) (f (y i))

def DualLaw (θ : Hf → P →ₛₗ[e] W) : Prop :=
  ∀ (γ : Γ) (h : Hf) (k : J) (p : P), e (lam k) • θ (ι γ * h * k) (ρ γ p) = θ h p

theorem kernel_traceForm (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W} (hθ : DualLaw ι J lam ρ θ)
    (h : Hf) (p : P) {x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) :
    θ x (traceForm ι J lam ρ h p x) = (Nat.card (stab ι J x) : C) • θ h p := by
  classical
  have hL := link_finite ι J hfin h x
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    hL.subset (support_subset ι J lam ρ h p x)
  have hterm : ∀ γ : Γ, θ x (lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) =
      if γ ∈ link ι J h x then θ h p else 0 := by
    intro γ
    split_ifs with hγ
    · obtain ⟨k, hk⟩ := (mem_link_iff ι J).1 hγ
      have hk' : h⁻¹ * (ι γ)⁻¹ * x = (k : Hf) := by
        rw [hk]
        group
      rw [hk', lamExt_coe, map_smulₛₗ, ← hθ γ h k p, ← hk]
    · have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hγ
      rw [lamExt_of_not_mem J lam hn, zero_smul, map_zero]
  have hsub : Function.support (fun γ : Γ => if γ ∈ link ι J h x then θ h p else 0) ⊆
      (hL.toFinset : Set Γ) := by
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    exact hγ (if_neg hn)
  have hc : hL.toFinset.card = Nat.card (stab ι J x) := by
    rw [Nat.card_congr (linkEquiv ι J h0), Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hL]
  unfold traceForm
  rw [map_finsum (θ x) hf]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ hsub,
    Finset.sum_congr rfl (fun γ hγ => if_pos ((Set.Finite.mem_toFinset hL).1 hγ)),
    Finset.sum_const, hc, Nat.cast_smul_eq_nsmul]

theorem classSum_traceForm [CharZero C] (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W}
    (hθ : DualLaw ι J lam ρ θ) {I : Type} [Fintype I] {y : I → Hf} (hy : IsReps ι J y) (h : Hf) (p : P) :
    classSum ι J θ y (traceForm ι J lam ρ h p) = θ h p := by
  obtain ⟨i₀, ⟨γ, k, hh⟩, huniq⟩ := hy h
  unfold classSum
  rw [Finset.sum_eq_single i₀]
  · have h0 : γ⁻¹ ∈ link ι J h (y i₀) := by
      rw [mem_link_iff]
      refine ⟨k⁻¹, ?_⟩
      rw [hh]
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [kernel_traceForm ι J lam ρ hfin hθ h p h0]
    have := hfin (y i₀)
    have hne : (Nat.card (stab ι J (y i₀)) : C) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact inv_smul_smul₀ hne _
  · intro i _ hi
    have hx : ¬ ∃ (γ' : Γ) (k' : J), y i = ι γ' * h * k' := by
      rintro ⟨γ', k', hy'⟩
      apply hi
      apply huniq
      refine ⟨γ'⁻¹, k'⁻¹, ?_⟩
      rw [hy']
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [traceForm_eq_zero ι J lam ρ h p hx, map_zero, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

theorem finite_stab_of_reps {I : Type} {y : I → Hf} (hy : IsReps ι J y) (hfin : ∀ i, Finite (stab ι J (y i)))
    (x : Hf) : Finite (stab ι J x) := by
  obtain ⟨i, ⟨γ, k, hx⟩, -⟩ := hy x
  subst hx
  have := hfin i
  refine Finite.of_injective (β := stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ * γ, ?_⟩) ?_
  · rw [mem_stab]
    have hδ := (mem_stab ι).1 δ.2
    have e : (y i)⁻¹ * ι (γ⁻¹ * δ * γ) * y i =
        (k : Hf) * ((ι γ * y i * k)⁻¹ * ι δ * (ι γ * y i * k)) * (k : Hf)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact J.mul_mem (J.mul_mem k.2 hδ) (J.inv_mem k.2)
  · intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this

end GlobalTheory.ClassTrace

end
