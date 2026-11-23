import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.MackeyFn

variable {Γ : Type} [Group Γ] [Fintype Γ]

open Classical in

def mS (A B : Subgroup Γ) (a b : Γ → ℂ) (x : Γ) : ℂ :=
  ∑ h, if h ∈ (A ⊓ cj x B : Subgroup Γ) then a h⁻¹ * b (x * h * x⁻¹) else 0

def dc (A B : Subgroup Γ) (g : Γ) : Set Γ := {x | ∃ β ∈ B, ∃ α ∈ A, x = β * g * α}

theorem conj_mem_iff (H : Subgroup Γ) {u h : Γ} (hu : u ∈ H) : u * h * u⁻¹ ∈ H ↔ h ∈ H := by
  constructor
  · intro hh
    have : u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hu) hh) (H.inv_mem (H.inv_mem hu))
    simpa [mul_assoc] using this
  · intro hh
    exact H.mul_mem (H.mul_mem hu hh) (H.inv_mem hu)

theorem ip_inter (A B : Subgroup Γ) (a b : Γ → ℂ) (y : Γ) :
    ip ((A ⊓ cj y B : Subgroup Γ) : Set Γ) a (fun h => b (y * h * y⁻¹)) =
      (Nat.card (A ⊓ cj y B : Subgroup Γ) : ℂ)⁻¹ * mS A B a b y := by
  classical
  have hc : (((A ⊓ cj y B : Subgroup Γ) : Set Γ)).ncard = Nat.card (A ⊓ cj y B : Subgroup Γ) :=
    (Nat.card_coe_set_eq _).symm
  unfold ip mS
  rw [hc]
  rfl

theorem ip_ind (A B : Subgroup Γ) (a b : Γ → ℂ) :
    ip (A : Set Γ) a (indF B b) =
      ((Nat.card A : ℂ)⁻¹ * (Nat.card B : ℂ)⁻¹) * ∑ x, mS A B a b x := by
  classical
  have hc : ((A : Set Γ)).ncard = Nat.card A := (Nat.card_coe_set_eq _).symm
  unfold ip indF mS
  rw [hc, Finset.sum_comm, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hh : h ∈ A
  · have hh' : h ∈ (A : Set Γ) := hh
    rw [if_pos hh', mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x * h * x⁻¹ ∈ B
    · have hm : h ∈ (A ⊓ cj x B : Subgroup Γ) := ⟨hh, hx⟩
      rw [if_pos hx, if_pos hm]
    · have hm : h ∉ (A ⊓ cj x B : Subgroup Γ) := fun q => hx q.2
      rw [if_neg hx, if_neg hm, mul_zero]
  · have hh' : h ∉ (A : Set Γ) := hh
    rw [if_neg hh']
    have : ∀ x, h ∉ (A ⊓ cj x B : Subgroup Γ) := fun x q => hh q.1
    simp [this]

theorem mS_inv {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    {β α : Γ} (x : Γ) (hβ : β ∈ B) (hα : α ∈ A) :
    mS A B a b (β * x * α) = mS A B a b x := by
  classical
  unfold mS
  refine Fintype.sum_equiv (MulAut.conj α).toEquiv _ _ fun h => ?_
  have he : (MulAut.conj α).toEquiv h = α * h * α⁻¹ := rfl
  rw [he]
  have hk : (β * x * α) * h * (β * x * α)⁻¹ = β * (x * (α * h * α⁻¹) * x⁻¹) * β⁻¹ := by group
  have hmem : h ∈ (A ⊓ cj (β * x * α) B : Subgroup Γ) ↔
      α * h * α⁻¹ ∈ (A ⊓ cj x B : Subgroup Γ) := by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_cj, mem_cj, hk, conj_mem_iff B hβ,
      conj_mem_iff A hα]
  by_cases hm : α * h * α⁻¹ ∈ (A ⊓ cj x B : Subgroup Γ)
  · have hx2 : x * (α * h * α⁻¹) * x⁻¹ ∈ B := hm.2
    rw [if_pos hm, if_pos (hmem.2 hm), hk, hB β hβ _ hx2]
    have hinv : (α * h * α⁻¹)⁻¹ = α * h⁻¹ * α⁻¹ := by group
    have hhA : h ∈ A := (conj_mem_iff A hα).1 hm.1
    rw [hinv, hA α hα _ (A.inv_mem hhA)]
  · rw [if_neg hm, if_neg (fun q => hm (hmem.1 q))]

theorem card_dc (A B : Subgroup Γ) (g : Γ) :
    Nat.card (dc A B g) * Nat.card (A ⊓ cj g B : Subgroup Γ) = Nat.card A * Nat.card B := by
  classical
  let φ : B × A → dc A B g := fun p => ⟨p.1 * g * p.2, p.1, p.1.2, p.2, p.2.2, rfl⟩
  have fib : ∀ x : dc A B g, Nat.card {p // φ p = x} = Nat.card (A ⊓ cj g B : Subgroup Γ) := by
    rintro ⟨x, β₀, hβ₀, α₀, hα₀, rfl⟩
    symm
    have hB' : ∀ c : (A ⊓ cj g B : Subgroup Γ), β₀ * (g * (c : Γ)⁻¹ * g⁻¹) ∈ B := fun c => by
      have h2 : g * (c : Γ) * g⁻¹ ∈ B := c.2.2
      have : g * (c : Γ)⁻¹ * g⁻¹ = (g * (c : Γ) * g⁻¹)⁻¹ := by group
      rw [this]
      exact B.mul_mem hβ₀ (B.inv_mem h2)
    have hA' : ∀ c : (A ⊓ cj g B : Subgroup Γ), (c : Γ) * α₀ ∈ A := fun c => A.mul_mem c.2.1 hα₀
    let f : (A ⊓ cj g B : Subgroup Γ) → {p // φ p = ⟨β₀ * g * α₀, β₀, hβ₀, α₀, hα₀, rfl⟩} := fun c =>
      ⟨(⟨_, hB' c⟩, ⟨_, hA' c⟩), by
        apply Subtype.ext
        show β₀ * (g * (c : Γ)⁻¹ * g⁻¹) * g * ((c : Γ) * α₀) = β₀ * g * α₀
        group⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
    · intro c c' hcc
      have h3 : (c : Γ) * α₀ = (c' : Γ) * α₀ := by
        have := congrArg (fun p => ((p.1.2 : A) : Γ)) hcc
        exact this
      exact Subtype.ext (mul_right_cancel h3)
    · rintro ⟨⟨⟨β, hβ⟩, ⟨α, hα⟩⟩, hp⟩
      have he : β * g * α = β₀ * g * α₀ := congrArg Subtype.val hp
      have hcA : α * α₀⁻¹ ∈ A := A.mul_mem hα (A.inv_mem hα₀)
      have hβe : β = β₀ * (g * (α * α₀⁻¹)⁻¹ * g⁻¹) := by
        have : β = (β * g * α) * α⁻¹ * g⁻¹ := by group
        rw [this, he]
        group
      have hcB : g * (α * α₀⁻¹) * g⁻¹ ∈ B := by
        have : g * (α * α₀⁻¹) * g⁻¹ = (β₀⁻¹ * β)⁻¹ := by
          rw [hβe]
          group
        rw [this]
        exact B.inv_mem (B.mul_mem (B.inv_mem hβ₀) hβ)
      refine ⟨⟨α * α₀⁻¹, hcA, hcB⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext hβe.symm
      · apply Subtype.ext
        show α * α₀⁻¹ * α₀ = α
        group
  have e : (B × A) ≃ Σ x : dc A B g, {p // φ p = x} := (Equiv.sigmaFiberEquiv φ).symm
  have h4 : Nat.card (B × A) = Nat.card (dc A B g) * Nat.card (A ⊓ cj g B : Subgroup Γ) := by
    rw [Nat.card_congr e, Nat.card_sigma]
    simp only [fib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  rw [← h4, Nat.card_prod, mul_comm]

theorem sum_dc {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    (g : Γ) [DecidablePred (· ∈ dc A B g)] :
    (∑ x, if x ∈ dc A B g then mS A B a b x else 0) = (Nat.card (dc A B g) : ℂ) * mS A B a b g := by
  classical
  have h1 : ∀ x, (if x ∈ dc A B g then mS A B a b x else 0) =
      if x ∈ dc A B g then mS A B a b g else 0 := by
    intro x
    by_cases hx : x ∈ dc A B g
    · obtain ⟨β, hβ, α, hα, rfl⟩ := hx
      rw [if_pos ⟨β, hβ, α, hα, rfl⟩, if_pos ⟨β, hβ, α, hα, rfl⟩, mS_inv hA hB g hβ hα]
    · rw [if_neg hx, if_neg hx]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem mackeyIp : ReciprocityTheory.Ty.Fin.St.MackeyIp := by
  classical
  intro Γ _ _ A B a b hA hB R _ g h1 h2
  have cardC : ∀ y, (Nat.card (A ⊓ cj y B : Subgroup Γ) : ℂ) ≠ 0 := fun y =>
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have cardA : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have cardB : (Nat.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hvan : ∀ x, (∀ r, x ∉ dc A B (g r)) → mS A B a b x = 0 := by
    intro x hx
    rcases h2 x with ⟨r, β, hβ, α, hα, e⟩ | ⟨y, ⟨β, hβ, α, hα, rfl⟩, hy⟩
    · exact absurd ⟨β, hβ, α, hα, e⟩ (hx r)
    · rw [mS_inv hA hB y hβ hα]
      rw [ip_inter] at hy
      exact (mul_eq_zero.1 hy).resolve_left (inv_ne_zero (cardC y))
  have hdisj : ∀ x r r', x ∈ dc A B (g r) → x ∈ dc A B (g r') → r = r' := by
    rintro x r r' ⟨β, hβ, α, hα, rfl⟩ ⟨β', hβ', α', hα', e⟩
    refine h1 r r' ⟨β'⁻¹ * β, B.mul_mem (B.inv_mem hβ') hβ, α * α'⁻¹, A.mul_mem hα (A.inv_mem hα'), ?_⟩
    have : g r' = β'⁻¹ * (β' * g r' * α') * α'⁻¹ := by group
    rw [this, ← e]
    group
  have hsum : ∀ x, mS A B a b x = ∑ r, if x ∈ dc A B (g r) then mS A B a b x else 0 := by
    intro x
    by_cases hx : ∃ r, x ∈ dc A B (g r)
    · obtain ⟨r, hr⟩ := hx
      rw [Fintype.sum_eq_single r, if_pos hr]
      intro r' hne
      exact if_neg fun q => hne (hdisj x r r' hr q).symm
    · push_neg at hx
      rw [hvan x hx]
      simp
  rw [ip_ind, Finset.sum_congr rfl fun x _ => hsum x, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_dc hA hB, ip_inter]
  have hc : (Nat.card (dc A B (g r)) : ℂ) * (Nat.card (A ⊓ cj (g r) B : Subgroup Γ) : ℂ) =
      (Nat.card A : ℂ) * (Nat.card B : ℂ) := by
    exact_mod_cast card_dc A B (g r)
  have := cardC (g r)
  field_simp
  linear_combination (mS A B a b (g r)) * hc

end GlobalTheory.CompanionTheory.MackeyFn
