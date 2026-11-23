import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood

noncomputable section

open Formalism.IndefR

namespace GlobalTheory.LawTrace

variable {G Γ W : Type} [Group G] [Group Γ] [AddCommGroup W] [Module ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)

open Classical in

def term (y x : G) (P : W) (γ : Γ) : W :=
  if h : (ι γ * y)⁻¹ * x ∈ J then ((χ ⟨_, h⟩ : ℂˣ) : ℂ) • ρ γ P else 0

def tr (y : G) (P : W) : G → W := fun x => ∑ᶠ γ, term ι ρ J χ y x P γ

variable {ι ρ J χ}

theorem support_term_subset (y x : G) (P : W) :
    Function.support (term ι ρ J χ y x P) ⊆ {γ | (ι γ * y)⁻¹ * x ∈ J} := by
  intro γ hγ
  by_contra h
  exact hγ (by unfold term; exact dif_neg (show ¬ ((ι γ * y)⁻¹ * x ∈ J) from h))

theorem finite_cond {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) : {γ | (ι γ * y)⁻¹ * x ∈ J}.Finite := by
  rcases Set.eq_empty_or_nonempty {γ | (ι γ * y)⁻¹ * x ∈ J} with h | ⟨γ₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  · have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
    refine (hs.image fun s => γ₀ * s).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
    change γ₀⁻¹ * γ ∈ Bridge.stab ι J y
    rw [Bridge.mem_stab]
    have h1 := J.mul_mem h₀ (J.inv_mem (show (ι γ * y)⁻¹ * x ∈ J from hγ))
    convert h1 using 1
    simp [mul_assoc]

theorem support_term_finite {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) (P : W) :
    (Function.support (term ι ρ J χ y x P)).Finite :=
  (finite_cond hf x).subset (support_term_subset y x P)

theorem term_mul (y x : G) (P : W) (γ₀ γ : Γ) (k : J) :
    term ι ρ J χ y (ι γ₀ * x * k) P (γ₀ * γ) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (term ι ρ J χ y x P γ) := by
  have e : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) = (ι γ * y)⁻¹ * x * k := by
    simp [mul_assoc]
  unfold term
  by_cases h : (ι γ * y)⁻¹ * x ∈ J
  · have h' : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by rw [e]; exact J.mul_mem h k.2
    rw [dif_pos h', dif_pos h]
    have ek : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k := Subtype.ext e
    rw [ek, map_mul, map_mul, Units.val_mul, map_smul, smul_smul, mul_comm, Module.End.mul_apply]
  · have h' : ¬ (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by
      rw [e]; intro h2; exact h (by simpa using J.mul_mem h2 (J.inv_mem k.2))
    rw [dif_neg h', dif_neg h, map_zero, smul_zero]

theorem tr_law {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (γ₀ : Γ) (x : G) (k : J) :
    tr ι ρ J χ y P (ι γ₀ * x * k) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (tr ι ρ J χ y P x) := by
  unfold tr
  rw [← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  simp only [Equiv.coe_mulLeft, term_mul]
  let L : W →ₗ[ℂ] W := ((χ k : ℂˣ) : ℂ) • ρ γ₀
  change ∑ᶠ γ, L (term ι ρ J χ y x P γ) = L (∑ᶠ γ, term ι ρ J χ y x P γ)
  exact (map_finsum L (support_term_finite hf x P)).symm

theorem mem_lawForms_tr {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) :
    tr ι ρ J χ y P ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ :=
  GlobalTheory.ExportSeries.mem_lawForms.2 fun γ x k => tr_law hf P γ x k

theorem tr_add {y : G} (hf : Finite (Bridge.stab ι J y)) (P Q : W) :
    tr ι ρ J χ y (P + Q) = tr ι ρ J χ y P + tr ι ρ J χ y Q := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (P + Q) γ = term ι ρ J χ y x P γ + term ι ρ J χ y x Q γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_add]
  simp only [tr, Pi.add_apply, e]
  exact finsum_add_distrib (support_term_finite hf x P) (support_term_finite hf x Q)

theorem tr_smul (y : G) (a : ℂ) (P : W) : tr ι ρ J χ y (a • P) = a • tr ι ρ J χ y P := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (a • P) γ = a • term ι ρ J χ y x P γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_comm a]
  simp only [tr, Pi.smul_apply, e]
  exact (smul_finsum a _).symm

theorem tr_zero (y : G) : tr ι ρ J χ y (0 : W) = 0 := by
  simpa using tr_smul (ι := ι) (ρ := ρ) (χ := χ) y (0 : ℂ) (0 : W)

theorem tr_mem {R : Type} [Semiring R] [Module R W] {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (x : G)
    (M : Submodule R W) (hM : ∀ γ, (ι γ * y)⁻¹ * x ∈ J → term ι ρ J χ y x P γ ∈ M) : tr ι ρ J χ y P x ∈ M := by
  unfold tr
  rw [finsum_eq_sum _ (support_term_finite hf x P)]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h := support_term_subset y x P ((Set.Finite.mem_toFinset _).1 hγ)
  exact hM γ h

theorem tr_self {y : G} (hf : Finite (Bridge.stab ι J y)) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    tr ι ρ J χ y (F y) y = (Nat.card (Bridge.stab ι J y) : ℂ) • F y := by
  classical
  have e : ∀ γ, term ι ρ J χ y y (F y) γ = if γ ∈ Bridge.stab ι J y then F y else 0 := fun γ => by
    unfold term
    have hc : (ι γ * y)⁻¹ * y ∈ J ↔ γ ∈ Bridge.stab ι J y := by
      rw [Bridge.mem_stab, ← J.inv_mem_iff]
      simp [mul_assoc]
    by_cases h : (ι γ * y)⁻¹ * y ∈ J
    · rw [dif_pos h, if_pos (hc.1 h)]
      have := GlobalTheory.ExportSeries.mem_lawForms.1 hF γ y ⟨_, h⟩
      rw [show ι γ * y * ((ι γ * y)⁻¹ * y) = y by group] at this
      exact this.symm
    · rw [dif_neg h, if_neg fun h' => h (hc.2 h')]
  unfold tr
  simp only [e]
  have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
  have ei : (fun γ => if γ ∈ Bridge.stab ι J y then F y else 0) =
      Set.indicator ((Bridge.stab ι J y : Subgroup Γ) : Set Γ) (fun _ => F y) := by
    funext γ; simp [Set.indicator]
  rw [ei, ← finsum_mem_def]
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  rw [← Nat.card_eq_card_finite_toFinset hs]
  rfl

theorem eq_sum_tr {I : Type} [Fintype I] {y : I → G} (hr : Bridge.IsReps ι J y)
    (hf : ∀ i, Finite (Bridge.stab ι J (y i))) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    F = ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ • tr ι ρ J χ (y i) (F (y i)) := by
  funext x
  obtain ⟨i₀, ⟨γ₀, k₀, hx⟩, huniq⟩ := hr x
  rw [Finset.sum_apply, Finset.sum_eq_single i₀]
  · have hne : ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)) ≠ 0 := by
      haveI := hf i₀
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Pi.smul_apply, hx, tr_law (hf i₀), tr_self (hf i₀) hF, GlobalTheory.ExportSeries.mem_lawForms.1 hF γ₀ (y i₀) k₀, map_smul,
      smul_comm ((χ k₀ : ℂˣ) : ℂ) ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)), smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro i _ hi
    rw [Pi.smul_apply]
    have : tr ι ρ J χ (y i) (F (y i)) x = 0 := by
      unfold tr
      refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
      unfold term
      rw [dif_neg]
      intro h
      exact hi (huniq i ⟨γ, ⟨_, h⟩, by simp [mul_assoc]⟩)
    rw [this, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LawTrace

end
