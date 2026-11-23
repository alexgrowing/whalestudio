import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section Member

theorem finrank_int_eq_finrank_mul (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

theorem free_int_of_projective (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] : Module.Free ℤ Y := by
  have : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
  have : Module.IsTorsionFree ℤ Y := Module.IsTorsionFree.trans (𝓞 E)
  exact Module.free_of_finite_type_torsion_free'

theorem mem_psdCone_int {E : Type} [Field E] [NumberField E] (bar : 𝓞 E → 𝓞 E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone bar X) : B ∈ psdCone (id : ℤ → ℤ) X := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, h1, h2, h3⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := free_int_of_projective E
  exact ⟨X₁, _, _, inferInstance, r.restrictScalars ℤ, B₁, hr, ⟨h1.1, fun a y z => by simp⟩, h2, h3⟩

section ClassMin

open scoped Pointwise

variable {M n : ℕ} {C C' : (Fin n → ℤ) → (Fin n → ℤ) → ℝ}

theorem classMin_set_nonempty (M : ℕ) (C : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) (y : Fin n → ZMod (M + 1)) :
    {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x}.Nonempty := by
  obtain ⟨a, ha⟩ := redV_surjective M n y
  exact ⟨_, a, ha, rfl⟩

theorem classMin_set_bddBelow (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) :
    BddBelow {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} :=
  ⟨0, by rintro _ ⟨a, -, rfl⟩; exact hC a⟩

theorem classMin_nonneg (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) : 0 ≤ classMin M C y :=
  le_csInf (classMin_set_nonempty M C y) (by rintro _ ⟨a, -, rfl⟩; exact hC a)

theorem classMin_smul {t : ℝ} (ht : 0 ≤ t) (y : Fin n → ZMod (M + 1)) :
    classMin M (fun a b => t * C a b) y = t * classMin M C y := by
  unfold classMin
  have : {x | ∃ a : Fin n → ℤ, redV M a = y ∧ t * C a a = x} = t • {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
  rw [this, Real.sInf_smul_of_nonneg ht, smul_eq_mul]

theorem classMin_add_le (hC : ∀ a, 0 ≤ C a a) (hC' : ∀ a, 0 ≤ C' a a) (y : Fin n → ZMod (M + 1)) :
    classMin M C y + classMin M C' y ≤ classMin M (fun a b => C a b + C' a b) y := by
  refine le_csInf (classMin_set_nonempty M (fun a b => C a b + C' a b) y) ?_
  rintro _ ⟨a, ha, rfl⟩
  exact add_le_add (csInf_le (classMin_set_bddBelow hC y) ⟨a, ha, rfl⟩)
    (csInf_le (classMin_set_bddBelow hC' y) ⟨a, ha, rfl⟩)

theorem classMin_exists_nat {β : (Fin n → ℤ) → (Fin n → ℤ) → ℤ} (hβ : ∀ a, 0 ≤ β a a) (y : Fin n → ZMod (M + 1)) :
    ∃ k : ℕ, classMin M (fun a b => (β a b : ℝ)) y = k := by
  classical
  let T : Set ℕ := {k | ∃ a : Fin n → ℤ, redV M a = y ∧ β a a = k}
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := redV_surjective M n y
    exact ⟨(β a a).toNat, a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  obtain ⟨a₀, ha₀, e₀⟩ := Nat.sInf_mem hT
  refine ⟨sInf T, IsLeast.csInf_eq ⟨⟨a₀, ha₀, by simp only [e₀]; push_cast; rfl⟩, ?_⟩⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : sInf T ≤ (β a a).toNat := Nat.sInf_le ⟨a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  have h2 : ((β a a).toNat : ℤ) = β a a := Int.toNat_of_nonneg (hβ a)
  show ((sInf T : ℕ) : ℝ) ≤ (β a a : ℝ)
  rw [← h2]
  exact_mod_cast h1

end ClassMin

variable {X : Type} [AddCommGroup X] [Module.Finite ℤ X]

theorem fineMean_eval_eq (M : ℕ) {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (fineMean M).eval X (fun a b => B a b) =
      (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y := by
  rw [(fineMean M).eval_eq hs]
  show _ * _ - B (s 0) (s 0) = _
  simp

end Member

theorem baseFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ)
    (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q →
    (∀ B ∈ psdCone H.bar X, ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) =
      t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧
    (∀ B ∈ psdCone H.bar X, ∀ B' ∈ psdCone H.bar X, evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B +
      evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  intro E _ _ _ H g q φs 𝓜 X _ _ _ _ hφ hE hX
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have hd : Module.finrank ℤ X ≤ g := by
    rw [finrank_int_eq_finrank_mul E X]
    exact (Nat.mul_le_mul_left _ hX).trans hE
  have hφX : IsPolFanOn id φs X := hφ X hd
  set d := Module.finrank ℤ X with hd_def
  let b := Module.finBasis ℤ X
  let s : (Fin d → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hs : Function.Surjective s := b.equivFun.symm.surjective
  set D := fineDen g 𝓜 with hD
  have key : ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, evalR (baseFun (𝓞 E) D φs 𝓜) B = D * (evalR φs B +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y) := by
    intro B
    rw [evalR, eval_baseFun]
    simp only [fineMean_eval_eq _ hs]
    rfl
  have keyZ : ∀ β : LinearMap.BilinForm ℤ X, (baseFun (𝓞 E) D φs 𝓜).evalZ β = D * (φs.evalZ β +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (β (s a) (s b) : ℝ)) y) := by
    intro β
    rw [← evalR_toReal, key, evalR_toReal]
    simp only [toReal_apply]
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_⟩
  · have hB0 := nonneg_of_mem_psdCone hB
    rw [key, key, hφX.homog B (mem_psdCone_int _ hB) t ht]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    simp only [mul_left_comm _ t, ← Finset.mul_sum]
    ring
  · have h1 := hφX.superadd B (mem_psdCone_int _ hB) B' (mem_psdCone_int _ hB')
    have h2 : ∀ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y +
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B' (s a) (s b)) y ≤
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (B + B') (s a) (s b)) y := fun M _ => by
      rw [← mul_add, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by positivity)
      simp only [LinearMap.add_apply]
      exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_add_distrib] at h3
    rw [key, key, key, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  · obtain ⟨n, hn⟩ := hφX.integral β (mem_balForms_int.2 hβ.1) hp
    have hdiv : ∀ M ∈ 𝓜, ∃ e : ℕ, D = (M + 1) ^ d * e := fun M hM =>
      (pow_dvd_pow (M + 1) hd).trans (Finset.dvd_prod_of_mem (fun M => (M + 1) ^ g) hM)
    choose! e he using hdiv
    choose k hk using fun M y => classMin_exists_nat (M := M) (β := fun a b => β (s a) (s b)) (fun a => hp (s a)) y
    refine ⟨D * n + ∑ M ∈ 𝓜, (e M : ℤ) * ∑ y, (k M y : ℤ), ?_⟩
    rw [keyZ, hn]
    simp only [hk]
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun M hM => ?_
    have hM : (D : ℝ) = ((M : ℝ) + 1) ^ d * e M := by exact_mod_cast he M hM
    rw [hM]
    field_simp
  · have h1 := hφX.pos β (mem_balForms_int.2 hβ.1) hp h0
    rw [keyZ]
    refine mul_pos (by exact_mod_cast fineDen_pos g 𝓜) (add_pos_of_pos_of_nonneg h1 (Finset.sum_nonneg fun M _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => classMin_nonneg (fun a => ?_) y)))
    exact_mod_cast hp (s a)

end GlobalTheory.PolFan
