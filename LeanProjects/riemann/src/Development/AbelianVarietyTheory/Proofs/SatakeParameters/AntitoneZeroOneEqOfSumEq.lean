import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open IsDedekindDomain NumberField

namespace GlobalTheory

theorem antitone_zero_one_eq_of_sum_eq {n : ℕ} (d e : Fin n → ℤ) (hd : Antitone d) (he : Antitone e)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (hs : ∑ i, d i = ∑ i, e i) : d = e := by
  have key : (∀ i, d i ≤ e i) ∨ (∀ i, e i ≤ d i) := by
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    have := hd0 j; have := hd1 i; have := he0 i; have := he1 j
    rcases le_total i j with hij | hij
    · have := he hij; omega
    · have := hd hij; omega
  rcases key with h | h
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs i (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs.symm i (Finset.mem_univ i)).symm

section

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem glint_entry_mem_Ov {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) (i j : Fin n) :
    (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v := by
  obtain ⟨g, rfl⟩ := hk
  have : ((Formalism.UG.bc (n := Fin n) (Formalism.UG.Ov F v).subtype g : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j
      = (((g : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)) i j : Formalism.UG.Ov F v) : v.adicCompletion F) := by
    simp [Formalism.UG.bc, Units.coe_map]
  rw [this]
  exact Subtype.property _

theorem mul_mul_entry_mem_Ov {A B C : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) (hB : ∀ i j, B i j ∈ Formalism.UG.Ov F v)
    (hC : ∀ i j, C i j ∈ Formalism.UG.Ov F v) (i j : Fin n) : (A * B * C) i j ∈ Formalism.UG.Ov F v := by
  simp only [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _
    (Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hA _ _) (hB _ _)) (hC _ _)

theorem valued_det_le_one_of_entries {A : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) : Valued.v A.det ≤ 1 := by
  have : A.det ∈ Formalism.UG.Ov F v := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hA _ _)
  exact this

theorem valued_det_eq_one_of_glint {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  have h1 := valued_det_le_one_of_entries (glint_entry_mem_Ov hk)
  have h2 := valued_det_le_one_of_entries (glint_entry_mem_Ov (Subgroup.inv_mem _ hk))
  have h3 : Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det *
      Valued.v ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem cartan_minuscule (k : ℕ) (ϖ ϖ' : v.adicCompletion F)
    (hϖ : Formalism.UG.IsUnifV F v ϖ) (hϖ' : Formalism.UG.IsUnifV F v ϖ') (a : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h2 : ∀ i j, ϖ' * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h3 : Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k) :
    ∃ d : Fin n → ℤ, Antitone d ∧ (∀ i, 0 ≤ d i) ∧ (∀ i, d i ≤ 1) ∧ ∑ i, d i = k ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hv' : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    show Valued.v ϖ ≤ 1
    rw [hv]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hpow : ∀ m : ℤ, Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
    intro m
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]
    simp
  have hsum : ∀ d : Fin n → ℤ, ∏ i, ϖ ^ d i = ϖ ^ ∑ i, d i := by
    intro d
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ hϖ0]
  obtain ⟨d, hd, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ a
  have hD : ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
    simp only [Units.val_mul, e, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
  have hDinv : ((k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ (-d) := by
    have e1 : (k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) = (k₁⁻¹ * a * k₂⁻¹)⁻¹ := by group
    rw [e1, Matrix.coe_units_inv, hD]
    apply Matrix.inv_eq_left_inv
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0]
    simp
  refine ⟨d, hd, fun i => ?_, fun i => ?_, ?_, k₁, hk₁, k₂, hk₂, hD⟩
  · have := mul_mul_entry_mem_Ov (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₁)) h1
      (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₂)) i i
    rw [← Units.val_mul, ← Units.val_mul, hD] at this
    have h : Valued.v (Formalism.UG.diagPow F v ϖ d i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, hpow, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h
    omega
  · have := mul_mul_entry_mem_Ov (B := ϖ' • ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F))) (glint_entry_mem_Ov hk₂) h2
      (glint_entry_mem_Ov hk₁) i i
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul, ← Units.val_mul, hDinv] at this
    have h : Valued.v (ϖ' * Formalism.UG.diagPow F v ϖ (-d) i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, map_mul, hpow, hv', ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    simp only [Pi.neg_apply] at h
    omega
  · rw [e, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, valued_det_eq_one_of_glint hk₁,
      valued_det_eq_one_of_glint hk₂, one_mul, mul_one, Formalism.UG.diagPow, Matrix.det_diagonal,
      hsum, hpow, hv', ← WithZero.exp_nsmul, WithZero.exp_inj] at h3
    simp only [nsmul_eq_mul] at h3
    omega

end

theorem glint_doubleCoset_of_minuscule : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ) (ϖ ϖ' : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → Formalism.UG.IsUnifV F v ϖ' → ∀ a a' : GL (Fin n) (v.adicCompletion F), (∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ ^ k → (∀ i j, (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ' * ((a'⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k → ∃ x ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ y ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), a' = x * a * y := by
  intro F _ _ v n k ϖ ϖ' hϖ hϖ' a a' h1 h2 h3 h1' h2' h3'
  obtain ⟨d, hd, hd0, hd1, hs, k₁, hk₁, k₂, hk₂, hD⟩ := cartan_minuscule k ϖ ϖ hϖ hϖ a h1 h2 h3
  obtain ⟨e, he, he0, he1, ht, l₁, hl₁, l₂, hl₂, hE⟩ :=
    cartan_minuscule k ϖ ϖ' hϖ hϖ' a' h1' h2' h3'
  obtain rfl : d = e := antitone_zero_one_eq_of_sum_eq d e hd he hd0 hd1 he0 he1 (hs.trans ht.symm)
  have h : k₁⁻¹ * a * k₂⁻¹ = l₁⁻¹ * a' * l₂⁻¹ := Units.ext (hD.trans hE.symm)
  refine ⟨l₁ * k₁⁻¹, Subgroup.mul_mem _ hl₁ (Subgroup.inv_mem _ hk₁), k₂⁻¹ * l₂,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₂) hl₂, ?_⟩
  calc a' = l₁ * (l₁⁻¹ * a' * l₂⁻¹) * l₂ := by group
    _ = l₁ * (k₁⁻¹ * a * k₂⁻¹) * l₂ := by rw [h]
    _ = _ := by group

end GlobalTheory
