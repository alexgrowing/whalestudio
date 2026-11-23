import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd Formalism.UG.P

namespace GlobalTheory.SatInd

section CosetTransport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_le_of_nonunit {x : K} (h1 : Valued.v x ≤ 1) (h2 : ¬ Valued.v x⁻¹ ≤ 1) (h0 : x ≠ 0) :
    Valued.v x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.1 hx0
  rw [map_inv₀, ← hk] at h2
  rw [← hk] at h1 ⊢
  have h2' : ¬ (k⁻¹ : Multiplicative ℤ) ≤ 1 := by
    intro h; apply h2; rw [← WithZero.coe_inv]; exact_mod_cast h
  rw [WithZero.coe_le_coe]
  have : (k⁻¹ : Multiplicative ℤ) = Multiplicative.ofAdd (- Multiplicative.toAdd k) := rfl
  rw [this, ← ofAdd_zero, Multiplicative.ofAdd_le] at h2'
  rw [← ofAdd_toAdd k, Multiplicative.ofAdd_le]
  omega

theorem cosetT_v_image (g : K ≃+* K) (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ : K}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (g ϖ) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact absurd hv WithZero.zero_ne_coe
  have hmem : ∀ x : K, x ∈ intL K ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  apply cosetT_le_of_nonunit
  · rw [← hmem, ← hint, hmem, hv]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)
  · rw [← map_inv₀, ← hmem, ← hint, hmem, map_inv₀, hv]
    rw [← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe]
    decide
  · exact (map_ne_zero g).2 hϖ0

theorem cosetT_unit (g : K ≃+* K) (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ ϖ' : K}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hv' : Valued.v ϖ' = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (g ϖ * ϖ'⁻¹) = 1 := by
  have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := by
    intro x; rw [hint (g.symm x), RingEquiv.apply_symm_apply]
  have hmem : ∀ x : K, x ∈ intL K ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact absurd hv WithZero.zero_ne_coe
  have hinv : Valued.v ϖ⁻¹ = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv, ← WithZero.coe_inv]; rfl
  have hinv' : Valued.v ϖ'⁻¹ = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv', ← WithZero.coe_inv]; rfl
  have hone : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = 1 := by
    rw [← WithZero.coe_mul, ← ofAdd_add]; rfl
  have h1 : Valued.v (g ϖ * ϖ'⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, hinv', ← hone]
    exact mul_le_mul' (cosetT_v_image g hint hv) le_rfl
  have h2 : Valued.v (g.symm ϖ' * ϖ⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, hinv, ← hone]
    exact mul_le_mul' (cosetT_v_image g.symm hint' hv') le_rfl
  have h3 : Valued.v (g ϖ * ϖ'⁻¹)⁻¹ ≤ 1 := by
    have e : (g ϖ * ϖ'⁻¹)⁻¹ = g (g.symm ϖ' * ϖ⁻¹) := by
      rw [map_mul, RingEquiv.apply_symm_apply, map_inv₀, mul_inv, inv_inv, mul_comm]
    rw [e, ← hmem, ← hint, hmem]; exact h2
  rw [map_inv₀] at h3
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv'; exact absurd hv' WithZero.zero_ne_coe
  have hne : Valued.v (g ϖ * ϖ'⁻¹) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (mul_ne_zero ((map_ne_zero g).2 hϖ0) (inv_ne_zero hϖ'0))
  exact le_antisymm h1 (by
    have := mul_le_mul' (le_refl (Valued.v (g ϖ * ϖ'⁻¹))) h3
    rwa [mul_inv_cancel₀ hne, mul_one] at this)

end CosetTransport
end GlobalTheory.SatInd

namespace GlobalTheory.SatInd

section CosetTransport2

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

local notation "⟪" b "⟫" => (((b : GU _ _) : GL (Fin _) K) : Matrix (Fin _) (Fin _) K)

theorem cosetT_tMat_map (g : K →+* K) (x : K) (n m : ℕ) (a : Fin m → ℤ) :
    (tMat x n m a).map g = tMat (g x) n m a := by
  unfold tMat
  rw [Matrix.diagonal_map (map_zero g)]
  congr 1
  funext i
  split_ifs <;> simp [map_zpow₀]

theorem cosetT_tMat_mul (x y : K) (n m : ℕ) (a : Fin m → ℤ) :
    tMat (x * y) n m a = tMat x n m a * tMat y n m a := by
  unfold tMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> first | exact mul_zpow _ _ _ | exact (mul_one 1).symm

theorem cosetT_tMat_unit {σ : K →+* K} {u : K} (hσ : σ u = u) (hv : Valued.v u = 1) {n m : ℕ}
    (hm : 2 * m ≤ n) (a : Fin m → ℤ) :
    ∃ t : GU σ n, (((t : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat u n m a ∧
      t ∈ KU σ n := by
  have h0 : u ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact zero_ne_one hv
  let f : Fin n → K := fun i : Fin n =>
    if h : i.val < m then u ^ (a ⟨i.val, h⟩)
    else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then u ^ (-(a ⟨n - 1 - i.val, h'.2⟩)) else 1
  have hf : ∀ i, σ (f i) * f i.rev = 1 := by
    intro i
    simp only [f]
    have hs : ∀ k : ℤ, σ (u ^ k) = u ^ k := fun k => by rw [map_zpow₀, hσ]
    have hi := i.isLt
    have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < m
    · have h2 : ¬ (i.rev : ℕ) < m := by omega
      have h3 : n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m := by omega
      simp only [dif_pos h1, dif_neg h2, dif_pos h3, hs]
      have : (⟨n - 1 - (i.rev : ℕ), h3.2⟩ : Fin m) = ⟨i, h1⟩ := Fin.ext (by simp only; omega)
      rw [this, ← zpow_add₀ h0, add_neg_cancel, zpow_zero]
    · by_cases h1' : n - m ≤ (i : ℕ) ∧ n - 1 - (i : ℕ) < m
      · have h2 : (i.rev : ℕ) < m := by omega
        simp only [dif_neg h1, dif_pos h1', dif_pos h2, hs]
        have : (⟨(i.rev : ℕ), h2⟩ : Fin m) = ⟨n - 1 - i, h1'.2⟩ := Fin.ext (by simp only; omega)
        rw [this, ← zpow_add₀ h0, neg_add_cancel, zpow_zero]
      · have h2 : ¬ (i.rev : ℕ) < m := by omega
        have h3 : ¬ (n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m) := by omega
        simp only [dif_neg h1, dif_neg h1', dif_neg h2, dif_neg h3, map_one, one_mul]
  obtain ⟨t, ht, ht'⟩ := fSatake_diag_exists f hf
  refine ⟨t, ht, fSatake_diag_mem_K ht ht' (fun i => ?_)⟩
  simp only [f]
  split_ifs <;> simp [map_zpow₀, hv]

theorem cosetT_guMap_mem_KU (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) :
    guMap g hg n k ∈ KU σ' n := by
  have hmem : ∀ M : Matrix (Fin n) (Fin n) K, (∀ i j, M i j ∈ intL K) →
      M ∈ (RingHom.mapMatrix (m := Fin n) (intL K).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  unfold KU intPts
  rw [Subgroup.mem_subgroupOf]
  refine ⟨(guMap g hg n k).2, glint_mem_range_of_integral (intL K) _ ?_ ?_⟩
  · refine hmem _ (fun i j => ?_)
    rw [guMap_val, Matrix.map_apply]
    exact (hint _).1 (fSatake_K_int hk i j)
  · rw [← Subgroup.coe_inv, ← map_inv]
    refine hmem _ (fun i j => ?_)
    rw [guMap_val, Matrix.map_apply]
    exact (hint _).1 (fSatake_K_int (inv_mem hk) i j)

end CosetTransport2
end GlobalTheory.SatInd

namespace GlobalTheory.SatInd

section CosetTransport3

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_fwd (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) (ϖ ϖ' : K) (q q' n m : ℕ)
    (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ' q') (hm : 2 * m ≤ n) (a : Fin m → ℤ)
    (y : GU σ n)
    (h : ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u₁, hu₁, k, hk, hy⟩ := h
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h0; have := hU'.2.2.2.1; rw [h0, Valuation.map_zero] at this
    exact absurd this WithZero.zero_ne_coe
  have hcv : Valued.v (g ϖ * ϖ'⁻¹) = 1 := cosetT_unit g hint hU.2.2.2.1 hU'.2.2.2.1
  have hcσ : σ' (g ϖ * ϖ'⁻¹) = g ϖ * ϖ'⁻¹ := by
    rw [map_mul, map_inv₀, ← hg, hU.2.2.1, hU'.2.2.1]
  obtain ⟨t, ht, htK⟩ := cosetT_tMat_unit hcσ hcv hm a
  have hgϖ : g ϖ = ϖ' * (g ϖ * ϖ'⁻¹) := by field_simp
  have hmap : ∀ M N : Matrix (Fin n) (Fin n) K, (M * N).map g = M.map g * N.map g :=
    fun M N => Matrix.map_mul (f := (g : K →+* K))
  have htm : (tMat ϖ n m a).map g = tMat (g ϖ) n m a := cosetT_tMat_map (g : K →+* K) ϖ n m a
  have hgu : IsBorelU (guMap g hg n u₁) := fun i j hij => by
    rw [guMap_val, Matrix.map_apply, hu₁.1 i j hij, map_zero]
  have htb : IsBorelU t := fSatake_borel_tMat ht
  refine ⟨t * guMap g hg n u₁ * t⁻¹,
    ⟨fSatake_borel_mul (fSatake_borel_mul htb hgu) (fSatake_borel_inv htb), fun i => ?_⟩,
    t * guMap g hg n k, mul_mem htK (cosetT_guMap_mem_KU g hg hint hk), ?_⟩
  · rw [fSatake_borel_diag_mul (fSatake_borel_mul htb hgu) (fSatake_borel_inv htb),
      fSatake_borel_diag_mul htb hgu, guMap_val, Matrix.map_apply, hu₁.2 i, map_one, mul_one,
      mul_comm]
    exact fSatake_borel_diag_inv htb i
  · have e : t * guMap g hg n u₁ * t⁻¹ * (t * guMap g hg n k) =
        t * guMap g hg n u₁ * guMap g hg n k := by group
    rw [Matrix.mul_assoc (tMat ϖ' n m a), ← Units.val_mul, ← Subgroup.coe_mul, e, guMap_val, hy,
      hmap, hmap, htm, hgϖ, cosetT_tMat_mul, ← ht]
    simp only [Subgroup.coe_mul, Units.val_mul, guMap_val, Matrix.mul_assoc]

theorem cosetT_iff : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q q' n m : ℕ), IsUnramInv ϖ σ q → IsUnramInv ϖ' σ' q' → 2 * m ≤ n → ∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q q' n m hU hU' hm a y
  constructor
  · exact cosetT_fwd g hg hint ϖ ϖ' q q' n m hU hU' hm a y
  · intro h
    have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := fun x => by
      apply g.injective
      rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
    have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := fun x => by
      rw [hint (g.symm x), RingEquiv.apply_symm_apply]
    have h2 := cosetT_fwd g.symm hg' hint' ϖ' ϖ q' q n m hU' hU hm a (guMap g hg n y) h
    have hyy : guMap g.symm hg' n (guMap g hg n y) = y := by
      apply Subtype.ext
      apply Units.ext
      rw [guMap_val, guMap_val]
      ext i j
      simp
    rwa [hyy] at h2

end CosetTransport3
end GlobalTheory.SatInd
