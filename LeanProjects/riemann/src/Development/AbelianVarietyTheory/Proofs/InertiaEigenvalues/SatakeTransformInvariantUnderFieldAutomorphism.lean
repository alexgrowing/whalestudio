import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInvAuto

open Formalism.UG GlobalTheory.SatInd

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

def diagExp (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

theorem tMat_eq_diag (x : K) (n m : ℕ) (a : Fin m → ℤ) :
    tMat x n m a = Matrix.diagonal fun i => x ^ diagExp n m a i := by
  unfold tMat diagExp
  congr 1
  funext i
  split_ifs <;> simp

theorem diagExp_rev {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (i : Fin n) :
    diagExp n m a i.rev = -diagExp n m a i := by
  have hi := i.isLt
  have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
  unfold diagExp
  by_cases h1 : (i : ℕ) < m
  · have h2 : ¬ (i.rev : ℕ) < m := by omega
    have h3 : n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m := by omega
    rw [dif_neg h2, dif_pos h3, dif_pos h1]
    rw [show (⟨n - 1 - (i.rev : ℕ), h3.2⟩ : Fin m) = ⟨i, h1⟩ from
      Fin.ext (show n - 1 - (i.rev : ℕ) = (i : ℕ) by omega)]
  · by_cases h4 : n - m ≤ (i : ℕ) ∧ n - 1 - (i : ℕ) < m
    · have h2 : (i.rev : ℕ) < m := by omega
      rw [dif_pos h2, dif_neg h1, dif_pos h4, neg_neg]
      rw [show (⟨(i.rev : ℕ), h2⟩ : Fin m) = ⟨n - 1 - i, h4.2⟩ from Fin.ext hr]
    · have h2 : ¬ (i.rev : ℕ) < m := by omega
      have h3 : ¬ (n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m) := by omega
      rw [dif_neg h2, dif_neg h3, dif_neg h1, dif_neg h4, neg_zero]

theorem div_mem_intL {ϖ x : K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hx : x ∈ intL K) (hx' : x⁻¹ ∉ intL K) : x / ϖ ∈ intL K := by
  unfold intL at *
  rw [Valuation.mem_integer_iff] at *
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hx'
    simp
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx (fun h => hx' (by rw [map_inv₀, h, inv_one]))
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [map_div₀, hϖ, ← WithZero.exp_log hv0, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem map_mul_mat (g : K ≃+* K) {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    (A * B).map g = A.map g * B.map g := by
  ext i j
  simp [Matrix.mul_apply, map_sum]

end Local

section Cell

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cell_guMap (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ : K} {q n m : ℕ} (hU : IsUnramInv ϖ σ q)
    (hm : 2 * m ≤ n) (a : Fin m → ℤ) (y : GU σ n)
    (hy : ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u, hu, k, hk, hyuk⟩ := hy
  obtain ⟨-, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖint : ϖ ∈ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖinv : ϖ⁻¹ ∉ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, map_inv₀, hϖ', ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp]; norm_num
  set c : K := g ϖ / ϖ with hc
  have hgϖ : g ϖ = ϖ * c := by rw [hc]; field_simp
  have hc0 : c ≠ 0 := div_ne_zero ((map_ne_zero g).2 h0) h0
  have hcint : c ∈ intL K := div_mem_intL hϖ' ((hint ϖ).1 hϖint)
    (by rw [← map_inv₀]; exact fun h => hϖinv ((hint _).2 h))
  have hcinv : c⁻¹ ∈ intL K := by
    have h1 : g.symm ϖ / ϖ ∈ intL K := div_mem_intL hϖ' (by rw [hint]; simpa using hϖint)
      (by rw [← map_inv₀, hint]; simpa using hϖinv)
    have h2 := (hint _).1 h1
    rw [map_div₀, RingEquiv.apply_symm_apply] at h2
    rw [hc, inv_div]; exact h2
  have hcv : Valued.v c = 1 := by
    unfold intL at hcint hcinv
    rw [Valuation.mem_integer_iff] at hcint hcinv
    refine le_antisymm hcint ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c * c⁻¹) := by rw [mul_inv_cancel₀ hc0, map_one]
      _ = Valued.v c * Valued.v c⁻¹ := map_mul _ _ _
      _ ≤ Valued.v c * 1 := mul_le_mul' le_rfl hcinv
      _ = Valued.v c := mul_one _
  have hσc : σ c = c := by rw [hc, map_div₀, hσϖ, ← hg, hσϖ]
  set e : Fin n → K := fun i => c ^ diagExp n m a i with he
  have he0 : ∀ i, e i ≠ 0 := fun i => zpow_ne_zero _ hc0
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) e (fun i => by
    simp only [he]; rw [map_zpow₀, hσc, diagExp_rev hm, ← zpow_add₀ hc0, add_neg_cancel, zpow_zero])
  have hdK : d ∈ KU σ n := by
    have hI : Formalism.UG.P.fIwasawaInt (((d : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      intro i j
      rw [hd]
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, he]; simp only; rw [map_zpow₀, hcv, one_zpow]
      · rw [Matrix.diagonal_apply_ne _ hij, map_zero]; exact zero_le'
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ d) hI
    have e' : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ d) = d := Subtype.ext (Units.ext rfl)
    rwa [e'] at this
  have hk1 : guMap g hg n k ∈ KU σ n := (mem_KU_iff_guMap g hg hint k).1 hk
  refine ⟨d * guMap g hg n u * d⁻¹, ?_, d * guMap g hg n k, (KU σ n).mul_mem hdK hk1, ?_⟩
  · refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.1 i j hij, map_zero, mul_zero, zero_mul]
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.2 i, map_one, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [guMap_val, hyuk, map_mul_mat, map_mul_mat]
    simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val]
    rw [tMat_eq_diag, Matrix.diagonal_map (map_zero _)]
    have hD : (Matrix.diagonal fun i => g (ϖ ^ diagExp n m a i)) =
        Matrix.diagonal (fun i => ϖ ^ diagExp n m a i) * Matrix.diagonal e := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [map_zpow₀, hgϖ, mul_zpow]
    have hinv : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (he0 i)
    rw [hD]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun i => (e i)⁻¹) (Matrix.diagonal e), hinv, Matrix.one_mul]

end Cell

open Classical in

theorem satU_guMap_self : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (ϖ : K) (q n m : ℕ), Formalism.UG.IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h : Formalism.UG.GU σ n → ℂ, Formalism.UG.IsBiInv (Formalism.UG.KU σ n) h → ∀ α : Fin m → ℂ, Formalism.UG.SatU ϖ q (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) α = Formalism.UG.SatU ϖ q h α := by
  intro K _ _ g σ hg hint ϖ q n m hU hm1 _ h hbi α
  have hg' : ∀ x, g.symm (σ x) = σ (g.symm x) := by
    intro x; apply g.injective; rw [hg]; simp
  have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := by
    intro x; rw [hint (g.symm x)]; simp
  refine satU_guMap g hg hint ϖ ϖ q n m h hbi
    (fun a y => ⟨cell_guMap g hg hint hU hm1 a y, fun hy => ?_⟩) α
  have := cell_guMap g.symm hg' hint' hU hm1 a (guMap g hg n y) hy
  rwa [guMap_symm_comp g hg hg' y] at this

end GlobalTheory.SatInvAuto
