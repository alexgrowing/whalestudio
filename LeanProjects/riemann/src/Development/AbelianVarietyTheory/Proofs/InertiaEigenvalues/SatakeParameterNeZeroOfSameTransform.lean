import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryIwasawaCellBoundSmallTorusDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SatNonzero

variable {m : ℕ}

def mon (α : Fin m → ℂ) (a : Fin m → ℤ) : ℂ := ∏ i, α i ^ a i

def ev0 (α : Fin m → ℂ) : ((Fin m → ℤ) →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ (mon α)

theorem laurentCoeffEvalLinear_apply (α : Fin m → ℂ) (s : (Fin m → ℤ) →₀ ℂ) :
    ev0 α s = s.sum fun a c => c * ∏ i, α i ^ a i := by
  simp [ev0, Finsupp.linearCombination_apply, mon, smul_eq_mul]

theorem laurentCoeffEvalLinear_single (α : Fin m → ℂ) (a : Fin m → ℤ) (c : ℂ) : ev0 α (Finsupp.single a c) = c * mon α a := by
  simp [ev0, Finsupp.linearCombination_single, smul_eq_mul]

theorem mon_zero (α : Fin m → ℂ) : mon α 0 = 1 := by simp [mon]

theorem mon_single (α : Fin m → ℂ) (j : Fin m) (k : ℤ) : mon α (Pi.single j k) = α j ^ k := by
  unfold mon
  rw [Finset.prod_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zpow_zero]) (by simp),
    Pi.single_eq_same]

theorem mon_add (α : Fin m → ℂ) (a b : Fin m → ℤ) (h : ∀ i, 0 ≤ a i * b i) :
    mon α (a + b) = mon α a * mon α b := by
  unfold mon
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply]
  refine zpow_add' ?_
  by_cases h1 : a i + b i = 0
  · right; right
    have := h i
    constructor <;> nlinarith
  · exact Or.inr (Or.inl h1)

theorem mon_e (α : Fin m → ℂ) (j : Fin m) : mon α (Pi.single j 1) = α j := by
  rw [mon_single, zpow_one]

theorem mon_ne (α : Fin m → ℂ) (j : Fin m) : mon α (-Pi.single j 1) = (α j)⁻¹ := by
  rw [← Pi.single_neg, mon_single, zpow_neg_one]

theorem quad (α : Fin m → ℂ) (j k : Fin m) :
    mon α (Pi.single j 1 + Pi.single k 1) + mon α (Pi.single j 1 + -Pi.single k 1) +
        mon α (Pi.single k 1 + -Pi.single j 1) + mon α (-Pi.single j 1 + -Pi.single k 1) =
      (α j + (α j)⁻¹) * (α k + (α k)⁻¹) + if j = k then 2 * (1 - α j * (α j)⁻¹) else 0 := by
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, add_neg_cancel, mon_zero,
      mon_add _ _ _ (fun i => mul_self_nonneg _), mon_add _ _ _ (fun i => mul_self_nonneg _), mon_e, mon_ne]
    ring
  · have h0 : ∀ i, (Pi.single j (1 : ℤ) : Fin m → ℤ) i * (Pi.single k (1 : ℤ) : Fin m → ℤ) i = 0 := fun i => by
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_of_ne hjk, mul_zero]
      · rw [Pi.single_eq_of_ne hi, zero_mul]
    rw [if_neg hjk, add_zero,
      mon_add _ _ _ (fun i => by rw [h0 i]),
      mon_add _ _ _ (fun i => by rw [Pi.neg_apply, mul_neg, h0 i, neg_zero]),
      mon_add _ _ _ (fun i => by rw [Pi.neg_apply, mul_neg, mul_comm, h0 i, neg_zero]),
      mon_add _ _ _ (fun i => by rw [Pi.neg_apply, Pi.neg_apply, neg_mul_neg, h0 i]),
      mon_e, mon_e, mon_ne, mon_ne]
    ring

def lin (c₀ : ℂ) (a b : Fin m → ℂ) : (Fin m → ℤ) →₀ ℂ :=
  Finsupp.single 0 c₀ + ∑ k, (Finsupp.single (Pi.single k 1) (a k) + Finsupp.single (-Pi.single k 1) (b k))

theorem laurentCoeffEval_linearCoeffsAtBasis (α : Fin m → ℂ) (c₀ : ℂ) (a b : Fin m → ℂ) :
    ev0 α (lin c₀ a b) = c₀ + ∑ k, (a k * α k + b k * (α k)⁻¹) := by
  simp only [lin, map_add, map_sum, laurentCoeffEvalLinear_single, mon_zero, mon_e, mon_ne, mul_one]

def sqCoeff (c₀ A : ℂ) : (Fin m → ℤ) →₀ ℂ :=
  Finsupp.single 0 (c₀ ^ 2) + ∑ k, (Finsupp.single (Pi.single k 1) (2 * c₀ * A) +
    Finsupp.single (-Pi.single k 1) (2 * c₀ * A)) +
  ∑ j, ∑ k, (Finsupp.single (Pi.single j 1 + Pi.single k 1) (A ^ 2) +
    Finsupp.single (Pi.single j 1 + -Pi.single k 1) (A ^ 2) +
    Finsupp.single (Pi.single k 1 + -Pi.single j 1) (A ^ 2) +
    Finsupp.single (-Pi.single j 1 + -Pi.single k 1) (A ^ 2))

theorem laurentCoeffEval_squareSymmetricCoeffs (α : Fin m → ℂ) (c₀ A : ℂ) :
    ev0 α (sqCoeff c₀ A) = (c₀ + A * ∑ k, (α k + (α k)⁻¹)) ^ 2 + 2 * A ^ 2 * ∑ k, (1 - α k * (α k)⁻¹) := by
  have e : ∀ j k, ev0 α (Finsupp.single (Pi.single j 1 + Pi.single k 1) (A ^ 2) +
      Finsupp.single (Pi.single j 1 + -Pi.single k 1) (A ^ 2) +
      Finsupp.single (Pi.single k 1 + -Pi.single j 1) (A ^ 2) +
      Finsupp.single (-Pi.single j 1 + -Pi.single k 1) (A ^ 2)) =
      A ^ 2 * ((α j + (α j)⁻¹) * (α k + (α k)⁻¹) + if j = k then 2 * (1 - α j * (α j)⁻¹) else 0) := by
    intro j k
    rw [← quad]
    simp only [map_add, laurentCoeffEvalLinear_single]
    ring
  rw [sqCoeff, map_add, map_add, map_sum, map_sum, Finset.sum_congr rfl fun j _ =>
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => e j k)]
  simp only [map_add, laurentCoeffEvalLinear_single, mon_zero, mon_e, mon_ne, mul_one]
  have h1 : ∑ j, ∑ k, A ^ 2 * ((α j + (α j)⁻¹) * (α k + (α k)⁻¹) + if j = k then 2 * (1 - α j * (α j)⁻¹) else 0) =
      A ^ 2 * (∑ k, (α k + (α k)⁻¹)) ^ 2 + 2 * A ^ 2 * ∑ k, (1 - α k * (α k)⁻¹) := by
    rw [pow_two (∑ k, (α k + (α k)⁻¹)), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
    ring
  have h2 : ∑ k, (2 * c₀ * A * α k + 2 * c₀ * A * (α k)⁻¹) = 2 * c₀ * A * ∑ k, (α k + (α k)⁻¹) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2]
  ring

theorem laurentCoeffs_eq_of_eval_on_complexTorus (s s' : (Fin m → ℤ) →₀ ℂ)
    (h : ∀ x : Fin m → ℂˣ, ev0 (fun i => (x i : ℂ)) s = ev0 (fun i => (x i : ℂ)) s') : s = s' := by
  have li := (linearIndependent_monoidHom (Fin m → ℂˣ) ℂ).comp _
    (GlobalTheory.InertThetaCompare.mono_injective (m := m))
  rw [← sub_eq_zero]
  refine linearIndependent_iff.1 li _ ?_
  funext x
  have hx := h x
  rw [← sub_eq_zero, ← map_sub] at hx
  rw [Pi.zero_apply, ← hx, Finsupp.linearCombination_apply, ev0, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
    Finset.sum_apply]
  rfl

theorem eq_of_sum_abs_le_one (κ : Fin m → ℤ) (h : ∑ i, |κ i| ≤ 1) :
    κ = 0 ∨ ∃ k, κ = Pi.single k 1 ∨ κ = -Pi.single k 1 := by
  by_cases h0 : κ = 0
  · exact Or.inl h0
  right
  obtain ⟨k, hk⟩ : ∃ k, κ k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (funext hc)
  have hsplit := Finset.add_sum_erase Finset.univ (fun i => |κ i|) (Finset.mem_univ k)
  have hk1 : 1 ≤ |κ k| := Int.one_le_abs hk
  have hnn : 0 ≤ ∑ i ∈ Finset.univ.erase k, |κ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hrest : ∑ i ∈ Finset.univ.erase k, |κ i| = 0 := by linarith
  have hz : ∀ i, i ≠ k → κ i = 0 := fun i hi => abs_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)).1 hrest i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩))
  have hab : |κ k| = 1 := by linarith
  refine ⟨k, ?_⟩
  rcases (abs_eq zero_le_one).1 hab with e | e
  · left
    funext i
    by_cases hi : i = k
    · subst hi; rw [e, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hi, hz i hi]
  · right
    funext i
    by_cases hi : i = k
    · subst hi; rw [e, Pi.neg_apply, Pi.single_eq_same]
    · rw [Pi.neg_apply, Pi.single_eq_of_ne hi, hz i hi, neg_zero]

theorem single_ne_zero' (k : Fin m) : (Pi.single k 1 : Fin m → ℤ) ≠ 0 := fun h => by
  simpa using congrFun h k

theorem neg_single_ne_zero' (k : Fin m) : (-Pi.single k 1 : Fin m → ℤ) ≠ 0 := fun h => by
  simpa using congrFun h k

theorem single_ne_neg_single (k l : Fin m) : (Pi.single k 1 : Fin m → ℤ) ≠ -Pi.single l 1 := fun h => by
  have := congrFun h k
  rw [Pi.single_eq_same, Pi.neg_apply] at this
  by_cases hl : k = l
  · subst hl; rw [Pi.single_eq_same] at this; omega
  · rw [Pi.single_eq_of_ne hl] at this; omega

theorem eq_lin (s : (Fin m → ℤ) →₀ ℂ) (h : ∀ κ, s κ ≠ 0 → κ = 0 ∨ ∃ k, κ = Pi.single k 1 ∨ κ = -Pi.single k 1) :
    s = lin (s 0) (fun k => s (Pi.single k 1)) (fun k => s (-Pi.single k 1)) := by
  classical
  have hinj : ∀ k l : Fin m, (Pi.single k 1 : Fin m → ℤ) = Pi.single l 1 ↔ k = l :=
    fun k l => ⟨fun e => by
      by_contra hne
      have := congrFun e k
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
      exact one_ne_zero this, fun e => e ▸ rfl⟩
  have hinj' : ∀ k l : Fin m, (-Pi.single k 1 : Fin m → ℤ) = -Pi.single l 1 ↔ k = l :=
    fun k l => neg_inj.trans (hinj k l)
  ext κ
  simp only [lin, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  by_cases h0 : κ = 0
  · subst h0
    simp [single_ne_zero', neg_single_ne_zero']
  by_cases h1 : ∃ k, κ = Pi.single k 1
  · obtain ⟨j, rfl⟩ := h1
    simp only [if_neg (Ne.symm h0), zero_add, hinj, fun k => (single_ne_neg_single j k).symm, if_false, add_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h2 : ∃ k, κ = -Pi.single k 1
  · obtain ⟨j, rfl⟩ := h2
    simp only [if_neg (Ne.symm h0), zero_add, hinj', single_ne_neg_single, if_false, zero_add,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  push_neg at h1 h2
  have hs : s κ = 0 := by
    by_contra hc
    rcases h κ hc with e | ⟨k, e | e⟩
    · exact h0 e
    · exact h1 k e
    · exact h2 k e
  rw [hs, if_neg (Ne.symm h0), zero_add]
  refine (Finset.sum_eq_zero fun k _ => ?_).symm
  rw [if_neg (fun e => h1 k e.symm), if_neg (fun e => h2 k e.symm), add_zero]

theorem satU_ne_zero : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K)
    (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂ) (β : Fin (n / 2) → ℂˣ),
    (∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h (fun i => (β i : ℂ))) →
    ∀ i, α i ≠ 0 := by
  intro K _ _ _ ϖ σ q n hU α β hαβ i₀ hα₀
  classical
  have hm0 : 0 < n / 2 := Fin.pos i₀
  let j₀ : Fin (n / 2) := ⟨0, hm0⟩
  obtain ⟨t, ht⟩ := Formalism.UG.P.fSatake_tMat_exists (n := n) hU (Nat.mul_div_le n 2) (Pi.single j₀ (1 : ℤ))
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have hT : Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) :=
    Formalism.UG.Final.DosetIndMem _ _ ℂ t
  have hT2 := Formalism.UG.Final.HeckeConvMem _ _ ℂ hK _ hT _ hT
  obtain ⟨s, hs, hsupp, hcoef⟩ := GlobalTheory.LFun.SatCoef.satU_laurent K ϖ σ q n hU _ hT
  obtain ⟨s₂, hs₂, -, -⟩ := GlobalTheory.LFun.SatCoef.satU_laurent K ϖ σ q n hU _ hT2

  have hsup : ∀ κ, s κ ≠ 0 → κ = 0 ∨ ∃ k, κ = Pi.single k 1 ∨ κ = -Pi.single k 1 := by
    intro κ hκ
    obtain ⟨g, hg, u, hu, k, hk, eg⟩ := hsupp κ hκ
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ Formalism.UG.KU σ n, ∃ b ∈ Formalism.UG.KU σ n, g = a * t * b := by
      by_contra h0
      exact hg (GlobalTheory.WeylGL.dosetInd_of_not h0)
    have hε : ∀ i, |(Pi.single j₀ (1 : ℤ) : Fin (n / 2) → ℤ) i| ≤ 1 := fun i => by
      by_cases hi : i = j₀
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    have hb := GlobalTheory.LFun.CellBound.cell_bound K ϖ σ q n hU (Pi.single j₀ 1) κ u k a b hε hu hk ha hb
      (by rw [← eg, ← ht]; rfl)
    refine eq_of_sum_abs_le_one κ (hb.2.trans (le_of_eq ?_))
    rw [Finset.sum_eq_single j₀ (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
    simp
  set c₀ := s 0
  set a : Fin (n / 2) → ℂ := fun k => s (Pi.single k 1)
  set b : Fin (n / 2) → ℂ := fun k => s (-Pi.single k 1)
  have hlin := eq_lin s hsup
  have hF : ∀ γ : Fin (n / 2) → ℂ, Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) γ =
      c₀ + ∑ k, (a k * γ k + b k * (γ k)⁻¹) := fun γ => by
    rw [hs γ, ← laurentCoeffEvalLinear_apply, hlin, laurentCoeffEval_linearCoeffsAtBasis]

  have hW := fun γ => GlobalTheory.SatBcZero.weyl_of_coeff GlobalTheory.SatBcZero.coeff_symm.1 GlobalTheory.SatBcZero.coeff_symm.2 K ϖ σ q n
    (n / 2) hU (by omega) (by omega) γ _ hT
  have hpt : ∀ (j : Fin (n / 2)) (c : ℂ),
      ∑ k, (a k * Function.update (0 : Fin (n / 2) → ℂ) j c k + b k * (Function.update (0 : Fin (n / 2) → ℂ) j c k)⁻¹) =
        a j * c + b j * c⁻¹ := fun j c => by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Function.update_of_ne hk]) (by simp)]
    simp
  have hab : ∀ j, a j = b j := fun j => by
    have e := (hW (Function.update 0 j 2)).2 j
    rw [hF, hF, Function.update_idem, Function.update_self, hpt, hpt] at e
    have : (3 / 2 : ℂ) * (a j - b j) = 0 := by linear_combination -e
    simpa [sub_eq_zero] using this
  have haa : ∀ j, a j = a j₀ := fun j => by
    have e := (hW (Function.update 0 j 2)).1 (Equiv.swap j₀ j)
    rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right] at e
    have e0 : (0 : Fin (n / 2) → ℂ) ∘ Equiv.swap j₀ j = 0 := rfl
    rw [e0, hF, hF, hpt, hpt, ← hab, ← hab] at e
    have : (5 / 2 : ℂ) * (a j - a j₀) = 0 := by linear_combination -e
    simpa [sub_eq_zero] using this
  set A := a j₀
  have hA : A ≠ 0 := hcoef t _ ht rfl
  have hF' : ∀ γ : Fin (n / 2) → ℂ, Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) γ = c₀ + A * ∑ k, (γ k + (γ k)⁻¹) := by
    intro γ
    rw [hF, Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [← hab k, haa k]; ring)

  have hsq : s₂ = sqCoeff c₀ A := by
    refine laurentCoeffs_eq_of_eval_on_complexTorus _ _ fun x => ?_
    rw [laurentCoeffEvalLinear_apply, ← hs₂, laurentCoeffEval_squareSymmetricCoeffs,
      Formalism.UG.Final.SatMul K ϖ σ q n (n / 2) hU (by omega) (by omega) _ (fun i => (x i).ne_zero) _ hT _ hT, hF']
    have : ∑ k, (1 - (x k : ℂ) * ((x k : ℂ))⁻¹) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [mul_inv_cancel₀ (x k).ne_zero, sub_self]
    rw [this]
    ring
  have e1 : Formalism.UG.SatU ϖ q (Formalism.UG.conv (Formalism.UG.KU σ n) (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t)
      (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t)) α = (c₀ + A * ∑ k, (α k + (α k)⁻¹)) ^ 2 + 2 * A ^ 2 * ∑ k, (1 - α k * (α k)⁻¹) := by
    rw [hs₂, ← laurentCoeffEvalLinear_apply, hsq, laurentCoeffEval_squareSymmetricCoeffs]
  have e2 : Formalism.UG.SatU ϖ q (Formalism.UG.conv (Formalism.UG.KU σ n) (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t)
      (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t)) α = (c₀ + A * ∑ k, (α k + (α k)⁻¹)) ^ 2 := by
    rw [hαβ _ hT2, Formalism.UG.Final.SatMul K ϖ σ q n (n / 2) hU (by omega) (by omega) _ (fun i => (β i).ne_zero) _ hT _ hT,
      ← hαβ _ hT, hF']
    ring
  rw [e2] at e1
  have hcnt : ∑ k, (1 - α k * (α k)⁻¹) = ((Finset.univ.filter fun k => α k = 0).card : ℂ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : α k = 0
    · simp [hk]
    · simp [hk, mul_inv_cancel₀ hk]
  have hc : ((Finset.univ.filter fun k => α k = 0).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, hα₀⟩))
  rw [hcnt] at e1
  have : 2 * A ^ 2 * ((Finset.univ.filter fun k => α k = 0).card : ℂ) = 0 := by linear_combination -e1
  exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hA)) hc this

end GlobalTheory.SatNonzero
