import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.CosetVanish

theorem integral_coset_singular_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (μ : Measure (GL A' k)) [μ.IsMulLeftInvariant] (ν : kˣ →* ℂˣ) (z : ℂ), ¬ IsUnram ν → ∀ (c : kˣ) (x : Matrix A' A' k), x.det = 0 → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  intro k _ _ _ _ _ _ A' _ _ μ _ ν z hν c x hx
  classical
  obtain ⟨u, hu1, hνu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hν fun y hy => h y hy
  obtain ⟨w0, hw0, hw0x⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := x)).2 hx
  obtain ⟨j, hj⟩ : ∃ j, w0 j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  haveI : Nonempty A' := ⟨j⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => valuation k (w0 i))
  have hwi₀ : w0 i₀ ≠ 0 := by
    intro h0
    have := hi₀ j
    rw [h0, map_zero] at this
    exact hj ((valuation k).zero_iff.1 (le_antisymm this zero_le'))
  set w : A' → k := (w0 i₀)⁻¹ • w0 with hwdef
  have hwi : w i₀ = 1 := by simp [w, hwi₀]
  have hwint : ∀ i, valuation k (w i) ≤ 1 := by
    intro i
    simp only [w, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hpos : valuation k (w0 i₀) ≠ 0 := by simpa using hwi₀
    calc (valuation k (w0 i₀))⁻¹ * valuation k (w0 i) ≤ (valuation k (w0 i₀))⁻¹ * valuation k (w0 i₀) :=
          by gcongr; exact hi₀ i
      _ = 1 := inv_mul_cancel₀ hpos
  have hwx : ∀ j, ∑ l, w l * x l j = 0 := by
    intro j
    have := congrFun hw0x j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    simp only [w, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  set e : A' → k := Pi.single i₀ ((u : k) - 1) with hedef
  have he : ∀ i, valuation k (e i) ≤ 1 := by
    intro i
    by_cases h : i = i₀
    · subst h
      simp only [e, Pi.single_eq_same]
      refine ((valuation k).map_sub _ _).trans ?_
      simp [hu1]
    · simp [e, Pi.single_eq_of_ne h]
  have hwe : ∑ l, w l * e l = (u : k) - 1 := by
    simp [e, Pi.single_apply, hwi]
  set M : Matrix A' A' k := 1 + Matrix.vecMulVec e w with hMdef
  have hMdet : M.det = u := by
    rw [hMdef, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct]
    rw [hwe]; ring
  have hMne : M.det ≠ 0 := by rw [hMdet]; exact u.ne_zero
  set m : GL A' k := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMne with hmdef
  have hmdet : gdet m = u := by
    ext; simp [gdet, Matrix.GeneralLinearGroup.val_det_apply, m, hMdet]
  have hmval : (m : Matrix A' A' k) = M := rfl
  have hMG : ∀ (G : Matrix A' A' k) i j, (M * G) i j = G i j + e i * ∑ l, w l * G l j := by
    intro G i j
    rw [hMdef, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.vecMulVec_apply, mul_assoc, Finset.mul_sum]
  have hsum : ∀ (G : Matrix A' A' k) j, ∑ l, w l * G l j = ∑ l, w l * (G l j - x l j) := by
    intro G j
    simp only [mul_sub, Finset.sum_sub_distrib, hwx, sub_zero]
  have hkey : ∀ g : GL A' k, (m * g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}) ↔
      g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
    intro g
    simp only [Set.mem_setOf_eq, Units.val_mul, hmval, hMG]
    constructor
    · intro h i j
      set s := ∑ l, w l * (g.val l j) with hs
      have h2 : ∑ l, w l * ((g.val l j + e l * s) - x l j) = (u : k) * s := by
        have : ∀ l, w l * ((g.val l j + e l * s) - x l j) = w l * (g.val l j - x l j) + (w l * e l) * s := by
          intro l; ring
        simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hwe, ← hsum, ← hs]
        ring
      have hsv : valuation k s ≤ valuation k (c : k) := by
        have : s = (u : k)⁻¹ * ∑ l, w l * ((g.val l j + e l * s) - x l j) := by
          rw [h2, ← mul_assoc, inv_mul_cancel₀ u.ne_zero, one_mul]
        rw [this, map_mul, map_inv₀, hu1, inv_one, one_mul]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j) |>.trans' (by rfl)
      have : g.val i j - x i j = ((g.val i j + e i * s) - x i j) + (-(e i * s)) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [Valuation.map_neg, map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
    · intro h i j
      have hsv : valuation k (∑ l, w l * g.val l j) ≤ valuation k (c : k) := by
        rw [hsum]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j)
      have : g.val i j + e i * (∑ l, w l * g.val l j) - x i j = (g.val i j - x i j) + e i * (∑ l, w l * g.val l j) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  have hpre : (fun g => m * g) ⁻¹' S = S := Set.ext hkey
  set χ : GL A' k → ℂ := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z with hχ
  have hχm : ∀ g, χ (m * g) = (ν u : ℂ) * χ g := by
    intro g
    simp only [χ, gdet, map_mul] at hmdet ⊢
    rw [hmdet, apow_mul, apow_of_valuation_eq_one hu1, Units.val_mul]
    ring
  have hmp : MeasurePreserving (fun g => m * g) μ μ := measurePreserving_mul_left μ m
  have hemb : MeasurableEmbedding (fun g => m * g) := (MeasurableEquiv.mulLeft m).measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb χ S
  rw [hpre] at h1
  simp only [hχm, integral_const_mul] at h1
  change ∫ g in S, χ g ∂μ = 0
  have hne : (ν u : ℂ) ≠ 1 := by
    intro h; exact hνu (Units.ext h)
  have h3 : ((ν u : ℂ) - 1) * ∫ g in S, χ g ∂μ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.CosetVanish
