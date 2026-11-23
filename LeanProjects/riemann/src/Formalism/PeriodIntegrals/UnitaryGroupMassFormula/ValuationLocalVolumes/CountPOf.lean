import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddSmul

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def clsP (a : ℕ) (ϖ : Fv F v) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    Set (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) :=
  QuotientAddGroup.mk '' {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ PrimT v Λ a ∧
    (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ T}

def MeasP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    MeasurableAdd (TupV (E := E) v n a) ∧ MeasurableSet (LamT v Λ a) ∧
      MeasurableSet (lamP v Λ a ϖ : Set (TupV (E := E) v n a))

def IdxP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a)

def ClsP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ℝ) =
      qv v ^ (2 * n * a - a ^ 2) * prodEtaB (E := E) v n a

theorem countP_of (a : ℕ) (Y : TupV (E := E) v n a) (hM : MeasP σ J ψ v Λ a Y)
    (hI : IdxP σ J ψ v Λ a Y) (hC : ClsP σ J ψ v Λ a Y) (hPC : PrimCos σ J ψ v Λ a) : CountP σ J ψ v Λ a Y := by
  intro hG hμ ϖ hϖ
  obtain ⟨hMA, hL, hP⟩ := hM hG ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  have hcos : ∀ x ∈ PrimT v Λ a, ∀ Z ∈ LamT v Λ a, x + sc (E := E) v ϖ • Z ∈ PrimT v Λ a := by
    intro x hx Z hZ
    apply hPC hG.1 hG.2.1 hSD hG.2.2.2.1 ϖ hϖ x hx
    refine (PI.VolStabSW.mem_smulSub _ _ _).2 ⟨Z, hZ, ?_⟩
    funext i p
    show ϖ ^ (0 + 1) • Z i p = sc (E := E) v ϖ * Z i p
    rw [zero_add, pow_one, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  set μ := dX σ J ψ v a with hμdef
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, dX, dif_pos hμ]
    exact hμ.choose_spec.1
  have hPL : lamP v Λ a ϖ ≤ lamA v Λ a := by
    rintro _ ⟨Z, hZ, rfl⟩ i
    have : (sc (E := E) v ϖ • Z) i = sc (E := E) v ϖ • Z i := rfl
    show (sc (E := E) v ϖ • Z) i ∈ latLoc (E := E) v Λ
    rw [this]
    have e : sc (E := E) v ϖ • Z i = (⟨ϖ, unif_int v hϖ⟩ : v.adicCompletionIntegers F) • Z i := by
      ext p
      simp only [Pi.smul_apply, smul_eq_mul]
      show _ = ϖ • Z i p
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
      rfl
    rw [e]
    exact (latLoc (E := E) v Λ).smul_mem _ (hZ i)
  have hIdx := hI hG ϖ hϖ
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h0
    have : qv v = 0 := by simp [qv, h0]
    linarith
  have hfin : (lamP v Λ a ϖ).relIndex (lamA v Λ a) ≠ 0 := by
    rw [hIdx]; exact pow_ne_zero _ hN0
  have eL := PI.VolStabSW.measure_eq_relIndex_mul μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hL hP hfin
  have eS := measure_image_cosets μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hP hfin
    {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ PrimT v Λ a ∧
      (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)}
    (by
      rintro x hx y ⟨Z, hZ, hZe⟩
      simp only [Set.mem_setOf_eq]
      rw [AddSubgroup.coe_add, ← hZe]
      exact ⟨hcos _ hx.1 Z hZ, nearT_add σ J v Λ hSD hϖ _ _ _ x.2 hZ hx.2⟩)
  have himg : ((↑) : lamA v Λ a → TupV (E := E) v n a) ''
      {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ PrimT v Λ a ∧
        (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)} =
      PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext X
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · rintro ⟨h1, h2⟩
      exact ⟨⟨X, h1.1⟩, ⟨h1, h2⟩, rfl⟩
  rw [himg] at eS
  have eL' : μ (LamT v Λ a) = (((lamP v Λ a ϖ).relIndex (lamA v Λ a) : ℕ) : ENNReal) *
      μ (lamP v Λ a ϖ) := eL
  rw [eS, eL', ← mul_assoc]
  congr 1
  have hcard := hC hG ϖ hϖ
  change (Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ENNReal) = _
  rw [← ENNReal.ofReal_natCast, hcard, hIdx, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  · congr 1
    have hqv : ((Ideal.absNorm v.asIdeal ^ (2 * n * a) : ℕ) : ℝ) = qv v ^ (2 * n * a) := by
      simp [qv]
    rw [hqv]
    have hle : a ^ 2 ≤ 2 * n * a := by nlinarith
    have e3 : qv v ^ (2 * n * a) = qv v ^ (2 * n * a - a ^ 2) * qv v ^ (a ^ 2) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e3]
    have e4 : qv v ^ (-((a : ℤ) ^ 2)) * qv v ^ (a ^ 2) = 1 := by
      rw [zpow_neg, show ((a : ℤ) ^ 2) = ((a ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero _ hq.ne')
    linear_combination (-(qv v ^ (2 * n * a - a ^ 2) * prodEtaB (E := E) v n a)) * e4
  · have hP0 : 0 ≤ prodEtaB (E := E) v n a := by
      unfold prodEtaB
      refine Finset.prod_nonneg fun j _ => ?_
      have hq1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
      have habs : |((etaV (E := E) v : ℤ) : ℝ)| = 1 := by
        unfold etaV; split_ifs <;> norm_num
      have h1 : ((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
        calc _ ≤ |((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))| :=
              le_abs_self _
          _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
              rw [abs_mul, abs_pow, habs, one_pow, one_mul, abs_of_nonneg (zpow_nonneg (by linarith) _)]
          _ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
      linarith
    exact mul_nonneg (zpow_nonneg hq.le _) hP0

end PI.OmVd
