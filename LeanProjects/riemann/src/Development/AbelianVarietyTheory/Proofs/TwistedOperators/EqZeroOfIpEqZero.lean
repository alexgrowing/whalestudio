import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

namespace GlobalTheory.LinUnit

section General
open MeasureTheory Matrix GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

noncomputable def fac (g : GL a k) (h : GL b k) : ℝ :=
  nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card b : ℝ) / 2) *
    nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ) / 2)

theorem fac_pos (g : GL a k) (h : GL b k) : 0 < fac g h :=
  mul_pos (Real.rpow_pos_of_pos (nabs_pos' _) _) (Real.rpow_pos_of_pos (nabs_pos' _) _)

theorem om_one_eq (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om 1 g h Φ = fun x => (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) := by
  funext x
  simp [om, fac]

theorem nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem fac_sq_mul (g : GL a k) (h : GL b k) :
    fac g h * fac g h * (nabs k (Matrix.GeneralLinearGroup.det h⁻¹) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) = 1 := by
  have hg := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos' (Matrix.GeneralLinearGroup.det h)
  rw [map_inv, nabs_inv, Real.inv_rpow hh.le, ← Real.rpow_neg hh.le, neg_neg, fac]
  set x := nabs k (Matrix.GeneralLinearGroup.det g)
  set y := nabs k (Matrix.GeneralLinearGroup.det h)
  have e1 : x ^ ((Fintype.card b : ℝ) / 2) * x ^ ((Fintype.card b : ℝ) / 2) * x ^ (-(Fintype.card b : ℝ)) = 1 := by
    rw [← Real.rpow_add hg, ← Real.rpow_add hg]; simp
  have e2 : y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (Fintype.card a : ℝ) = 1 := by
    rw [← Real.rpow_add hh, ← Real.rpow_add hh]; simp
  linear_combination (y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) *
    y ^ (Fintype.card a : ℝ)) * e1 + e2

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem ip_om_one (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ip ν (om 1 g h Φ) (om 1 g h Φ) = ip ν Φ Φ := by
  have key := integral_comp_mul_mul_volM ν g h⁻¹ (fun x => Φ x * (starRingEnd ℂ) (Φ x))
  have e := fac_sq_mul g h
  rw [om_one_eq]
  unfold ip
  have : ∀ x : Matrix b a k, (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) *
      (starRingEnd ℂ) ((fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val)) = ((fac g h * fac g h : ℝ) : ℂ) *
      (Φ ((h⁻¹).val * x * g.val) * (starRingEnd ℂ) (Φ ((h⁻¹).val * x * g.val))) := by
    intro x
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  simp_rw [this]
  rw [integral_const_mul, key, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, e]
  simp

omit [DecidableEq a] [DecidableEq b] in

theorem eq_zero_of_ip_eq_zero {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) (h0 : ip ν Φ Φ = 0) : Φ = 0 := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨h2, ht⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (Matrix b a k) := inferInstanceAs (BorelSpace (b → a → k))
  have : (volM ν b a).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : Continuous fun x => Complex.normSq (Φ x) := Complex.continuous_normSq.comp hl.continuous
  have hs : HasCompactSupport fun x => Complex.normSq (Φ x) := hK.comp_left (g := Complex.normSq) (by simp)
  have e : ∫ x, Complex.normSq (Φ x) ∂(volM ν b a) = 0 := by
    unfold ip at h0
    simp_rw [Complex.mul_conj] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  have := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
    (hc.integrable_of_hasCompactSupport hs)).1 e
  have := (hc.ae_eq_iff_eq _ continuous_zero).1 this
  funext x
  exact Complex.normSq_eq_zero.1 (congrFun this x)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem linOm_unitary : ∀ (D : D7) (v : FinPl D) (m n : ℕ) (g : GL (Fin n) (Fv D.host.F v)) (h : GL (Fin m) (Fv D.host.F v)), (∃ r : ℝ, 0 < r ∧ ∀ Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ, linOm v g h Φ = fun x => (r : ℂ) * Φ ((h⁻¹).val * x * g.val)) ∧ ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), linOm v g h Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) ∧ ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (linOm v g h Φ) (linOm v g h Φ) = GlobalTheory.SplitWeil.ip ν Φ Φ ∧ (GlobalTheory.SplitWeil.ip ν Φ Φ = 0 → Φ = 0) := by
  intro D v m n g h
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨⟨fac g h, fac_pos g h, fun Φ => om_one_eq g h Φ⟩, fun Φ hΦ => ⟨?_, fun ν hν => ⟨?_, ?_⟩⟩⟩
  · exact GlobalTheory.SplitWeil.Model.om_mem_SB 1 g h hΦ
  · exact ip_om_one ν g h Φ
  · exact eq_zero_of_ip_eq_zero ν hΦ

end GlobalTheory.LinUnit
