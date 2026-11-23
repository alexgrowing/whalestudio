import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeComponent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*}

def dehomIdeal (i : (k : K) → ι k) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun k => (X ⟨k, i k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))

abbrev DehomRing (i : (k : K) → ι k) := MvPolynomial (Σ k, ι k) ℂ ⧸ dehomIdeal i

def dehom (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] DehomRing i :=
  Ideal.Quotient.mkₐ ℂ (dehomIdeal i)

def coneUnit (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ :=
  ∏ k, X ⟨k, i k⟩

abbrev ConeRing (i : (k : K) → ι k) := Localization.Away (coneUnit i)

theorem isUnit_coneX (i : (k : K) → ι k) (k : K) :
    IsUnit (algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)) :=
  isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (Finset.mem_univ k))) (IsLocalization.Away.algebraMap_isUnit (coneUnit i))

def coneRatio (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ConeRing i :=
  aeval fun p => (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
    algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X p)

theorem coneRatio_X_self (i : (k : K) → ι k) (k : K) : coneRatio i (X ⟨k, i k⟩) = 1 := by
  rw [coneRatio, aeval_X]
  exact (isUnit_coneX i k).val_inv_mul

def ratioMap (i : (k : K) → ι k) : DehomRing i →+* ConeRing i :=
  Ideal.Quotient.lift (dehomIdeal i) (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) (by
    have hle : dehomIdeal i ≤ RingHom.ker (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) := by
      rw [dehomIdeal, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp [coneRatio_X_self]
    exact fun a ha => hle ha)

theorem ratioMap_dehom (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    ratioMap i (dehom i f) = coneRatio i f :=
  Ideal.Quotient.lift_mk _ _ _

omit [Fintype K] in
theorem dehom_X_self (i : (k : K) → ι k) (k : K) : dehom i (X ⟨k, i k⟩) = 1 := by
  rw [← sub_eq_zero, ← map_one (dehom i), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)

theorem dehom_coneUnit (i : (k : K) → ι k) : dehom i (coneUnit i) = 1 := by
  rw [coneUnit, map_prod]
  exact Finset.prod_eq_one fun k _ => dehom_X_self i k

omit [Fintype K] in
theorem dehom_surjective (i : (k : K) → ι k) : Function.Surjective (dehom i) :=
  Ideal.Quotient.mk_surjective

def evalOne (i : (k : K) → ι k) : ConeRing i →+* DehomRing i :=
  IsLocalization.Away.lift (coneUnit i) (g := (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i))
    (by rw [AlgHom.coe_toRingHom, dehom_coneUnit]; exact isUnit_one)

theorem evalOne_algebraMap (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    evalOne i (algebraMap _ (ConeRing i) f) = dehom i f :=
  IsLocalization.lift_eq _ _

theorem evalOne_comp_algebraMap (i : (k : K) → ι k) :
    (evalOne i).comp (algebraMap _ (ConeRing i)) = (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) :=
  RingHom.ext (evalOne_algebraMap i)

theorem evalOne_comp_ratioMap (i : (k : K) → ι k) : (evalOne i).comp (ratioMap i) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply]
    have h1 : ratioMap i (Ideal.Quotient.mk (dehomIdeal i) (C c)) =
        algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
      rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio,
        aeval_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i),
        MvPolynomial.algebraMap_eq]
    rw [h1, evalOne_algebraMap]
    rfl
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, evalOne_algebraMap]
    have hu : evalOne i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      rw [IsUnit.unit_spec, evalOne_algebraMap, dehom_X_self]
    have hinv : evalOne i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      have := congrArg (evalOne i) ((isUnit_coneX i p.1).unit.inv_mul)
      rwa [map_mul, hu, mul_one, map_one] at this
    rw [hinv, one_mul]

theorem evalOne_ratioMap (i : (k : K) → ι k) (g : DehomRing i) : evalOne i (ratioMap i g) = g :=
  RingHom.congr_fun (evalOne_comp_ratioMap i) g

variable [DecidableEq K]

def segreDehom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Fin m) ℂ →ₐ[ℂ] DehomRing i :=
  aeval fun a => dehom i (∏ k, X ⟨k, σ a k⟩)

theorem segreDehom_chartSubst {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) : segreDehom σ i (chartSubst σ i f) = dehom i f := by
  have h : (segreDehom σ i).comp (chartSubst σ i) = dehom i := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, chartSubst_X, segreDehom, aeval_X, Equiv.apply_symm_apply, map_prod]
    rw [Finset.prod_eq_single p.1]
    · simp only [Function.update_self]
    · intro k _ hk
      rw [Function.update_of_ne hk, dehom_X_self]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact AlgHom.congr_fun h f

theorem segreDehom_surjective {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Function.Surjective (segreDehom σ i) := fun g => by
  obtain ⟨f, rfl⟩ := dehom_surjective i g
  exact ⟨chartSubst σ i f, segreDehom_chartSubst σ i f⟩

end Objects

end GroundTheory.Heights₂.Heights.Targets
