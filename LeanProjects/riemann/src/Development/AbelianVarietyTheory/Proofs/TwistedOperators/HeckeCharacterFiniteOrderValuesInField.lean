import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

namespace HeckeCharacterValueBounds
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.CharValues

open Formalism.L2.Host

section General

variable {E : Type} [Field E] [NumberField E]

theorem exp_lt_one (m : ℕ) : (WithZero.exp (-((m : ℤ) + 1)) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem valued_v_algebraMap_adicCompletion' (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a) = v.valuation E a := by
  first
    | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    | (rw [HeightOneSpectrum.algebraMap_adicCompletion]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a)

theorem locK_eq_of_level (χ : HChar E) {v : HeightOneSpectrum (𝓞 E)} {m : ℕ} (h : χ.LevelLe v m) (x y : Eˣ)
    (hxy : v.valuation E ((y : E) - x) ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : (x : E) ≠ 0 := x.ne_zero
  have hv0 : v.valuation E (x : E) ≠ 0 := ((v.valuation E).ne_zero_iff).mpr hx0

  have hd : ((y * x⁻¹ : Eˣ) : E) - 1 = ((y : E) - x) * (x : E)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ hx0]
  have hle : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) ≤ WithZero.exp (-((m : ℤ) + 1)) := by
    rw [hd, map_mul, map_inv₀]
    calc v.valuation E ((y : E) - x) * (v.valuation E (x : E))⁻¹
        ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E) * (v.valuation E (x : E))⁻¹ := by
          first | gcongr | exact mul_le_mul_right' hxy _
      _ = WithZero.exp (-((m : ℤ) + 1)) := by rw [mul_assoc, mul_inv_cancel₀ hv0, mul_one]
  have hlt : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) < v.valuation E 1 := by
    rw [map_one]
    exact lt_of_le_of_lt hle (exp_lt_one m)
  have hu : v.valuation E ((y * x⁻¹ : Eˣ) : E) = 1 := ((v.valuation E).map_eq_of_sub_lt hlt).trans (map_one _)

  have hA : IsUnitAt v (atFin v (y * x⁻¹)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E)) = 1
    rw [valued_v_algebraMap_adicCompletion']
    exact hu
  have hB : Valued.v (((atFin v (y * x⁻¹) : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) ≤
      WithZero.exp (-(m : ℤ)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E) - 1) ≤ _
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, valued_v_algebraMap_adicCompletion']
    exact le_trans hle (WithZero.exp_le_exp.mpr (by omega))
  have h1 : χ.locK v (y * x⁻¹) = 1 := h _ hA hB
  calc χ.locK v y = χ.locK v (y * x⁻¹ * x) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = χ.locK v x := by rw [map_mul, h1, one_mul]

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 E))) (t : HeightOneSpectrum (𝓞 E) → 𝓞 E) (m : HeightOneSpectrum (𝓞 E) → ℕ)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 E, ∀ v ∈ S,
      v.valuation E ((y : E) - (t v : E)) ≤ WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E (t v : E) := by
  classical

  have hk : ∀ v : HeightOneSpectrum (𝓞 E),
      WithZero.exp (WithZero.log (v.intValuation (t v))) = v.intValuation (t v) :=
    fun v => WithZero.exp_log (v.intValuation_ne_zero _ (ht v))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v))).toNat)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem (y - t v) _).mpr (hy v hv)
  have h2 : v.valuation E ((y : E) - (t v : E)) = v.intValuation (y - t v) := by
    have h := v.valuation_of_algebraMap (K := E) (y - t v)
    first
      | (push_cast at h; exact h)
      | exact h
      | simpa using h
  have h3 : v.valuation E (t v : E) = v.intValuation (t v) := v.valuation_of_algebraMap (K := E) (t v)
  rw [h2, h3, ← hk v, ← WithZero.exp_add]
  refine le_trans h1 (WithZero.exp_le_exp.mpr ?_)
  have := Int.self_le_toNat ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v)))
  omega

private theorem exp_neg_succ_mul_lt_self (m : ℕ) {b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) :
    WithZero.exp (-((m : ℤ) + 1)) * b < b := by
  rw [← WithZero.exp_log hb, ← WithZero.exp_add, WithZero.exp_lt_exp]
  omega

theorem locK_mem (χ : HChar E) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 E)) (x : Eˣ) : χ.locK P x ∈ G := by
  classical
  choose m hm using GlobalTheory.Mem.UnrAe.exists_levelLe χ

  have key : ∀ a : 𝓞 E, a ≠ 0 → ∀ k : Eˣ, (k : E) = (a : E) → χ.locK P k ∈ G := by
    intro a ha k hk

    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1) m
      (fun v => by by_cases h : v = P <;> simp [h, ha])
    have hyP : P.valuation E ((y : E) - (a : E)) ≤ WithZero.exp (-((m P : ℤ) + 1)) * P.valuation E (a : E) := by
      simpa using hy P (Finset.mem_insert_self P T)
    have hva : P.valuation E (a : E) ≠ 0 := by
      rw [(P.valuation E).ne_zero_iff]
      intro h0
      exact ha (RingOfIntegers.ext (by rw [h0]; rfl))
    have hy0 : (y : E) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hyP
      exact absurd hyP (not_le.mpr (exp_neg_succ_mul_lt_self (m P) hva))
    set ky : Eˣ := Units.mk0 (y : E) hy0 with hky
    have hone : ∀ v ∈ insert P T, v ≠ P → χ.locK v ky = 1 := by
      intro v hv hvP
      have h1 : v.valuation E ((ky : E) - ((1 : Eˣ) : E)) ≤
          WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E ((1 : Eˣ) : E) := by
        simpa [hvP, hky] using hy v hv
      rw [locK_eq_of_level χ (hm v) 1 ky h1, map_one]
    have hPk : χ.locK P ky = χ.locK P k := by
      apply locK_eq_of_level χ (hm P) k ky
      simpa [hky, hk] using hyP

    have hS : ∀ v, v ∉ insert P T → χ.UnrAt v := fun v hv => hunr v (fun h => hv (Finset.mem_insert_of_mem h))
    have hPR := GlobalTheory.TypeValues.productRule χ (insert P T) hS ky
    rw [Finset.prod_eq_single_of_mem P (Finset.mem_insert_self P T) hone] at hPR
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P T), χ.val v ^ ordF v ky) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 := G.one_mem
    rw [← hPR] at h1
    rw [← hPk]
    exact (G.mul_mem_cancel_left (hinf ky)).mp ((G.mul_mem_cancel_right hF).mp h1)

  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 E) (x : E)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact x.ne_zero hab.symm
  have haE : algebraMap (𝓞 E) E a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  have hx : x = Units.mk0 _ haE * (Units.mk0 _ hbE)⁻¹ := by
    ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, div_eq_mul_inv]
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0 _ rfl) (G.inv_mem (key b hb0 _ rfl))

end General

theorem main : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ hc hn ho hv x
  classical
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  have hunr : ∀ v, v ∉ hfin.toFinset → χ.UnrAt v := fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)
  have hval : ∀ v, v ∉ hfin.toFinset → χ.val v ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := by
    intro v hv'
    obtain ⟨y, hy⟩ := hv v (hunr v hv')
    have hw : χ.valTw 0 v = ((χ.val v : ℂˣ) : ℂ) := by simp [HChar.valTw]
    exact RingHom.mem_fieldRange.mpr ⟨y, hy.trans hw⟩
  have hinf : ∀ k, χ.inf k ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := fun k => by
    rw [GlobalTheory.TypeValues.inf_eq_one χ hn ho k]
    exact Subgroup.one_mem _
  have hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ σ.fieldRange := fun P k =>
    locK_mem χ (GlobalTheory.TameVal.unitsIn σ.fieldRange) hfin.toFinset hunr hval hinf P k
  obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp (GlobalTheory.TwistValues.char_mem c χ hc hn ho σ.fieldRange hM x)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact Circle.coe_ne_zero _ hy.symm
  exact ⟨Units.mk0 y hy0, hy⟩

end GlobalTheory.CompanionTheory.CharValues

end

end

end HeckeCharacterValueBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ h₁ h₂ h₃ h₄ x
  exact HeckeCharacterValueBounds.GlobalTheory.CompanionTheory.CharValues.main D c χ n L σ h₁ h₂ h₃ h₄ x

end
