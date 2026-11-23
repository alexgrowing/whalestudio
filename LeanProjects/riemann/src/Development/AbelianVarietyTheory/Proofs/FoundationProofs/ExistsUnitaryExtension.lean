import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.UnramHecke

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [div_mul_div_comm]

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

theorem phase_of_norm (z : ℂˣ) (h : ‖(z : ℂ)‖ = 1) : phase z = z := by
  ext; rw [phase_val, h]; simp

theorem exists_unitary_extension {A M : Type} [CommGroup A] [CommGroup M] (Φ : A →* M) (χ : A →* ℂˣ)
    (hk : ∀ a, Φ a = 1 → χ a = 1) (hu : ∀ a, ‖((χ a : ℂˣ) : ℂ)‖ = 1) :
    ∃ κ : M →* ℂˣ, (∀ x, κ (Φ x) = χ x) ∧ ∀ y, ‖((κ y : ℂˣ) : ℂ)‖ = 1 := by
  let _ : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  let _ : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift Φ)) (QuotientGroup.kerLift_injective Φ)
    (MonoidHom.toAdditive (QuotientGroup.lift Φ.ker χ fun a ha => hk a ha))
  refine ⟨phase.comp (MonoidHom.toAdditive.symm ρ), fun x => ?_, fun y => norm_phase _⟩
  have h : (MonoidHom.toAdditive.symm ρ) (Φ x) = χ x :=
    DFunLike.congr_fun hρ (Additive.ofMul (QuotientGroup.mk x))
  rw [MonoidHom.comp_apply, h, phase_of_norm _ (hu x)]

variable (D : D7)

theorem emb_conj (σ : D.host.E →+* ℂ) (z : D.host.E) : σ (D.host.conj z) = starRingEnd ℂ (σ z) :=
  D.host.conjE_apply σ z

theorem conj_conj (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem sgA_sgA (x : AE D) : sgA D (sgA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]

theorem sgU_sgU (x : (AE D)ˣ) : sgU D (sgU D x) = x := Units.ext (sgA_sgA D x)

theorem sgA_mem {x : AE D} (hx : x ∈ OhE D) : sgA D x ∈ OhE D :=
  Formalism.UG.P.csDual_sig_mem _ hx

def intUnits : Subgroup (AE D)ˣ where
  carrier := {u | IntU D u}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul]; exact mul_mem ha.1 hb.1,
    by rw [mul_inv, Units.val_mul]; exact mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem sgU_mem {u : (AE D)ˣ} (hu : u ∈ intUnits D) : sgU D u ∈ intUnits D :=
  ⟨sgA_mem D hu.1, by rw [← map_inv]; exact sgA_mem D hu.2⟩

def ratio : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / sgU D

theorem ratio_apply (x : (AE D)ˣ) : ratio D x = x / sgU D x := rfl

abbrev incU : D.host.Eˣ →* (AE D)ˣ := Units.map (inc D).toMonoidHom

def infChar (c : ℤ) : D.host.Eˣ →* ℂˣ :=
  ∏ τ : D.what₂.Tau, (zpowGroupHom (2 * c)).comp (phase.comp (Units.map (embT D τ).toMonoidHom))

theorem infChar_val (c : ℤ) (a : D.host.Eˣ) : ((infChar D c a : ℂˣ) : ℂ) =
    ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) := by
  simp [infChar, phase_val]

theorem norm_infChar (c : ℤ) (a : D.host.Eˣ) : ‖((infChar D c a : ℂˣ) : ℂ)‖ = 1 := by
  rw [infChar_val, norm_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (by simpa using h), one_zpow]

theorem ratio_eq_pm (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) :
    ∃ m : ℕ, 0 < m ∧ ((a : D.host.E) / D.host.conj a) ^ m = 1 := by
  have hc : D.host.conj (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  have hval : ((ratio D (incU D a) : (AE D)ˣ) : AE D) = inc D ((a : D.host.E) / D.host.conj a) := by
    have h1 : ((sgU D (incU D a) : (AE D)ˣ) : AE D) = inc D (D.host.conj a) :=
      Formalism.UG.P.csDual_sig_incl _ _
    rw [ratio_apply, div_eq_mul_inv, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, h1, ← map_mul,
      div_mul_cancel₀ _ hc]
    rfl
  have hint : IsIntegral ℤ ((a : D.host.E) / D.host.conj a) :=
    Formalism.UG.P.csGlob_int (F := ℚ) _ (by have := h.1; rw [hval] at this; exact this)
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint (fun φ => by
    rw [map_div₀, emb_conj, norm_div, Complex.norm_conj, div_self]
    simpa using a.ne_zero)
  exact ⟨n, hn, hpow⟩

theorem infChar_eq_one (c : ℤ) (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) : infChar D c a = 1 := by
  apply Units.ext
  rw [infChar_val, Units.val_one]
  have key : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) =
      embT D τ ((a : D.host.E) / D.host.conj a) ^ c := by
    intro τ
    have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    rw [zpow_mul, map_div₀, emb_conj, zpow_two, div_mul_div_comm, ← sq (‖_‖ : ℂ), ← Complex.mul_conj',
      mul_div_mul_left _ _ h]
  simp only [key]
  exact UpperTheory.Mu.prod_emb_zpow D.host D.eTau (ratio_eq_pm D a h) c

end GlobalTheory.NormSum.UnramHecke

open GlobalTheory.NormSum.UnramHecke in

theorem GlobalTheory.NormSum.exists_unramified_heckeU : ∀ (D : D7) (N : ℕ) (c : ℤ), Even N → ∃ χ : HeckeU D N, (∀ τ, χ.n τ = 2 * c) ∧ ∀ u, IntU D u → χ.f u = 1 := by
  intro D N c hN
  obtain ⟨κ, hκ, hnorm⟩ := exists_unitary_extension
    (((ratio D).comp (incU D)).coprod (intUnits D).subtype)
    ((infChar D c)⁻¹.comp (MonoidHom.fst _ _))
    (by
      rintro ⟨a, u⟩ h
      have h' : ratio D (incU D a) * (u : (AE D)ˣ) = 1 := h
      have hm : ratio D (incU D a) ∈ intUnits D := by
        rw [eq_inv_of_mul_eq_one_left h']; exact inv_mem u.2
      show (infChar D c a)⁻¹ = 1
      rw [infChar_eq_one D c a hm, inv_one])
    (by
      rintro ⟨a, u⟩
      show ‖(((infChar D c a)⁻¹ : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_inv_eq_inv_val, norm_inv, norm_infChar, inv_one])
  have hint : ∀ u, IntU D u → (κ.comp (ratio D)) u = 1 := by
    intro u hu
    have hm : ratio D u ∈ intUnits D := div_mem hu (sgU_mem D hu)
    have := hκ (1, ⟨_, hm⟩)
    simpa using this
  refine ⟨{ f := κ.comp (ratio D)
            n := fun _ => 2 * c
            unitary := fun x => hnorm _
            cont := ⟨1, one_pos, fun u hu _ => hint u hu⟩
            aut := fun a => ?_
            norm := fun x => ?_
            par := fun _ => (even_two_mul c).sub ((Int.even_coe_nat N).2 hN)
            unr := fun u hu _ => hint u hu }, fun _ => rfl, hint⟩
  · have h1 : κ (ratio D (incU D a)) = (infChar D c a)⁻¹ := by
      have := hκ (a, 1)
      simpa using this
    rw [← infChar_val, MonoidHom.comp_apply, h1, Units.inv_mul]
  · rw [MonoidHom.comp_apply, ratio_apply, map_mul (sgU D), sgU_sgU, mul_comm (sgU D x), div_self', map_one]
