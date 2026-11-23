import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.InertChar

open ValuativeRel

variable {F : Type} [Field F] [NumberField F]

theorem valued_eq_exp_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    Valued.v (x : v.adicCompletion F) = WithZero.exp (-Formalism.UG.ordL (x : v.adicCompletion F)) := by
  have h0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (_root_.map_ne_zero _).2 x.ne_zero
  rw [← WithZero.exp_log h0]
  congr 1
  unfold Formalism.UG.ordL
  rw [dif_neg h0, neg_neg]
  have key : ∀ (z : WithZero (Multiplicative ℤ)) (h : z ≠ 0), WithZero.log z = Multiplicative.toAdd (WithZero.unzero h) := by
    intro z h
    cases z with
    | zero => exact absurd rfl h
    | coe a => rfl
  exact key _ h0

theorem ord_eq_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.SmGL.ord (v.adicCompletion F) x = Formalism.UG.ordL (x : v.adicCompletion F) := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE := ValuativeRel.isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer (v.adicCompletion F))
  have hpu : valuation (v.adicCompletion F) p = uniformizer (v.adicCompletion F) := by
    refine le_antisymm (le_uniformizer_iff.2 (hE.lt_one_iff_lt_one.2 ?_)) ?_
    · rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    · have h1 : Valued.v y < 1 := hE.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      rw [← hy, hE.le_iff_le, hp]
      rcases eq_or_ne (Valued.v y) 0 with h0 | h0
      · rw [h0]; exact zero_le
      · rw [← WithZero.exp_log h0] at h1 ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
        rw [WithZero.exp_le_exp]; omega
  set P : (v.adicCompletion F)ˣ := Units.mk0 p hp0
  have hP1 : GlobalTheory.SmGL.ord (v.adicCompletion F) P = 1 := GlobalTheory.SmGL.ord_eq_one hpu
  set m := Formalism.UG.ordL (x : v.adicCompletion F)
  set U : (v.adicCompletion F)ˣ := x * P ^ (-m)
  have hU : Valued.v (U : v.adicCompletion F) = 1 := by
    simp only [U, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, P, Units.val_mk0, hp]
    rw [valued_eq_exp_ordL v x, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [m]
  have hU' : valuation (v.adicCompletion F) (U : v.adicCompletion F) = 1 := by
    apply le_antisymm
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
  have hU0 : GlobalTheory.SmGL.ord (v.adicCompletion F) U = 0 := GlobalTheory.SmGL.ord_eq_zero hU'
  let o : (v.adicCompletion F)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun z => .ofAdd (GlobalTheory.SmGL.ord (v.adicCompletion F) z)) fun a b => by
      rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
  have hx : x = U * P ^ m := by simp [U]
  have : o x = o U * o P ^ m := by rw [hx, map_mul, map_zpow]
  have e2 : GlobalTheory.SmGL.ord (v.adicCompletion F) x = GlobalTheory.SmGL.ord (v.adicCompletion F) U +
      m * GlobalTheory.SmGL.ord (v.adicCompletion F) P := by
    have := congrArg Multiplicative.toAdd this
    simpa [o, mul_comm] using this
  rw [e2, hU0, hP1]; ring

end GlobalTheory.BCT.InertChar

open GlobalTheory.BCT.InertChar in
theorem GlobalTheory.BCT.inertChar_muLocK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : Eˣ, ((μ.locK w k : ℂˣ) : ℂ) = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (k : E)) := by
  intro E _ _ _ μ e hμ w hw k
  have h := hμ.2.2.1 w hw
  show ((μ.loc w (atFin w k) : ℂˣ) : ℂ) = _
  rw [h, GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL]
  push_cast
  rfl
