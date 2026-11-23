import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp

open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CompRestr

open GlobalTheory.FlatLine GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem idem_mem_sec (Z : Comp Xo c) : idem Z ∈ sec Xo c 0 0 := by
  rw [← secZ_nat]
  have : (fun i => (ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 i : ℤ)) = 0 := by
    funext i
    rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
  rw [this]
  exact idem_mem_secZ Z

theorem idem_mul_mem_cuspW {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (Z : Comp Xo c) {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U G) : idem Z * f ∈ cuspW Xo c U G := by
  rw [mem_cuspW] at hf ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · have := mul_mem_secZ (idem_mem_secZ Z) hf.1
    rwa [zero_add] at this
  · rw [AllWt.rdU_mul]
    refine IdemCusp.mul_mem_holSub (U σ).X (modelWt (U σ) G) (rdU (U σ) (idem Z)) (fun k => ?_) (hf.2 σ hσ)
    have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
    have hs := (hU σ hσ).2.2.2.2.1 0 0 hD (idem Z) (idem_mem_sec Z) k
    have h0 : laU (U σ) 0 0 k = 0 := by
      funext τ j
      simp [laU]
    rw [h0] at hs
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (AllWt.rdU_mul (U σ) (idem Z) (idem Z)) k
    rw [idem_mul_idem] at this
    exact this.symm

theorem exists_cuspOn_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (Z : Comp Xo c) (G : WTZ E) (f : cuspW Xo c U G), ∃ g : cuspOn U Z G, (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) ∧ (f ∈ latW U G → g ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U hU Z G f
  have hs : idem Z * (f : Rul Xo c) ∈ suppOn Z := by
    rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  refine ⟨⟨idem Z * (f : Rul Xo c), idem_mul_mem_cuspW hU Z f.2, hs⟩, fun S _ _ y hy => ?_, fun hf => ?_⟩
  · show evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c f y
    by_cases ht : Tested y
    · have e : evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c (idem Z) y * evR Xo c f y :=
        evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) f y
      rw [e, evR_idem hy ht, one_mul]
    · unfold evR evalAt
      rw [dif_neg ht, dif_neg ht]
  · refine (mem_supLat_iff (Z := Z) hs).2 fun la v hv => ?_
    show 0 ≤ v (idem Z * (f : Rul Xo c))
    rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
    exact hf la v (valOn_subset Z la hv)

end GlobalTheory.CompRestr
