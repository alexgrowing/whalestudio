import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.CombTw

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem wt_diff_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) :
    wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m = wtOf Dw (parWt Dw (-w₀)) 0 + m • (-wtOf Dw 0 1) := by
  ext x
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.fst_neg, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply]
    simp only [wtOf, parWt, Pi.zero_apply, Pi.neg_apply, Pi.add_apply, nsmul_eq_mul]
    split_ifs <;> ring
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_neg]
    simp only [wtOf, nsmul_eq_mul]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem exists_mul_inv_pow {Z : Comp Xo c} {G₀ G₁ : WTZ E} (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) (m : ℕ) :
    ∃ z : TwSec U x Z (G₀ + m • (-G₁)), z.lo = s.lo - (m : ℝ) • t.hi ∧ z.hi = s.hi - (m : ℝ) • t.lo := by
  induction m with
  | zero => exact ⟨s.copy (by simp), by simp [TwSec.copy], by simp [TwSec.copy]⟩
  | succ n ih =>
    obtain ⟨z, hlo, hhi⟩ := ih
    refine ⟨(z.mul t.symm).copy (by rw [succ_nsmul, add_assoc]), ?_, ?_⟩
    · show z.lo + -t.hi = _
      rw [hlo]; push_cast; rw [add_smul, one_smul]; abel
    · show z.hi + -t.lo = _
      rw [hhi]; push_cast; rw [add_smul, one_smul]; abel

theorem exists_twSec_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (B : Finset ℕ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (k : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : TwSec U x Z (wtOf Dw (parWt Dw (-w₀)) 0)) (t : TwSec U x Z (wtOf Dw 0 1)), s.hi = s.lo → IntOff B s.lo → IntOff B t.hi → (∀ w, t.hi w - t.lo w ≤ k w) → ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m), IntOff B z.lo ∧ ∀ w, z.hi w - z.lo w ≤ m * k w := by
  intro E _ _ _ H Dw l Xo c r U _ x B Z u w₀ m k s t hs hslo hthi hk
  obtain ⟨z, hlo, hhi⟩ := exists_mul_inv_pow s t m
  refine ⟨z.copy (wt_diff_eq Dw u w₀ m).symm, ?_, ?_⟩
  · show IntOff B z.lo
    rw [hlo]
    intro w hw
    obtain ⟨a, ha⟩ := hslo w hw
    obtain ⟨b, hb⟩ := hthi w hw
    exact ⟨a - m * b, by simp [ha, hb]⟩
  · intro w
    show z.hi w - z.lo w ≤ _
    rw [hhi, hlo]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hs]
    have := hk w
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

end GlobalTheory.CombTw
