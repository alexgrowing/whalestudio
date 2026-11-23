import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScal
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwMulOne

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_eq_of_agree {Z : Comp Xo c} {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w)
    {f g : Rul Xo c}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) :
    v g = v f := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  show nval T.V e (evR Xo c g y.1) = nval T.V e (evR Xo c f y.1)
  rw [h _ y.1 hy.2]

theorem exists_latW_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c)
    (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G,
    ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG Z t w v hv f hf
  obtain ⟨f', hres, hlat⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z G f
  have hf'lat := hlat hf
  obtain ⟨a, ha0, hva, hpos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F t.lo t.finite_lo w
  obtain ⟨φ, hφ, -, hint, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ t G hG
  have hg := hint a ha0 hpos f' hf'lat (a • φ f') (by rw [Submodule.coe_smul])
  refine ⟨⟨(a • φ f' : cuspOn U Z (G + G₀)), cuspOn_le U Z (G + G₀) (a • φ f').2⟩, (mem_latOn U).1 hg, ?_⟩
  have hV := isVal_valOn hv
  obtain ⟨b, hb, -, -, hbhi⟩ := t.exists_val hv
  have e1 : v (f' : Rul Xo c) = v (f : Rul Xo c) := val_eq_of_agree hv (hres)
  show v ((a • φ f' : cuspOn U Z (G + G₀)) : Rul Xo c) ≤ _
  rw [Submodule.coe_smul, hV.smul _ _ ha0, hφ, hV.mul, e1, hb, hva]
  rw [← add_assoc, add_comm (((-(⌊t.lo w⌋ : ℝ) : ℝ)) : EReal) (v (f : Rul Xo c)), add_assoc, ← EReal.coe_add]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.TwMulOne
