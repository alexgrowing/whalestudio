import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G₀ : WTZ E}

theorem mul_idem_cusp {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * idem Z = f := by
  rw [mul_comm]; exact idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩

def mulEquiv (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀) where
  toFun f := ⟨(f : Rul Xo c) * s.sig, s.cusp_sig G hG f f.2⟩
  invFun g := ⟨(g : Rul Xo c) * s.inv, s.cusp_inv G hG g g.2⟩
  map_add' f f' := Subtype.ext (add_mul _ _ _)
  map_smul' a f := Subtype.ext (smul_mul_assoc a (f : Rul Xo c) s.sig)
  left_inv f := Subtype.ext (by
    show (f : Rul Xo c) * s.sig * s.inv = f
    rw [mul_assoc, s.mul_inv, mul_idem_cusp f.2])
  right_inv g := Subtype.ext (by
    show (g : Rul Xo c) * s.inv * s.sig = g
    rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_idem_cusp g.2])

theorem ereal_nonneg {a b : ℝ} {t : EReal} (ht : 0 ≤ t) (hab : 0 ≤ a + b) :
    0 ≤ ((a : ℝ) : EReal) + (t + ((b : ℝ) : EReal)) := by
  rw [add_comm t, ← add_assoc, ← EReal.coe_add]
  exact add_nonneg (EReal.coe_nonneg.2 hab) ht

theorem mem_latOn_of_mul (s : TwSec U x Z G₀) {G G' : WTZ E} (a : c.F) (ha : a ≠ 0)
    (hlo : ∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) (f : cuspOn U Z G) (hf : f ∈ latOn U Z G)
    (g : cuspOn U Z G') (hg : (g : Rul Xo c) = a • ((f : Rul Xo c) * s.sig)) : g ∈ latOn U Z G' := by
  refine (mem_supLat_iff (Z := Z) g.2.2).2 fun w v hv => ?_
  have hfv : 0 ≤ v (f : Rul Xo c) := ((mem_supLat_iff (Z := Z) f.2.2).1 hf) w v hv
  obtain ⟨b, hb, -, hlb, -⟩ := s.exists_val hv
  rw [hg, (isVal_valOn hv).smul _ _ ha, (isVal_valOn hv).mul, hb]
  exact ereal_nonneg hfv (by linarith [hlo w])

theorem mem_latOn_of_mul_inv (s : TwSec U x Z G₀) {G G' : WTZ E} (b : c.F) (hb : b ≠ 0)
    (hhi : ∀ w, s.hi w ≤ (vAdd w b : ℝ)) (g : cuspOn U Z G') (hg : g ∈ latOn U Z G')
    (f : cuspOn U Z G) (hf : (f : Rul Xo c) = b • ((g : Rul Xo c) * s.inv)) : f ∈ latOn U Z G := by
  refine (mem_supLat_iff (Z := Z) f.2.2).2 fun w v hv => ?_
  have hgv : 0 ≤ v (g : Rul Xo c) := ((mem_supLat_iff (Z := Z) g.2.2).1 hg) w v hv
  obtain ⟨β, -, hβ, -, hβh⟩ := s.exists_val hv
  rw [hf, (isVal_valOn hv).smul _ _ hb, (isVal_valOn hv).mul, hβ]
  exact ereal_nonneg hgv (by linarith [hhi w])

theorem twSec_mulEquiv_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG
  refine ⟨mulEquiv s G hG, fun _ => rfl, fun _ => rfl, fun a ha hlo f hf g hg => ?_, fun b hb hhi g hg f hf => ?_⟩
  · exact mem_latOn_of_mul s a ha hlo f hf g hg
  · exact mem_latOn_of_mul_inv s b hb hhi g hg f hf

end GlobalTheory.FlatTw.Mul
