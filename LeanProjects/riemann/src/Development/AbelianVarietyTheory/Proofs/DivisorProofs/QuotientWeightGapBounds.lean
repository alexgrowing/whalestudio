import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegreeStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.QuoShape

theorem antitone_of_adj {N : ℕ} (f : Fin N → ℤ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : a ≤ b := hab
  clear hab
  induction b, hab' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega))

theorem shape {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (n : ℕ)
    (hn : 4 * (W.T : ℤ) * n ≤ W.h0) :
    (∀ τ, Antitone (W.u1 τ)) ∧
    (∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b) ∧
    ∀ τ a, |(W.u1 τ a : ℝ)| ≤ W.b / 2 := by
  have hT : (4 : ℤ) ≤ W.T := by have := hH.h1; omega
  have bar : ∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b := by
    intro τ a b ha hb
    have h := ((GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b (by omega)).2.1 hb).2
    have h2 : (n : ℤ) ≤ W.u1 τ a - W.u1 τ b - 3 * N := le_of_mul_le_mul_left (hn.trans h) (by omega)
    have h3 := b.isLt
    omega
  refine ⟨fun τ => antitone_of_adj _ fun a b hab => ?_, bar, fun τ a => ?_⟩
  · by_cases hb : (b : ℕ) = W.p
    · have := bar τ a b (by omega) hb
      omega
    · have := (GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b hab).1 hb
      omega
  · have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hH hD τ a).1
    have h2 : 4 * |W.u1 τ a| ≤ |W.u τ a| + W.c0 + 4 * N :=
      (mul_le_mul_of_nonneg_right (by omega) (abs_nonneg _)).trans h1
    have h3 : 4 * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h2
    have h4 := hH.h5 τ a
    linarith

theorem ranks_le (D : D7) : 80 * D.R.f * D.R.r ^ 2 ≤ D.R.r * D.R.f ^ 2 * D.R.m ^ 2 * D.R.k * (D.R.f * D.R.r.choose 2) := by
  have hf := SizeTZ.two_le_f D
  have hr := SizeTZ.six_le_r D
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  generalize D.R.f = f at *
  generalize D.R.r = r at *
  generalize D.R.m = m at *
  generalize D.R.k = k at *
  have hc : r ≤ r.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left _ (by omega)
  calc 80 * f * r ^ 2 = r * 2 ^ 2 * 2 ^ 2 * 5 * (f * r) := by ring
    _ ≤ r * f ^ 2 * m ^ 2 * k * (f * r.choose 2) := by gcongr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem shape_at {PP : ℝ} (hPP : 1 ≤ PP) (hW : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m) (u1 : Psi p.T.Q.H → Fin ((dat p i).p + (dat p i).q) → ℤ)
    (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (dat p i).p + (dat p i).q = D.R.r ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p →
      (nCol (dat p i) : ℤ) + 1 ≤ u1 τ a - u1 τ b) ∧ ∀ τ a, |(u1 τ a : ℝ)| ≤ 2 * L.sc.b := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hW.hyp hi
  have hH1 := hH u1
  have hcol : (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 :=
    SizeTZ.nCol_le_of_pins p.fw.laws.pins ⟨Nat.le_add_left _ _, i.2⟩
  have hr : (80 : ℝ) * D.R.f * (D.R.r : ℝ) ^ 2 ≤
      D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) := by
    rw [hW.dim]; exact_mod_cast ranks_le D
  have hn : 4 * ((lenT p i PP : ℕ) : ℤ) * (nCol (dat p i) : ℕ) ≤ h0 := by
    have hT0 : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
    have h1 : 4 * (lenT p i PP : ℝ) * (nCol (dat p i) : ℝ) ≤ h0 := by
      refine le_trans ?_ hh
      generalize (lenT p i PP : ℝ) = T at *
      calc 4 * T * (nCol (dat p i) : ℝ) ≤ 4 * T * (20 * D.R.f * (D.R.r : ℝ) ^ 2) := by gcongr
        _ = 1 * (T * (80 * D.R.f * (D.R.r : ℝ) ^ 2)) := by ring
        _ ≤ PP * (T * (D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ))) := by gcongr
        _ = _ := by ring
    exact_mod_cast h1
  obtain ⟨a1, a2, a3⟩ := shape (wtsAt p i PP h0 S eta u1) hH1 ((quo_iff p i PP h0 S eta u1).1 hq) (nCol (dat p i)) hn
  have b1 : D.R.k - 1 < (dat p i).p := hH1.kc_lt
  have b2 : (dat p i).p < (dat p i).p + (dat p i).q := hH1.p_lt
  refine ⟨by omega, by omega, hW.sig.2.2, a1, a2, fun τ a => (a3 τ a).trans (le_of_eq ?_)⟩
  show 4 * L.sc.b / 2 = 2 * L.sc.b
  ring

theorem quo_shape : Size → Lifts fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (dat p i).p + (dat p i).q = (Fm.D x ι).R.r ∧ (∀ τ, Antitone (u1 τ)) ∧ (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (nCol (dat p i) : ℤ) + 1 ≤ u1 τ a - u1 τ b) ∧ (∀ τ a, |(u1 τ a : ℝ)| ≤ 2 * (Fm.L x ι).sc.b) ∧ Dom (aOf p i u1) (nCol (dat p i)) ∧ LastPos (dat p i) (aOf p i u1) ∧ GOf p i u1 = wtOf (dat p i) (u1 + parWt (dat p i) (shift (dat p i) u1 (nCol (dat p i)))) ((nCol (dat p i) / 2 : ℕ) : ℤ) := fun _ =>
  Formalism.MainNotions.Closed.imp GlobalTheory.T.weight_bound_holds fun Fm _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi u1 hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := shape_at p i
      ((one_le_pow₀ (SizeTZ.one_le_zBase _)).trans (SizeTZ.pow_le_PP (Fm.parT x hx ι))) (h x hx hle ι p hp i) hi u1 hq
    have hev : Even (nCol (dat p i)) := even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) eight_dvd_nCol)
    obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree _ _ (dat p i) u1 (nCol (dat p i)) _ a1 hev a4 a5 a6
    exact ⟨a1, a2, a3, a4, a5, a6, b1, b3, b2⟩⟩

end GlobalTheory.RefSum.QuoShape

end
