import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXLeafPin

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ac_le (c Cl L : ℝ) (r k f : ℕ) (hCl : 1000 + |c| ≤ Cl) (hf : 2 ≤ f) (hL : 1 / 2 ≤ L) :
    max (c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) 0 ≤
      Cl * ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hn]
  have hn1 : (1 : ℝ) ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hrn : (r : ℝ) + 1 ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hCl0 : 0 ≤ Cl := by linarith [abs_nonneg c]
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (f : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hf' 5
    norm_num at this
    linarith
  have hP0 : 0 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) := by positivity
  have hn19 : 0 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := by positivity
  have hP : ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by
    have h1 : ((r : ℝ) + 1) ^ 2 ≤ (2 * (r : ℝ) + k + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hrn 2
    have h2 : (r : ℝ) * (2 * (r : ℝ) + k + 1) + 1 ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 2 := by
      linarith [mul_nonneg hr0 hk0, mul_nonneg hr0 hr0, mul_nonneg hk0 hk0]
    have h3 : (2 * (r : ℝ) + k + 1) ^ 4 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)
        ≤ (2 * (r : ℝ) + k + 1) ^ 2 * (2 * (2 * (r : ℝ) + k + 1) ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * (2 * (r : ℝ) + k + 1) ^ 4 := by ring
      _ ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by linarith
  have hA : 0 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 := mul_nonneg hCl0 hn19
  have hRHS : 8 * (Cl * (2 * (r : ℝ) + k + 1) ^ 19) ≤
      Cl * (2 * (r : ℝ) + k + 1) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
    have hfl : (32 : ℝ) * (1 / 2) ≤ (f : ℝ) ^ 5 * L := mul_le_mul hf5 hL (by norm_num) (by positivity)
    have := mul_le_mul_of_nonneg_left hfl hA
    linarith
  apply max_le
  · have hcP : c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) ≤
        |c| * (2 * (2 * (r : ℝ) + k + 1) ^ 19) :=
      (mul_le_mul_of_nonneg_right (le_abs_self c) hP0).trans
        (mul_le_mul_of_nonneg_left hP (abs_nonneg c))
    have hcl : |c| * (2 * (r : ℝ) + k + 1) ^ 19 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 :=
      mul_le_mul_of_nonneg_right (by linarith) hn19
    have e : c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) =
        c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) := by ring
    rw [e]
    linarith
  · linarith

def XPins : Prop :=
  ∀ (CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl : ℝ)
    (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
    (τ : D.what₂.Tau) (Cp Th' : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    u ≠ u' → 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl → 1801 ≤ D.R.k →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → PlaceTie T.X e →
    J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
      (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
    ∃ (θ : ℝ) (Ch : Choice T.X θ) (hB : WuBessel Ch) (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j))
      (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j)) (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)),
      HypTT D u u' ∧ 0 < Tr D u ∧ 0 < Tr D u' ∧
      (∀ j, GoodW D (e (plE D j)) u u' θ (locW Ch u u' (e (plE D j)))) ∧
      (∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j)))) ∧
      (∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1) ∧
      (∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) ∧ (∀ j, cOf hB u (e (plE D j)) ≠ 0)

end Formalism.L2.SG.Pf.CarrierXAll
