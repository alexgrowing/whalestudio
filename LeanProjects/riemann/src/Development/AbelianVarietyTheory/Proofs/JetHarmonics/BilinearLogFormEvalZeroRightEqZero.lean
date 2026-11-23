import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeIntCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BilLActRight

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeIntCut
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart dLin)

namespace GlobalTheory.GaugeShift

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ ev_sub ev_zeroFam logOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix (bilL lg)
open GlobalTheory.TwistCheck (ev_bilL cc_log bilL_mixed balanced_iff)

variable {S : Type} [CommRing S] {d : ℕ}

theorem cz2 {n : ℕ} {a b : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    CZ (![a, b] : Fin 2 → Pt S n d) := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem coeff_mixed (g : PS S 2 d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) g =
      constantCoeff (pderiv S ((0 : Fin 2), i) (pderiv S ((1 : Fin 2), l) g)) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, coeff_pderiv, zero_add]
  simp

variable [Algebra ℚ S]

theorem ev_zero_log {n : ℕ} (G : FGLaw S d) (i : Fin d) : ev (n := n) ![0] (logOf G i) = 0 := by
  have e : (![0] : Fin 1 → Pt S n d) = fun _ _ => 0 := by
    funext j c; fin_cases j; rfl
  rw [e, ev_zeroFam, cc_log, map_zero]

theorem cz0 {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt S n d) i) = 0 := by simp

theorem bilinearLogForm_eval_zero_left_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![0, pt S d 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 cz0 (FBMap.cz_pt _))]
  simp [ev_zero_log]

theorem bilinearLogForm_eval_zero_right_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![pt S d 0, 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) cz0)]
  simp [ev_zero_log]

theorem bilL_add_left (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) + ev (n := 3) ![pt S d 1, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (FBMap.cz_pt _)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2c.formal_log_add_first_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_add_right (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![pt S d 0, G.add (pt S d 1) (pt S d 2)] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 1] (bilL G c) + ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (CIndFrFix2b.constantCoeff_add_second_third G)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2b.formal_log_add_last_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_swap (G : FGLaw S d) (c : Fin d → Fin d → S) (hs : ∀ i l, c i l = c l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (bilL G c) = bilL G c := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, bilL, lg, smul_eq_C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hs l i, mul_comm (ev _ _)]

theorem canon_sub_bilin : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ β : Matrix (Fin d) (Fin d) k, βᵀ = β → (∀ a : O, (dAct k B a)ᵀ * β = β * dAct k B (star a)) → ∃ h' : PS k 2 d, B.IsCanonGauge k h' ∧ bilinPart k h' = bilinPart k h - β := by
  intro R _ d O _ _ k _ _ _ B h hc β hs hb
  let G : FGLaw k d := FBMap.mapG (algebraMap R k) B.G
  let A : OAct O G := FBMap.mapA (algebraMap R k) B.A
  have hF : B.FK k = G.F := rfl
  have hA : ∀ a, B.actK k a = A.act a := fun _ => rfl
  have p {n : ℕ} (j : Fin n) := FBMap.cz_pt (R := k) (d := d) j
  have q (a : O) (j : Fin 2) := FBMap.cz_comp1 (A.act a) (A.const a) (pt k d j) (p j)
  refine ⟨h - bilL G β, ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩, ?_⟩
  · rw [ev_sub (cz2 cz0 (p _)), hc.ax0, bilinearLogForm_eval_zero_left_eq_zero G β, sub_zero]
  · rw [ev_sub (cz2 (p _) cz0), hc.ax1, bilinearLogForm_eval_zero_right_eq_zero G β, sub_zero]
  · rw [hc.ph1, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (p _)), bilL_add_left G β]
    congr 1; ring
  · rw [hc.ph2, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (p _) (CIndFrFix2b.constantCoeff_add_second_third G)), bilL_add_right G β]
    congr 1; ring
  · rw [hc.sy, ev_sub (cz2 (p _) (p _)), bilL_swap G β (fun i l => congrFun (congrFun hs l) i)]
    congr 1; ring
  · have hbal := (balanced_iff G A a (star a) β).1 (hb a)
    rw [hc.ad a, hA, hA, ev_sub (cz2 (q _ _) (p _)), ev_sub (cz2 (p _) (q _ _)), hbal]
    congr 1; ring
  · funext i l
    have := coeff_mixed (bilL G β) i l
    rw [bilL_mixed G β] at this
    simp only [bilinPart, map_sub, this, Matrix.sub_apply]

end GlobalTheory.GaugeShift
