import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap

noncomputable section

namespace Formalism.L2.G.Pend

open MvPowerSeries Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.J

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

theorem wToC_eq : (k0ToC p).comp (algebraMap (WW p) (K0 p)) = wToC p := RingHom.ext (witt_fraction_to_Cp_algebraMap p)

theorem coeff_one_l_ne (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) : PowerSeries.coeff 1 g.l ≠ 0 := by
  intro h
  have hE : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hd : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ g.l := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact cc_l g
    · exact h
  obtain ⟨m, hm⟩ := hd
  obtain ⟨e', he'⟩ := PowerSeries.X_dvd_iff.2 hex
  have h1 : PowerSeries.subst g.ex g.l = (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 * (e' ^ 2 * PowerSeries.subst g.ex m) := by
    rw [hm, PowerSeries.subst_mul hE, PowerSeries.subst_pow hE, PowerSeries.subst_X hE]
    nth_rewrite 1 [he']
    ring
  rw [hinv] at h1
  have h2 := congrArg (PowerSeries.coeff 1) h1
  rw [PowerSeries.coeff_one_X, PowerSeries.coeff_X_pow_mul'] at h2
  simp at h2

theorem ex_l (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) :
    PowerSeries.subst g.l g.ex = PowerSeries.X := by
  have hE : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hL : PowerSeries.HasSubst g.l := PowerSeries.HasSubst.of_constantCoeff_zero' (cc_l g)
  have hu : IsUnit (PowerSeries.coeff 1 g.l) := (coeff_one_l_ne g hex hinv).isUnit
  have hQ : PowerSeries.subst g.l (g.l.substInvOfIsUnit hu) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left g.l (cc_l g) hu
  have h1 : g.ex = g.l.substInvOfIsUnit hu := by
    calc g.ex = PowerSeries.subst g.ex (PowerSeries.X : PowerSeries ℂ_[p]) := (PowerSeries.subst_X hE).symm
      _ = PowerSeries.subst g.ex (PowerSeries.subst g.l (g.l.substInvOfIsUnit hu)) := by rw [hQ]
      _ = PowerSeries.subst (PowerSeries.subst g.ex g.l) (g.l.substInvOfIsUnit hu) :=
          PowerSeries.subst_comp_subst_apply hL hE _
      _ = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) (g.l.substInvOfIsUnit hu) := by rw [hinv]
      _ = g.l.substInvOfIsUnit hu := PowerSeries.X_subst _
  rw [h1]
  exact hQ

theorem pt_lg (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) : g.pt (g.lg a) = a := by
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (cc_l g))
    (PowerSeries.HasSubst.of_constantCoeff_zero ha), ex_l g hex hinv,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha)]

def LTIso : Prop :=
  ∃ (ep : (WW p)ˣ) (th : PowerSeries (WW p)), PowerSeries.constantCoeff th = 0 ∧ IsUnit (PowerSeries.coeff 1 th) ∧
    PowerSeries.subst (PowerSeries.map (wToC p) th) (PowerSeries.map (k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p)) =
      PowerSeries.C (wToC p (ep : WW p)) * g.l

variable {g}

def epOf (h : LTIso g) : (WW p)ˣ := h.choose

def thOf (h : LTIso g) : PowerSeries (WW p) := h.choose_spec.choose

theorem thOf_zero (h : LTIso g) : PowerSeries.constantCoeff (thOf h) = 0 := h.choose_spec.choose_spec.1

theorem thOf_unit (h : LTIso g) : IsUnit (PowerSeries.coeff 1 (thOf h)) := h.choose_spec.choose_spec.2.1

theorem thOf_log (h : LTIso g) :
    PowerSeries.subst (PowerSeries.map (wToC p) (thOf h)) (PowerSeries.map (k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p)) =
      PowerSeries.C (wToC p (epOf h : WW p)) * g.l := h.choose_spec.choose_spec.2.2

theorem wToC_unit_ne (u : (WW p)ˣ) : wToC p (u : WW p) ≠ 0 := (u.isUnit.map (wToC p)).ne_zero

variable (g)

def beC (ep : ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  g.be (g.pt (C ep⁻¹ * X (0 : Fin 2))) (g.pt (C ep⁻¹ * X (1 : Fin 2)))

theorem beC_tie (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {ep : ℂ_[p]} (hep : ep ≠ 0) :
    subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (beC g ep) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)) := by
  have hT : HasSubst (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] :
      Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    hs2 (by rw [map_mul, cc_lg g (by simp), mul_zero]) (by rw [map_mul, cc_lg g (by simp), mul_zero])
  have h0 : ∀ i : Fin 2, constantCoeff (C ep⁻¹ * X i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    intro i
    rw [map_mul, constantCoeff_X, mul_zero]
  have hc : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], C ep⁻¹ * (C ep * a) = a := by
    intro a
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hep, map_one, one_mul]
  unfold beC
  rw [be_subst g hex hT (cc_pt g hex (h0 0)) (cc_pt g hex (h0 1)), pt_subst g hT (h0 0), pt_subst g hT (h0 1),
    subst_mul hT, subst_mul hT, subst_C, subst_X hT, subst_X hT]
  show g.be (g.pt (C ep⁻¹ * (C ep * g.lg (X (0 : Fin 2))))) (g.pt (C ep⁻¹ * (C ep * g.lg (X (1 : Fin 2))))) = _
  rw [hc, hc, pt_lg g hex hinv (by simp), pt_lg g hex hinv (by simp)]

def BeRat (ep : ℂ_[p]) : Prop := ∃ b : MvPowerSeries (Fin 2) (K0 p), map (k0ToC p) b = beC g ep

def beOf (ep : ℂ_[p]) : MvPowerSeries (Fin 2) (K0 p) :=
  open Classical in if h : BeRat g ep then h.choose else 0

variable {g}

theorem map_beOf {ep : ℂ_[p]} (h : BeRat g ep) : map (k0ToC p) (beOf g ep) = beC g ep := by
  unfold beOf
  rw [dif_pos h]
  exact h.choose_spec

theorem be_tie (hOk : g.Ok) {ep : ℂ_[p]} (hep : ep ≠ 0) (h : BeRat g ep) :
    subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map (k0ToC p) (beOf g ep)) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)) := by
  rw [map_beOf h]
  exact beC_tie g hOk.2.2.1 hOk.2.2.2 hep

def beLT (h : LTIso g) : MvPowerSeries (Fin 2) (K0 p) := beOf g (wToC p (epOf h : WW p))

end Formalism.L2.G.Pend
