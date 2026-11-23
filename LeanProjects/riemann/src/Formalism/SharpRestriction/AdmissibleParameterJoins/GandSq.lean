import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem cc_l : PowerSeries.constantCoeff g.l = 0 := by
  unfold G1.l
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.TaylorLogMetric.flog, PowerSeries.coeff_mk, if_pos rfl]

private theorem cc_subst_lemma {R : Type} [CommRing R] {υ : Type} {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hs]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  rcases d with _ | d
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow (Nat.succ_ne_zero d), smul_zero]

private theorem comp_lemma_2 {υ ρ : Type} {R : Type} [CommRing R] {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {c : υ → MvPowerSeries ρ R} (hc : HasSubst c)
    (f : PowerSeries R) : subst c (PowerSeries.subst a f) = PowerSeries.subst (subst c a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hc]

theorem cc_lg {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) : constantCoeff (g.lg a) = 0 :=
  cc_subst_lemma ha (cc_l g)

theorem cc_pt (hex : PowerSeries.constantCoeff g.ex = 0) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) :
    constantCoeff (g.pt a) = 0 :=
  cc_subst_lemma ha hex

theorem lg_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.lg a) = g.lg (subst c a) :=
  comp_lemma_2 ha hc g.l

theorem pt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.pt a) = g.pt (subst c a) :=
  comp_lemma_2 ha hc g.ex

theorem phAt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.phAt a) = g.phAt (subst c a) :=
  comp_lemma_2 ha hc g.ph

theorem add_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.add a b) = g.add (subst c a) (subst c b) := by
  have h0 : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add, cc_lg g ha, cc_lg g hb, add_zero]
  show subst c (g.pt (g.lg a + g.lg b)) = g.pt (g.lg (subst c a) + g.lg (subst c b))
  rw [pt_subst g hc h0, ← coe_substAlgHom hc, map_add, coe_substAlgHom, lg_subst g hc ha, lg_subst g hc hb]

theorem cc_add (hex : PowerSeries.constantCoeff g.ex = 0) {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : constantCoeff (g.add a b) = 0 :=
  cc_pt g hex (by rw [map_add, cc_lg g ha, cc_lg g hb, add_zero])

theorem be_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.be a b) = g.be (subst c a) (subst c b) := by
  have hab := cc_add g hex ha hb
  show subst c (g.phAt (g.add a b) - g.phAt a - g.phAt b) =
    g.phAt (g.add (subst c a) (subst c b)) - g.phAt (subst c a) - g.phAt (subst c b)
  rw [← coe_substAlgHom hc, map_sub, map_sub, coe_substAlgHom, phAt_subst g hc hab, phAt_subst g hc ha,
    phAt_subst g hc hb, add_subst g hex hc ha hb]

theorem dg_Cmul (ep : ℂ_[p]) (i : σ) :
    (diagS (PowerSeries.C ep * g.l) i : MvPowerSeries σ ℂ_[p]) = C ep * g.lg (X i) := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries σ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
  unfold diagS G1.lg
  rw [← PowerSeries.smul_eq_C_mul, ← smul_eq_C_mul, ← PowerSeries.coe_substAlgHom hX, map_smul]

theorem cc_Cl (ep : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
  rw [map_mul, cc_l g, mul_zero]

end G1

section Lin

variable {Z E Kap : Type} {R : Type} [CommRing R]

def IsLin [Fintype Z] (f : MvPowerSeries Z R) : Prop :=
  f = ∑ z, C (coeff (Finsupp.single z 1) f) * X z

theorem isLin_sum [Fintype Z] {α : Type} (s : Finset α) (f : α → MvPowerSeries Z R) (h : ∀ a ∈ s, IsLin (f a)) :
    IsLin (∑ a ∈ s, f a) := by
  unfold IsLin at *
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl h

end Lin

end Formalism.MainNotions.J
