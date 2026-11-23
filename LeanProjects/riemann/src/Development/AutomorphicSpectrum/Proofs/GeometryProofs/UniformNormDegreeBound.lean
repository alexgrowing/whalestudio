import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightCountStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightEstimateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsCuspLawsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace GlobalTheory.CompanionTheory.Ar.Plug.TopGrowth

theorem exists_intWeight_of_regDominant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : WZ E), Top.RegDominant (towerWt Dw a) → ∃ u : GlobalTheory.AllWt.Weight Dw, (∀ τ, StrictAnti (u τ)) ∧ reW u = towerWt Dw a ∧ WEq Dw a (GlobalTheory.AllWt.wtOf Dw u 0).1 := by
  intro E _ _ _ H Dw a ha
  classical
  let u : GlobalTheory.AllWt.Weight Dw := fun τ n =>
    if (n : ℕ) < Dw.p then a (τ.1, (n : ℕ)) else -a (conjEmb τ.1, Dw.p + Dw.q - 1 - (n : ℕ))
  have hre : reW u = towerWt Dw a := by
    funext τ n
    simp only [reW, towerWt, u]
    split_ifs <;> push_cast <;> rfl
  refine ⟨u, fun τ i j hij => ?_, hre, ?_⟩
  · have := ha τ i j hij
    rw [← hre] at this
    simpa [reW] using this
  · intro τ i hi
    by_cases h : τ (H.rt : E) = H.rt0
    · have hp : i < Dw.p := by simpa [Datum.mult, h] using hi
      simp [GlobalTheory.AllWt.wtOf, h, hp, u]
    · have hq : i < Dw.q := by simpa [Datum.mult, h] using hi
      have h' : conjEmb τ (H.rt : E) = H.rt0 := Small.conjEmb_rt_of_ne h
      have hidx : Dw.p + Dw.q - 1 - (Dw.p + (Dw.q - 1 - i)) = i := by omega
      have hnp : ¬ Dw.p + (Dw.q - 1 - i) < Dw.p := by omega
      simp [GlobalTheory.AllWt.wtOf, h, h', hq, u, hnp, hidx, GlobalTheory.AllWt.conjEmb_conjEmb]

theorem limsup_real_eq_of_growth : ∀ (D : ℕ) (r : ℕ → ℕ∞) (t : ℝ), 0 ≤ t → limsup (fun n : ℕ => (D.factorial : ENNReal) * (r n : ENNReal) / (n : ENNReal) ^ D) atTop = ENNReal.ofReal t → limsup (fun n : ℕ => (D.factorial : ℝ) * ((r n).toNat : ℝ) / (n : ℝ) ^ D) atTop = t := by
  intro D r t ht hlim
  have hb : ENNReal.ofReal t + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hev : ∀ᶠ n : ℕ in atTop, (D.factorial : ENNReal) * (r n : ENNReal) / (n : ENNReal) ^ D < ENNReal.ofReal t + 1 :=
    eventually_lt_of_limsup_lt (by rw [hlim]; exact ENNReal.lt_add_right ENNReal.ofReal_ne_top one_ne_zero)
  have heq : (fun n : ℕ => (D.factorial : ℝ) * ((r n).toNat : ℝ) / (n : ℝ) ^ D) =ᶠ[atTop]
      fun n : ℕ => ((D.factorial : ENNReal) * (r n : ENNReal) / (n : ENNReal) ^ D).toReal := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn h1
    have hfin : r n ≠ ⊤ := by
      intro hr
      have hD : (D.factorial : ENNReal) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero D
      have hpow : (n : ENNReal) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)
      rw [hr, ENat.toENNReal_top, ENNReal.mul_top hD, ENNReal.top_div_of_ne_top hpow] at hn
      exact absurd hn (not_lt.2 le_top)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hm]
    simp [ENNReal.toReal_div, ENNReal.toReal_mul]
  rw [limsup_congr heq, ENNReal.limsup_toReal_eq hb (hev.mono fun n hn => hn.le), hlim, ENNReal.toReal_ofReal ht]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem flagDeg_reW_eq [DecidableEq (CMType H)] : ∃ C : ℝ, ∀ u : GlobalTheory.AllWt.Weight Dw,
    Top.flagDeg (reW u) = C * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ) := by
  refine ⟨((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * ∏ _τ : CMType H, ∏ i : Fin (Dw.p + Dw.q),
    ∏ k : Fin (Dw.p + Dw.q), (if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1), fun u => ?_⟩
  have hv : ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ) = GlobalTheory.CompHt.vdm (fun τ i => (u τ i : ℝ)) := by
    simpa using GlobalTheory.CompHt.map_vdm (Int.castRingHom ℝ) u
  rw [(Top.flagDeg_eq_weyl _ _ (reW u)).1, mul_assoc, hv]
  congr 1
  unfold GlobalTheory.CompHt.vdm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : Finset.Ioi i = Finset.univ.filter (fun k : Fin (Dw.p + Dw.q) => i < k) := by ext b; simp
  rw [this, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · simp [reW, div_eq_mul_inv, mul_comm]
  · simp

theorem flagDeg_reW_mul [DecidableEq (CMType H)] (u v : GlobalTheory.AllWt.Weight Dw) :
    Top.flagDeg (reW u) * ((GlobalTheory.CompHt.vdm v : ℤ) : ℝ) = Top.flagDeg (reW v) * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ) := by
  obtain ⟨C, hC⟩ := flagDeg_reW_eq (Dw := Dw)
  rw [hC u, hC v]; ring

theorem regDominant_reW [DecidableEq (CMType H)] {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    Top.RegDominant (reW u) := fun τ a b hab => by
  simpa [reW] using (Int.cast_lt (R := ℝ)).2 (hu τ hab)

theorem vdm_inst (la : GlobalTheory.AllWt.Weight Dw) :
    @GlobalTheory.CompHt.vdm _ GlobalTheory.CompHt.fintypePsi _ ℤ _ la = GlobalTheory.CompHt.vdm la := by
  first | rfl | convert rfl | congr 1

theorem dimFlag_eq [DecidableEq (CMType H)] :
    GlobalTheory.CompHt.dimFlag Dw = Top.dimFl (CMType H) (Dw.p + Dw.q) := by
  simp only [GlobalTheory.CompHt.dimFlag, Formalism.DegreeFormula.dimFl, Top.dimFl]
  first | rfl | (congr 1; convert rfl) | convert rfl

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem volL_eq_of_growth [DecidableEq (CMType H)] {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hL : CompLaws U h e) (Z : Comp Xo c) (a : WZ E) (u : GlobalTheory.AllWt.Weight Dw)
    (hW : WEq Dw a (GlobalTheory.AllWt.wtOf Dw u 0).1) {t : ℝ} (ht : 0 ≤ t)
    (hg : GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal t) :
    volL U h a Z (Top.dimFl (CMType H) (Dw.p + Dw.q)) = t := by
  have hG0 : GlobalTheory.AllWt.wtOf Dw u 0 = ((GlobalTheory.AllWt.wtOf Dw u 0).1, 0) := Prod.ext rfl (by simp [GlobalTheory.AllWt.wtOf_snd])
  have hcusp : ∀ n : ℕ, cuspOn U h (n • a) Z = GlobalTheory.AllWt.cuspOn U Z (n • GlobalTheory.AllWt.wtOf Dw u 0) := by
    intro n
    have hWn : WEq Dw (n • a) (n • (GlobalTheory.AllWt.wtOf Dw u 0).1) := fun τ i hi => by simp [hW τ i hi]
    rw [(((GlobalTheory.T.lattice_sections_cusp_laws E H Dw l Xo c r U h e hL (n • a) 0).2 _ hWn).2.2.2.2.2 Z).1,
      (GlobalTheory.T.all_weight_sections_compat E H Dw l Xo c r U h e hL (n • (GlobalTheory.AllWt.wtOf Dw u 0).1) Z).2.2.1]
    conv_rhs => rw [hG0]
    rw [Prod.smul_mk, smul_zero]
  have hfun : (fun n : ℕ => ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) *
      (Module.finrank c.F (cuspOn U h (n • a) Z) : ℝ) / (n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q)) =
      fun n : ℕ => ((GlobalTheory.CompHt.dimFlag Dw).factorial : ℝ) *
      ((Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z (n • GlobalTheory.AllWt.wtOf Dw u 0)))).toNat : ℝ) /
        (n : ℝ) ^ GlobalTheory.CompHt.dimFlag Dw := by
    funext n; rw [hcusp n, ← dimFlag_eq]; simp [Module.finrank]
  show limsup _ atTop = t
  rw [hfun]
  exact limsup_real_eq_of_growth _ _ _ ht hg

end GlobalTheory.CompanionTheory.Ar.Plug.TopGrowth

namespace GlobalTheory.CompanionTheory.Ar.Plug

open TopGrowth in

theorem topGrowth : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → (∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal (GlobalTheory.CompHt.topDeg U Z u) ∧ GlobalTheory.CompHt.topDeg U Z u = T.vol (κ Z) * Top.flagDeg (reW u) ∧ 0 < GlobalTheory.CompHt.topDeg U Z u) ∧ (∀ Z, 0 < GlobalTheory.CompHt.vZero U Z) ∧ (T.VolEq → ∀ Z Z', GlobalTheory.CompHt.vZero U Z = GlobalTheory.CompHt.vZero U Z') ∧ ∀ (Z : Comp Xo c) (a : WZ E), Top.RegDominant (towerWt Dw a) → volL U h a Z (Top.dimFl (CMType H) (Dw.p + Dw.q)) = T.vol (κ Z) * Top.flagDeg (towerWt Dw a) := by
  intro hRR hG E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o κ II hC hF hP hT1
  have hgr : ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) →
      GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) :=
    fun Z u hu => le_antisymm
      (GlobalTheory.T.growthOn_le_vol_mul_flagDeg hRR hG E H Dw l Xo c r U h e hL x hx Y T o κ II hC hF hP hT1 Z u hu)
      (GlobalTheory.T.uniform_norm_height_count hRR hG E H Dw l Xo c r U h e hL x hx Y T o κ II hC hF hP hT1 Z u hu)
  have hfd : ∀ u : GlobalTheory.AllWt.Weight Dw, (∀ τ, StrictAnti (u τ)) → 0 < Top.flagDeg (reW u) :=
    fun u hu => (Top.flagDeg_eq_weyl _ _ _).2.1 (TopGrowth.regDominant_reW hu)
  have hvol : ∀ Z, 0 < T.vol (κ Z) := fun Z => hP.1 _
  have hs : ∀ τ, StrictAnti ((GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw) τ) :=
    fun τ => GlobalTheory.CompHt.strictAnti_stdWt τ
  have hvs : (0 : ℝ) < ((GlobalTheory.CompHt.vdm (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw) : ℤ) : ℝ) :=
    Int.cast_pos.2 (GlobalTheory.CompHt.vdm_pos hs)
  have hvZ : ∀ Z, GlobalTheory.CompHt.vZero U Z = T.vol (κ Z) *
      Top.flagDeg (reW (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw)) /
      ((GlobalTheory.CompHt.vdm (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw) : ℤ) : ℝ) := by
    intro Z
    rw [GlobalTheory.CompHt.vZero, hgr Z _ hs, ENNReal.toReal_ofReal (mul_pos (hvol Z) (hfd _ hs)).le, TopGrowth.vdm_inst]
  have htop : ∀ Z (u : GlobalTheory.AllWt.Weight Dw), GlobalTheory.CompHt.topDeg U Z u = T.vol (κ Z) * Top.flagDeg (reW u) := by
    intro Z u
    have hr := TopGrowth.flagDeg_reW_mul u (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw)
    rw [GlobalTheory.CompHt.topDeg, TopGrowth.vdm_inst, hvZ Z, div_mul_eq_mul_div, div_eq_iff hvs.ne']
    linear_combination (-(T.vol (κ Z))) * hr
  refine ⟨fun Z u hu => ⟨?_, htop Z u, ?_⟩, fun Z => ?_, fun hV Z Z' => ?_, fun Z a ha => ?_⟩
  · rw [hgr Z u hu, htop Z u]
  · rw [htop Z u]; exact mul_pos (hvol Z) (hfd u hu)
  · rw [hvZ Z]; exact div_pos (mul_pos (hvol Z) (hfd _ hs)) hvs
  · rw [hvZ Z, hvZ Z', hV (κ Z) (κ Z')]
  · obtain ⟨u, hu, hreW, hW⟩ := TopGrowth.exists_intWeight_of_regDominant E H Dw a ha
    have hgrowth := hgr Z u hu
    rw [hreW] at hgrowth
    exact TopGrowth.volL_eq_of_growth hL Z a u hW (mul_pos (hvol Z) ((Top.flagDeg_eq_weyl _ _ _).2.1 ha)).le hgrowth

end GlobalTheory.CompanionTheory.Ar.Plug
