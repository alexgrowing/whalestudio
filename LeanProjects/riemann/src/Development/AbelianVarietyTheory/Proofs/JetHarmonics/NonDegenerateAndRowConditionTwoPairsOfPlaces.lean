import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairData
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsPairDataStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerateStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NonDegPair

section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowLawSquare GlobalTheory.RowLawPair
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] {dd : ℕ}

theorem coeff_mvExp_of_van {τ : Type} {T : Set τ} {H : MvPowerSeries τ C} [CharZero C] (hH : Van T H)
    (ν : τ →₀ ℕ) (hν : ∀ w ∈ ν.support, w ∉ T) (t : τ) :
    coeff (ν + Finsupp.single t 1) (mvExp H) = coeff (ν + Finsupp.single t 1) H := by
  have h := GlobalTheory.RowLaw.AddCurve.van_pderiv_mvExp hH t ν hν
  rw [map_sub, coeff_pderiv, coeff_pderiv, ← sub_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (Nat.cast_add_one_ne_zero _)

theorem van_add {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f + g) :=
  fun ν hν => by rw [map_add, hf ν hν, hg ν hν, add_zero]

theorem van_sub {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f - g) :=
  fun ν hν => by rw [map_sub, hf ν hν, hg ν hν, sub_zero]

theorem zc_cvAt {V : VF C} {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) (s : Fin 2) :
    Zc fun j => cvAt (X s : MvPowerSeries (Fin 2) C) (γ j) := fun j =>
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (hγ j).1

def toOne (b : MvPowerSeries (Fin dd) C) : PS C 1 dd := subst (pt C dd (0 : Fin 1)) b

theorem sb_toOne {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (b : MvPowerSeries (Fin dd) C) :
    sb ![a] (toOne b) = subst a b := by
  unfold toOne sb
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (zc_pt 0)) (hasSubst_sb (zc1 ha))]
  congr 1
  funext i
  exact sb_pt (zc1 ha) 0 i

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

theorem van_h {n : ℕ} (j : Fin n) {b : Fin dd → PS C n dd} (hb : Zc b) :
    Van {s : Fin n × Fin dd | s.1 = j} (sb ![gp C (Fin dd) j, b] Y.h) := by
  classical
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} (fun s => zc2 (GlobalTheory.RowLawPair.zc_gp j) hb s.1 s.2) ?_ (h_axes Y 0)
  rintro ⟨s, x⟩ hs ν hν
  obtain rfl : s = 0 := hs
  show coeff ν (X (j, x) : PS C n dd) = 0
  rw [coeff_X, if_neg]
  rintro rfl
  exact hν (j, x) (by simp) rfl

theorem sb_gp_three (f : PS C 3 dd) : sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] f = f := by
  have e : (fun q : Fin 3 × Fin dd => ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] q.1 q.2) = X := by
    funext ⟨s, x⟩
    fin_cases s <;> rfl
  unfold sb
  rw [e, subst_self]
  rfl

theorem formalGroupCocycleLinearTerm_eq_chartLinear (u : Fin dd → C) : c2 (Y.raw p) u = Y.chartLinearTerm u := by
  have z := fun j : Fin 3 => GlobalTheory.RowLawPair.zc_gp (C := C) (dd := dd) j
  have hv : Van {s : Fin 3 × Fin dd | s.1 = 0}
      (sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1] Y.h + sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 2] Y.h -
        sb ![gp C (Fin dd) (0 : Fin 3), law Y (gp C (Fin dd) 1) (gp C (Fin dd) 2)] Y.h) :=
    van_sub (van_add (van_h Y 0 (z 1)) (van_h Y 0 (z 2))) (van_h Y 0 (zc_law Y (z 1) (z 2)))
  have e := exp_gauge_cocycle_second_variable Y (z 0) (z 1) (z 2)
  rw [sb_gp_three, ← mvExp_eq hv.const] at e
  funext μ
  unfold c2 FBChart.chartLinearTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [formalAdd_eq_law Y p (z 1) (z 2), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, ← e, coeff_mvExp_of_van hv]
  intro w hw
  classical
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw)
  exact Fin.succ_ne_zero _

theorem cob_eq (b : MvPowerSeries (Fin dd) C) : cob (Y.raw p) b =
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (toOne b) - ev (n := 2) ![pt C dd 0] (toOne b) -
      ev (n := 2) ![pt C dd 1] (toOne b) := by
  unfold cob
  rw [formalAdd_eq_law Y p (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1),
    ← sb_toOne (zc_law Y (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1)),
    ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 0), ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 1)]
  rfl

theorem nonDeg_raw (h : NDG Y) : NonDeg (Y.raw p) V := by
  rintro γ hγ hu hadd ⟨b, hb, hcob⟩
  refine h γ hγ hu (fun i μ h0 h1 => ?_) ⟨toOne b, intS_subst V (zc_pt 0) (fun _ => intS_X V _) hb, fun μ => ?_⟩
  · have e := hadd i μ h0 h1
    rw [formalAdd_eq_law Y p (zc_cvAt hγ 0) (zc_cvAt hγ 1)] at e
    have e2 : (fun q : Fin 2 × Fin dd => cvAt (X q.1 : MvPowerSeries (Fin 2) C) (γ q.2)) =
        fun q : Fin 2 × Fin dd => ![fun j => cvAt (X 0 : MvPowerSeries (Fin 2) C) (γ j),
          fun j => cvAt (X 1 : MvPowerSeries (Fin 2) C) (γ j)] q.1 q.2 := by
      funext ⟨s, x⟩
      fin_cases s <;> rfl
    rw [e2]
    exact e
  · have e := hcob μ
    rwa [formalGroupCocycleLinearTerm_eq_chartLinear, cob_eq] at e

end

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem nonDegenerate_and_rowConditionTwo_pairsOfPlaces : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate :=
  ⟨fun _ _ _ _ _ _ _ _ Y _ _ _ _ p h => nonDeg_raw Y p h,
    fun C _ _ V O _ _ dd Y d _ I _ p h _ Hc =>
      GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate C V d I (Fin dd) (Y.raw p) (GlobalTheory.RowLawPair.rLaw_raw Y p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData C V O dd Y d I p)
        (nonDeg_raw Y p h) Hc⟩

end GlobalTheory.NonDegPair
