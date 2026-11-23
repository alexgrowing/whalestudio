import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.GaugeBiadd

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.LawLog
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

def famPt {n : ℕ} (x : Fin n → Fin d → MvPowerSeries σ C) : Fin n × Fin d → MvPowerSeries σ C :=
  fun q => x q.1 q.2

theorem hs_famPt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) :
    HasSubst (famPt x) :=
  hasSubst_of_constantCoeff_zero fun q => hx q.1 q.2

theorem constantCoeff_vecCons_pair_eq_zero {τ : Type} {x y : Fin d → MvPowerSeries τ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (j : Fin 2) (i : Fin d) :
    constantCoeff ((![x, y] : Fin 2 → Fin d → MvPowerSeries τ C) j i) = 0 := by
  fin_cases j
  exacts [hx i, hy i]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt C d j i) = 0 := by simp [pt]

theorem constantCoeff_germEvalPair_eq_zero {n : ℕ} {x y : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {f : PS C 2 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev ![x, y] f) = 0 :=
  constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero hx hy)) (fun q => constantCoeff_vecCons_pair_eq_zero hx hy q.1 q.2) hf

theorem cc_comp1 {n : ℕ} {x : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    {φ : Pt C 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin d) :
    constantCoeff (comp1 φ x i) = 0 := by
  have h : ∀ (j : Fin 1) i, constantCoeff ((![x] : Fin 1 → Pt C n d) j i) = 0 := fun j i => by
    fin_cases j; exact hx i
  exact constantCoeff_subst_eq_zero (hs_famPt h) (fun q => h q.1 q.2) (hφ i)

theorem subst_famPt_pt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (j : Fin n) : (fun i => (subst (famPt x) (pt C d j i) : MvPowerSeries σ C)) = x j :=
  funext fun i => subst_X (hs_famPt hx) _

theorem subst_pointFamily_germEvalPair {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    {a b : Pt C n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (f : PS C 2 d) :
    (subst (famPt x) (ev ![a, b] f) : MvPowerSeries σ C) =
      subst (famPt ![fun i => (subst (famPt x) (a i) : MvPowerSeries σ C), fun i => subst (famPt x) (b i)]) f := by
  refine (subst_comp_subst_apply (hs_famPt (constantCoeff_vecCons_pair_eq_zero ha hb)) (hs_famPt hx) f).trans ?_
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> rfl

theorem subst_famPt_comp1 {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (φ : Pt C 1 d) (j : Fin n) :
    (fun i => (subst (famPt x) (comp1 φ (pt C d j) i) : MvPowerSeries σ C)) =
      fun i => subst (fun q : Fin 1 × Fin d => x j q.2) (φ i) := by
  have h : ∀ (l : Fin 1) i, constantCoeff ((![pt C d j] : Fin 1 → Pt C n d) l i) = 0 := fun l i => by
    fin_cases l; exact cc_pt j i
  funext i
  refine (subst_comp_subst_apply (hs_famPt h) (hs_famPt hx) (φ i)).trans ?_
  congr 1
  funext ⟨l, e⟩
  fin_cases l
  exact subst_X (hs_famPt hx) _

theorem subst_elim_twoVars {x y : Fin d → MvPowerSeries σ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS C 2 d) :
    (subst (Sum.elim x y) (subst (twoVars C d) f) : MvPowerSeries σ C) = subst (famPt ![x, y]) f := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (i | i); exacts [hx i, hy i])
  rw [subst_comp_subst_apply hs_twoVars hs]
  congr 1
  funext ⟨j, i⟩
  rw [twoVars, subst_X hs]
  fin_cases j <;> simp [famPt]

theorem logUnit_subst [CharZero C] {v : AddValuation C (WithTop ℝ)} {n : ℕ}
    {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) (hI : ∀ j i, MvIsInt v (x j i))
    {U f : PS C n d} (hU : MvIsInt v U) (hf : constantCoeff f = 0) (e : U = FB.expS C f) :
    LogUnit v (subst (famPt x) f : MvPowerSeries σ C) := by
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt hx) (fun q => hx q.1 q.2) hf, ?_⟩
  have h := ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v hU (a := famPt x) (fun q => hI q.1 q.2) (fun q => hx q.1 q.2)
  rw [e] at h
  unfold FB.expS PowerSeries.subst at h
  rw [subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (hs_famPt hx)] at h
  exact h

end

theorem biadd_of_add_of_act : AddSt → ActSt → BiaddSt := by
  intro hAdd hAct C _ _ v d R _ _ O _ _ B hB h H σ _ w w' z hw hw' hz
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis H.ax0
  have hF : ∀ i, constantCoeff (B.FK C i) = 0 := GlobalTheory.GaugeBaseChange.gp_FK B
  have hA : ∀ a i, constantCoeff (B.actK C a i) = 0 := fun a => GlobalTheory.GaugeBaseChange.gp_actK B a
  have cw := cc_expPt (fglOf hB) hw.1
  have cw' := cc_expPt (fglOf hB) hw'.1
  have cz := cc_expPt (fglOf hB) hz.1
  have hadd : expPt (fglOf hB) (w + w') =
      fun i => subst (famPt ![expPt (fglOf hB) w, expPt (fglOf hB) w']) (B.FK C i) := by
    rw [(hAdd C v d (fglOf hB) σ).2.1 w w' hw.1 hw'.1]
    funext i
    exact subst_elim_twoVars cw cw' (B.FK C i)
  have cA : ∀ {n : ℕ} (j l : Fin n) i, constantCoeff (addOf (B.FK C) (pt C d j) (pt C d l) i) = 0 :=
    fun j l i => constantCoeff_germEvalPair_eq_zero (cc_pt j) (cc_pt l) (hF i)
  have sA : ∀ {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (_ : ∀ j i, constantCoeff (x j i) = 0) (j l : Fin n),
      (fun i => (subst (famPt x) (addOf (B.FK C) (pt C d j) (pt C d l) i) : MvPowerSeries σ C)) =
        fun i => subst (famPt ![x j, x l]) (B.FK C i) := fun hx j l => by
    funext i
    unfold addOf
    rw [subst_pointFamily_germEvalPair hx (cc_pt j) (cc_pt l), subst_famPt_pt hx, subst_famPt_pt hx]
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero cw cz)) (fun q => constantCoeff_vecCons_pair_eq_zero cw cz q.1 q.2) hc, ?_, ?_,
    fun a => ?_⟩
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) w, expPt (fglOf hB) w', expPt (fglOf hB) z] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cw i, cw' i, cz i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hw'.2 i, hz.2 i]) hB.2.2.1
      (by rw [map_sub, map_add, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cA _ _) (cc_pt _) hc]; simp) H.ph1
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cA _ _) (cc_pt _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) z, expPt (fglOf hB) w, expPt (fglOf hB) w'] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cz i, cw i, cw' i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hz.2 i, hw.2 i, hw'.2 i]) hB.2.2.2.1
      (by rw [map_sub, map_add, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cA _ _) hc]; simp) H.ph2
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cc_pt _) (cA _ _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx := constantCoeff_vecCons_pair_eq_zero cw cz
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hz.2 i]) (hB.2.2.2.2 a)
      (by rw [map_sub, constantCoeff_germEvalPair_eq_zero (cc_comp1 (cc_pt _) (hA _)) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_comp1 (cc_pt _) (hA _)) hc]; simp) (H.ad a)
    rw [subst_sub (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_comp1 (cc_pt _) (hA _)) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_comp1 (cc_pt _) (hA _)), subst_famPt_comp1 hx, subst_famPt_comp1 hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [(hAct C v d R O B hB σ a).1 w hw.1, (hAct C v d R O B hB σ (star a)).1 z hz.1]
    exact k

end GlobalTheory.IsoTriv.GaugeBiadd
