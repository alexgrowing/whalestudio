import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSt

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Be

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem lg_pt (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hax : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hae : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply hae hax, hinv, PowerSeries.subst_X hax]

variable (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p])

theorem be_at (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {a b : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst ![C ep * g.lg a, C ep * g.lg b] (map i0 be) = g.be a b := by
  have hlg : ∀ {σ' : Type} {c : σ' → MvPowerSeries τ ℂ_[p]}, HasSubst c → ∀ i : σ',
      subst c (C ep * g.lg (X i)) = C ep * g.lg (c i) := by
    intro σ' c hc i
    have hXi : HasSubst (fun _ : Unit => (X i : MvPowerSeries σ' ℂ_[p])) :=
by
      have hz : ∀ _ : Unit, constantCoeff (X i : MvPowerSeries σ' ℂ_[p]) = 0 := fun _ => constantCoeff_X i
      first
        | exact hasSubst_of_constantCoeff_zero hz
        | exact HasSubst.of_constantCoeff_zero' hz
        | exact hasSubst_of_constantCoeff_nilpotent (fun j => by rw [hz j]; exact IsNilpotent.zero)
    rw [← smul_eq_C_mul, subst_smul hc, ← smul_eq_C_mul]
    congr 1
    unfold G1.lg PowerSeries.subst
    rw [subst_comp_subst_apply hXi hc]
    simp only [subst_X hc]
  have h0 : ∀ i : Fin 2, constantCoeff (![a, b] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hc : HasSubst ![a, b] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have hl0 : ∀ i : Fin 2, constantCoeff (g.lg (X i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ (cc_l g)
  have h1 : ∀ i : Fin 2, constantCoeff
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i) = 0 := by
    intro i; fin_cases i <;> simp [hl0]
  have hd : HasSubst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] := by
    first
      | exact hasSubst_of_constantCoeff_zero h1
      | exact HasSubst.of_constantCoeff_zero' h1
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h1 i]; exact IsNilpotent.zero)
  have h := congrArg (subst ![a, b]) be_tie
  rw [be_subst g hex hc (constantCoeff_X _) (constantCoeff_X _), subst_X hc, subst_X hc,
    subst_comp_subst_apply hd hc] at h
  have hfun : (fun i => subst ![a, b]
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i)) = ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hlg hc 0
    · exact hlg hc 1
  rw [hfun] at h
  simpa using h

def LogOf (x : MvPowerSeries τ (K0 p)) (a : MvPowerSeries τ ℂ_[p]) : Prop :=
  constantCoeff x = 0 ∧ constantCoeff a = 0 ∧
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 x) = C ep * g.lg a

theorem logOf_X (i : τ) : LogOf g i0 ep (X i) (X i) := by
  refine ⟨constantCoeff_X i, constantCoeff_X i, ?_⟩
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  rw [map_X, subst_X (hs_dg hc), dg_Cmul]

theorem logOf_add (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) : LogOf g i0 ep (x + y) (g.add a b) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hlb : constantCoeff (g.lg b) = 0 := PowerSeries.constantCoeff_subst_eq_zero hb0 _ (cc_l g)
  have hs : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add, hla, hlb, add_zero]
  refine ⟨by rw [map_add, hx0, hy0, add_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_add, subst_add (hs_dg hc), hx1, hy1, G1.add, lg_pt g hex hinv hs, mul_add]

theorem logOf_mul (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) (c : K0 p) {x : MvPowerSeries τ (K0 p)}
    {a : MvPowerSeries τ ℂ_[p]} (hx : LogOf g i0 ep x a) : LogOf g i0 ep (C c * x) (g.mulBy (i0 c) a) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hs : constantCoeff (C (i0 c) * g.lg a) = 0 := by rw [map_mul, hla, mul_zero]
  refine ⟨by rw [map_mul, hx0, mul_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_mul, map_C, ← smul_eq_C_mul, subst_smul (hs_dg hc), hx1, G1.mulBy, lg_pt g hex hinv hs,
      smul_eq_C_mul]
    ring

theorem subtraction_formal_group_log (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) :
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 (sub2 p be x y)) = g.be a b := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have h0' : ∀ i : Fin 2, constantCoeff (map i0 (![x, y] i)) = 0 := by
    intro i; rw [constantCoeff_map, h0 i, map_zero]
  have hs' : HasSubst (fun i : Fin 2 => map i0 (![x, y] i)) := by
    first
      | exact hasSubst_of_constantCoeff_zero h0'
      | exact HasSubst.of_constantCoeff_zero' h0'
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0' i]; exact IsNilpotent.zero)
  unfold sub2
  rw [map_subst hs, subst_comp_subst_apply hs' (hs_dg hc)]
  have hfun : (fun i : Fin 2 => subst (diagS (PowerSeries.C ep * g.l)) (map i0 (![x, y] i))) =
      ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hx1
    · exact hy1
  rw [hfun]
  exact be_at g i0 be ep hex be_tie ha0 hb0

theorem constantCoeff_sub2_eq_zero (hbe : constantCoeff be = 0) {x y : MvPowerSeries τ (K0 p)} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : constantCoeff (sub2 p be x y) = 0 := by
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact Formalism.G.LogP.hs2 hx hy
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  unfold sub2
  first
    | exact constantCoeff_subst_eq_zero hs h0 hbe
    | exact constantCoeff_subst_eq_zero h0 hbe
    | exact MvPowerSeries.constantCoeff_subst_eq_zero hs h0 hbe

end Be

end Formalism.MainNotions.J
