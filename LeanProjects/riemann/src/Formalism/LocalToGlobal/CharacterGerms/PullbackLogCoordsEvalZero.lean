import Formalism.LocalToGlobal.CharacterGerms.LogCoordOfDpull

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def exZero (Y : FBChart C V O dd) : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C :=
  fun q => if q.1 = 0 then un1 (Y.ex q.2) else 0

def ExpODESt (Y : FBChart C V O dd) : Prop :=
  ∀ i j : Fin dd, MvPowerSeries.pderiv C i (un1 (Y.ex j)) =
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j))

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

def Mu : WVO I → Fin dd → C := fun w i => (p w.1).u w.2.1 w.2.2 i

theorem expAll_eq (x : Fin dd) : expAll Y p x = MvPowerSeries.subst (linS (Mu Y p)) (un1 (Y.ex x)) := rfl

theorem cc_exZero (q : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (exZero Y q) = 0 := by
  unfold exZero
  split_ifs
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex q.2) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Y.ex_const _
  · exact map_zero _

theorem subst_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.subst a (0 : MvPowerSeries σ C) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (Formalism.L2.FormalSeriesBounds.VP.hs ha), map_zero]

theorem pderiv_rowOf {n : ℕ} (b b' : Fin n) (w : WVO I) (E : MvPowerSeries (WVO I) C) :
    MvPowerSeries.pderiv C (b, w) (rowOf b' E) = if b' = b then rowOf b (MvPowerSeries.pderiv C w E) else 0 := by
  unfold rowOf
  rw [Formalism.L2.FormalSeriesBounds.pderiv_subst (Formalism.L2.FormalSeriesBounds.VP.og (fun v => MvPowerSeries.constantCoeff_X _))]
  by_cases h : b' = b
  · subst h
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff, h]

theorem constantCoeff_two_points_zero {n : ℕ} (b : Fin n) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simp

theorem pullback_log_coords_eval_zero {n : ℕ} (b : Fin n) (G : PS C 2 dd) :
    pullN Y p (ev (n := n) ![pt C dd b, 0] G) =
      rowOf b (MvPowerSeries.subst (linS (Mu Y p)) (MvPowerSeries.subst (exZero Y) G)) := by
  have hl : ∀ w, MvPowerSeries.constantCoeff (linS (Mu Y p) w) = 0 :=
    fun w => (Formalism.L2.FormalSeriesBounds.ordGE_one_iff _).1 (Formalism.L2.FormalSeriesBounds.ordGE_linS _ w)
  have h1 : MvPowerSeries.HasSubst
      (fun q : Fin 2 × Fin dd => ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun q => constantCoeff_two_points_zero b q)
  have h2 : MvPowerSeries.HasSubst (fun q : Fin n × Fin dd => rowOf q.1 (expAll Y p q.2)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun q => cc_pullPt Y p q)
  have h3 : MvPowerSeries.HasSubst (exZero Y) := Formalism.L2.FormalSeriesBounds.VP.hs (cc_exZero Y)
  have h4 : MvPowerSeries.HasSubst (linS (Mu Y p)) := Formalism.L2.FormalSeriesBounds.VP.hs hl
  have h5 : MvPowerSeries.HasSubst
      (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun w => MvPowerSeries.constantCoeff_X _)
  have h6 : MvPowerSeries.HasSubst (fun q => MvPowerSeries.subst (linS (Mu Y p)) (exZero Y q)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun q => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero hl (cc_exZero Y q))
  unfold pullN ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  conv_rhs => unfold rowOf
  rw [MvPowerSeries.subst_comp_subst_apply h1 h2, MvPowerSeries.subst_comp_subst_apply h3 h4,
    MvPowerSeries.subst_comp_subst_apply h6 h5]
  congr 1
  funext q
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    rw [MvPowerSeries.subst_X h2]
    simp only [exZero, if_true]
    rw [← expAll_eq]
    rfl
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply]
    simp only [exZero, one_ne_zero, if_false]
    rw [subst_zero' (fun q => cc_pullPt Y p q), subst_zero' hl, subst_zero' (fun w => MvPowerSeries.constantCoeff_X _)]

theorem pderiv_pullN {n : ℕ} (b : Fin n) (w : WVO I) (F : PS C n dd) :
    MvPowerSeries.pderiv C (b, w) (pullN Y p F) =
      ∑ j : Fin dd, rowOf b (MvPowerSeries.pderiv C w (expAll Y p j)) *
        pullN Y p (MvPowerSeries.pderiv C (b, j) F) := by
  unfold pullN
  rw [Formalism.L2.FormalSeriesBounds.pderiv_subst (Formalism.L2.FormalSeriesBounds.VP.og (fun q => cc_pullPt Y p q))]
  simp only [pderiv_rowOf]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro a _ hab; simp [hab]
  · simp

end VP

theorem dpull_of_ode {Y : FBChart C V O dd} (p : ∀ o, PairData Y d (I o)) (hE : ExpODESt Y) : DPullSt Y p := by
  intro n b c F
  have hP : MvPowerSeries.HasSubst (fun q : Fin n × Fin dd => rowOf q.1 (expAll Y p q.2)) :=
    VP.hs (fun q => VP.cc_pullPt Y p q)
  have hR : MvPowerSeries.HasSubst
      (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) :=
    VP.hs (fun w => MvPowerSeries.constantCoeff_X _)
  have hpull : ∀ G : PS C n dd, pullN Y p G = MvPowerSeries.substAlgHom hP G := fun G => by
    rw [MvPowerSeries.coe_substAlgHom]; rfl
  have hrow : ∀ G : MvPowerSeries (WVO I) C, rowOf b G = MvPowerSeries.substAlgHom hR G := fun G => by
    rw [MvPowerSeries.coe_substAlgHom]; rfl
  have key : ∀ j : Fin dd, ∑ w : WVO I, c w • rowOf b (MvPowerSeries.pderiv C w (expAll Y p j)) =
      ∑ i : Fin dd, (∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i) •
        rowOf b (MvPowerSeries.subst (linS (VP.Mu Y p)) (MvPowerSeries.subst (exZero Y)
          (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j)))) := by
    intro j
    have e1 : ∀ w, MvPowerSeries.pderiv C w (expAll Y p j) = ∑ i : Fin dd, VP.Mu Y p w i •
        MvPowerSeries.subst (linS (VP.Mu Y p)) (MvPowerSeries.subst (exZero Y)
          (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j))) := by
      intro w
      rw [VP.expAll_eq, Formalism.L2.FormalSeriesBounds.pderiv_subst_linS]
      exact Finset.sum_congr rfl fun i _ => by rw [hE i j]
    simp only [e1, hrow, map_sum, map_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    rfl
  simp only [VP.pderiv_pullN]
  unfold DofN
  simp only [← MvPowerSeries.smul_eq_C_mul]
  rw [hpull, map_sum]
  simp only [map_mul, map_sum, map_smul]
  simp only [← hpull, VP.pullback_log_coords_eval_zero]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [← smul_mul_assoc, ← Finset.sum_mul]
  congr 1
  rw [key j]

theorem logCoord_of_ode {Y : FBChart C V O dd} (p : ∀ o, PairData Y d (I o)) (hE : ExpODESt Y) : LogCoordSt Y p := logCoord_of_dpull (dpull_of_ode p hE)

end Formalism.L2.FormalSeriesBounds
