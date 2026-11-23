import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename

set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol

namespace GlobalTheory.ChartTransN

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dofN_ev {m : ℕ} (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (V : Fin m → Pt k n d)
    (hV : ∀ j, GP (V j)) (g : PS k m d) :
    DofN F b u (ev V g) = ∑ c : Fin m, ∑ l : Fin d, ev V (pderiv k (c, l) g) * DofN F b u (V c l) := by
  unfold DofN
  simp only [pderiv_ev V hV]
  simp only [Finset.mul_sum (s := (Finset.univ : Finset (Fin m))), Finset.mul_sum (f := fun l => ev V _ * _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dofN_inCol_ne (F : Fin d → PS k 2 d) {b c : Fin n} (h : c ≠ b) (u : Fin d → k) (f : PS k 1 d) :
    DofN F b u (inCol c f) = 0 := by
  unfold DofN
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pderiv_inCol, if_neg h, mul_zero]

theorem dofN_eq_sum (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN F b u g = ∑ l, inCol b (Dof F u (X ((0 : Fin 1), l))) * pderiv k (b, l) g := by
  have hX : ∀ l, inCol b (X ((0 : Fin 1), l) : PS k 1 d) = X (b, l) := fun l => gt_ev_X _ (gp b) 0 l
  simp only [← dofN_inCol, hX]
  conv_lhs => unfold DofN
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  unfold DofN
  symm
  rw [Finset.sum_eq_single l]
  · rw [pderiv_X_self, mul_one]
  · intro j _ hj
    rw [pderiv_X_of_ne (fun h => hj (congrArg Prod.snd h).symm), mul_zero]
  · simp

theorem unit_right (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  conv_lhs => rw [← G.comm i]
  rw [gt_ev_ev' _ _ axis_GP (pair_points_zero_constant (gp_pt 1) (gp_pt 0)), eval_pair_points, evP_pt _ axis_GP,
    evP_pt _ axis_GP]
  exact G.unit i

theorem dofN_transF (G : FGLaw k d) (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (b : Fin n) (u : Fin d → k)
    (g : PS k n d) :
    DofN (transF G.F φ φi) b u (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
      ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (DofN G.F b ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hφ (gp_pt c)
  have hc : ∀ (c : Fin n) l, comp1 φ (pt k (n := n) d c) l = inCol c (φ l) := fun _ _ => rfl
  have hcol : ∀ f : PS k 1 d, ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (inCol b f) =
      inCol b (ev (n := 1) ![φ] f) := by
    intro f
    unfold inCol
    rw [gt_ev_ev' _ _ hΦ (gp b), gt_ev_ev' _ _ (gp b) (single_point_zero_constant hφ), vec1, vec1, evP_pt _ hΦ]
    rfl
  rw [dofN_ev _ _ _ _ hΦ, dofN_eq_sum G.F, ev_sum _ hΦ, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ hΦ, hcol, ← dof_transF G.F G.const (unit_right G) φ φi hinv, gt_ev_X _ (single_point_zero_constant hφ), hc,
      dofN_inCol, mul_comm]
    rfl
  · intro c _ hcb
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hc, dofN_inCol_ne _ hcb, mul_zero]
  · simp

theorem dpolyN_transF : ∀ (k : Type) [CommRing k] (d n : ℕ) (G : FGLaw k d) (φ φi : Pt k 1 d), IsInvPair φ φi → ∀ (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (g : PS k n d), DpolyN (transF G.F φ φi) cp u P (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) g) = ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) (DpolyN G.F cp (fun l => (dLin φ).mulVec (u l)) P g) := by
  intro k _ d n G φ φi hinv Ix _ cp u P g
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hinv.1 (gp_pt c)
  have hit : ∀ (b : Fin n) (v : Fin d → k) (r : ℕ) (g : PS k n d),
      (DofN (transF G.F φ φi) b v)^[r] (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) ((DofN G.F b ((dLin φ).mulVec v))^[r] g) := by
    intro b v r
    induction r with
    | zero => intro g; rfl
    | succ r ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dofN_transF G φ φi hinv, ih]
  have hmon : ∀ m : Ix →₀ ℕ,
      DmonN (transF G.F φ φi) cp u m (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c))
          (DmonN G.F cp (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonN
    induction (Finset.univ : Finset Ix).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyN
  rw [ev_sum _ hΦ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ hΦ, hmon]

end GlobalTheory.ChartTransN
