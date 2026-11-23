import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ContinuousPderivDisc
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.DerivEndo

open GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem dof_endo (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ : Pt k 1 d) (hφ : GP φ)
    (hom : comp1 φ F = addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u (ev (n := 1) ![φ] g) = ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have key : ev (n := 2) ![F] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![F] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F := hom
    rw [this]
  rw [dof_eq _ hF hu, dof_eq F hF hu, key, ChartTrans.ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ChartTrans.ev_C_mul _ (single_point_zero_constant hφ)]
  simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dof_smul_dir (F : Fin d → PS k 2 d) (c : k) (u : Fin d → k) (g : PS k 1 d) :
    Dof F (c • u) g = C c * Dof F u g := by
  unfold Dof
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem iterate_dof_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (n : ℕ) (c : k) (g : PS k 1 d) :
    (Dof F u)^[n] (C c * g) = C c * (Dof F u)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul]

theorem dmonOf_endo (F : Fin d → PS k 2 d) (φ : Pt k 1 d) (hφ : GP φ) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (α : ι → k)
    (h : ∀ l g, Dof F (u l) (ev (n := 1) ![φ] g) = C (α l) * ev (n := 1) ![φ] (Dof F (u l) g))
    (m : ι →₀ ℕ) (g : PS k 1 d) :
    DmonOf F u m (ev (n := 1) ![φ] g) = C (∏ l, α l ^ m l) * ev (n := 1) ![φ] (DmonOf F u m g) := by
  have hit : ∀ (l : ι) (n : ℕ) (g : PS k 1 d), (Dof F (u l))^[n] (ev (n := 1) ![φ] g) =
      C (α l ^ n) * ev (n := 1) ![φ] ((Dof F (u l))^[n] g) := by
    intro l n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul, h, pow_succ,
        map_mul, mul_assoc]
  rw [← Finset.prod_map_toList]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, iterate_dof_C_mul, hit, List.map_cons, List.prod_cons,
      map_mul]
    ring

end GlobalTheory.DerivEndo

namespace GlobalTheory

open DerivEndo QuadDeriv

theorem invariantDeriv_along_endo : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (a : O), (∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) = ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g)) ∧ ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (m : ι →₀ ℕ) (g : PS k 1 d), constantCoeff (DmonOf (B.FK k) u m (ev (n := 1) ![B.actK k a] g)) = (∏ l, α l ^ m l) * constantCoeff (DmonOf (B.FK k) u m g) := by
  intro R _ d O _ _ k _ _ _ B a
  have hF : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const
  have hw : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k a) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k a) (pt k (n := 2) d 0))
      (comp1 (B.actK k a) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom a)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const a) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const a) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have h1 : ∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) =
      ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g) :=
    dof_endo (B.FK k) hF (congrFun hU) (B.actK k a) hw hom
  refine ⟨h1, fun ι _ u α hα m g => ?_⟩
  rw [dmonOf_endo (B.FK k) (B.actK k a) hw u α (fun l g => by
    rw [h1, hα, dof_smul_dir, ChartTrans.ev_C_mul _ (single_point_zero_constant hw)]), map_mul, constantCoeff_C,
    constSt k d (B.actK k a) hw]

end GlobalTheory
