import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpecStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLawsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffInvariantOperatorAlongMatrixStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffEv

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem kappa_mul_pullM_mul_expS {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
    (K : Type) [CommRing K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O)
    (hh : MvPowerSeries.constantCoeff h = 0) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d)
    (hκ : IsKappa B K h w0 mu N κ) (g : PS V n d) :
    FB.toK K (κ * pullM B mu g) * FB.expS K ((N : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
        (FB.toK K g * FB.expS K (((1 : ℕ) : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0))) := by
  have hpt : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V :=
    fun b i => by rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b i]; exact Ideal.zero_mem _
  have h0 : ∀ (b : Fin n) (i : Fin d),
      MvPowerSeries.constantCoeff (matV B mu (fun j => pt V (n := n) d j) b i) = 0 :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n mu mu (fun j => pt V (n := n) d j) (fun j => pt V (n := n) d j) hpt hpt).2.2.2.2.2.1
  have hy : ∀ b : Fin n,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) := by
    intro b i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap V K) (matV B mu (fun j => pt V (n := n) d j) b i)) = 0
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  have hact : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (B.actK K w0) := by
    intro i
    unfold FB.actK
    rw [MvPowerSeries.constantCoeff_map, B.A.const w0 i, map_zero]
  have hL0 : MvPowerSeries.constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.pair_points_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_comp1 _ _ hact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0))) _ hh
  have hsm : ∀ (c : K) (f : PS K n d), MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (c • f) = 0 := by
    intro c f hf
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hS : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b)) _ hL0
  have hA : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n)
      ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (hy b)) _ hL0
  have hsub : MvPowerSeries.HasSubst
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h0 p.1 p.2
  have hpull : FB.toK K (pullM B mu g) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) (FB.toK K g) := by
    have hC := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin n × Fin d) (Fin n × Fin d)
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2)
      (fun p => by rw [h0]; exact Ideal.zero_mem _)).2.2.1 (fun p => h0 p.1 p.2)
    unfold pullM evV
    rw [hC]
    unfold FB.toK ev
    exact MvPowerSeries.map_subst hsub _
  have hevy : ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
      (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0) := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_sum hy]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_ev' _ _ hy (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b))]
    congr 1
    funext j
    fin_cases j
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.evP_pt _ hy b
  have hm : FB.toK K (κ * pullM B mu g) = FB.toK K κ * FB.toK K (pullM B mu g) :=
    map_mul (MvPowerSeries.map (algebraMap V K)) κ (pullM B mu g)
  have hk := hκ
  unfold IsKappa at hk
  have hAS := hsm (N : K) _ hS
  rw [Nat.cast_one, one_smul, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_mul _ hy, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_expS _ hy _ hS,
    hevy, ← hpull, hm, hk, _root_.mul_comm (FB.expS K _) (FB.toK K (pullM B mu g)), _root_.mul_assoc,
    ← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_expS_add _ _ (by rw [map_sub, hA, hAS, sub_zero]) hAS, sub_add_cancel]

theorem nabValN_kappa_mul_pullM : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O), MvPowerSeries.constantCoeff h = 0 → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d), IsKappa B K h w0 mu N κ → ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS V n d), nabValN B K h w0 N (FB.toK K (κ * pullM B mu g)) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B K h w0 1 (FB.toK K g) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ h w0 hh n mu N κ hκ Ty _ r σ u hu P g
  unfold nabValN
  rw [kappa_mul_pullM_mul_expS B K h w0 hh mu N κ hκ g]
  exact GlobalTheory.T.constantCoeff_invariant_operator_along_matrix V d O B K n mu Ty r σ u hu P _

end GlobalTheory.PlaceInt
