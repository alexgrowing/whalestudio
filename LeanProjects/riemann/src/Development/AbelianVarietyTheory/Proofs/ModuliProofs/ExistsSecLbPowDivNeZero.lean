import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PowDominates

open LBGerm GlobalTheory.AbLaw GlobalTheory.TwistGen ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def chartPullTw (L N : LB X) (t : ℕ) : ChartPull (LB.div (lbPow L t) N) (tw (pw N (-1)) L (t : ℤ)) (𝟙 X) where
  idx p := (p.2, p.1 PUnit.unit)
  le _ _ hy := ⟨hy.2, mem_powChart.1 hy.1⟩
  g y p q hp hq := by
    refine (gm_div N (lbPow L t) (𝟙 X) y p q ⟨hp, hq⟩).trans (Eq.symm (Units.ext ?_))
    refine (gm_tw_g (pw N (-1)) L t y (p.2, p.1 PUnit.unit) (q.2, q.1 PUnit.unit)
      ⟨hp.2, mem_powChart.1 hp.1⟩ ⟨hq.2, mem_powChart.1 hq.1⟩).trans ?_
    rw [gm_lbPow_g t (𝟙 X) y p.1 q.1 hp.1 hq.1, ← Units.val_pow_eq_pow_val, ← Units.val_mul, _root_.mul_comm]
    refine congrArg Units.val (congrArg₂ (· * ·) rfl ?_)
    exact (map_zpow _ _ _).trans (zpow_neg_one _)

theorem exists_sec_div [CompactSpace X] [QuasiSeparatedSpace X] {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) {n : ℕ}
    (s : (lbPow L n).Sec) (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (t : ℕ) (u : (LB.div (lbPow L t) N).Sec), y ∈ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hN y
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := N.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hL s a
  obtain ⟨e, u, hu⟩ := exists_sec_of_le_chart (M := pw N (-1)) (isLB_pw hN (-1)) hL (n * m) (powSecFn σ)
    (fun z j j' hj hj' => by
      have hz : z ∈ L.U j ⊓ L.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨n * m * e, chartSec (chartPullTw L N _) u, ?_⟩
  rw [nonzeroLocus_chartSec_id (chartPullTw L N _) u fun z j hj =>
    ⟨((fun _ => j.2 : PUnit → L.ι), j.1),
      (⟨mem_powChart.2 hj.2, hj.1⟩ : z ∈ powChart L (fun _ => j.2) ⊓ N.U j.1)⟩]
  exact hu hya

theorem exists_f_ne_zero {M : LB X} (u : M.Sec) {y : X} (hy : y ∈ nonzeroLocus u) : ∃ j, u.f j ≠ 0 := by
  have hy' : y ∈ ⨆ k, X.basicOpen (u.f k) := hy
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
  refine ⟨k, fun h0 => ?_⟩
  rw [h0, Scheme.basicOpen_zero] at hk
  exact absurd hk (by simp)

end GlobalTheory.PowDominates

namespace GlobalTheory

open PowDominates

theorem exists_sec_lbPow_div_ne_zero : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left), N.IsLB → ∃ (n : ℕ) (s : (LB.div (lbPow P.L n) N).Sec), ∃ j, s.f j ≠ 0 := by
  intro h K _ _ P N hN
  obtain ⟨m, s, hc, hs⟩ := veryAmple_lbPow h.ample K P 4 le_rfl
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨_, _⟩ := TwistGen.compact_quasiSeparated (isLB_lbPow P.isLB 4) s hc fun i => (hs i).1
  obtain ⟨y⟩ : Nonempty P.A.left := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, Out.nonzeroLocus (s i) by rw [hc]; trivial)
  obtain ⟨t, u, hu⟩ := exists_sec_div P.isLB hN (s i) (hs i).1 y hi
  exact ⟨t, u, exists_f_ne_zero u hu⟩

end GlobalTheory
