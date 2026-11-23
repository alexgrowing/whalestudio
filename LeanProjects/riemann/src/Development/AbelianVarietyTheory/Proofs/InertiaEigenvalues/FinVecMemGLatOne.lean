import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LatRatStd

variable {D : D7}

theorem finVec_mem_gLat_one (T : HSp D) (v : Fin T.rank → D.host.E) :
    Formalism.L2.Pj.finVec T v ∈ Formalism.L2.Pj.gLat T 1 ↔ v ∈ L0c D T := by
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.mem_coe]
  obtain ⟨h1, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D T
  rw [← ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E T.rank _ hfg hsp).1 v), ← h1]
  constructor
  · rintro ⟨z, hz, e⟩
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    exact hz
  · intro h
    exact ⟨_, h, by rw [map_one, Units.val_one, Matrix.one_mulVec]; rfl⟩

theorem mem_latRat_iff_cols {S T : HSp D} (hG : S.gram = 1) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)}
    (hS : LS = (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E))) (hT : LT = L0c D T)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ GlobalTheory.LatVac.latRat S T LS LT ↔ ∀ b, (fun a => M a b) ∈ Formalism.L2.Pj.latG T 1 := by
  subst hS hT
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = star (s j) := fun s j => by
    rw [hG, Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero]) (by simp),
      Matrix.one_apply_eq, mul_one]
  constructor
  · intro hM b
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 (SetLike.mem_coe.1 hs)) b trivial)
      obtain ⟨c', hc'⟩ := GlobalTheory.DatumFourier.star_int c
      have h1 : a • t ∈ Formalism.L2.Pj.latG T 1 :=
        Submodule.subset_span ⟨a, ha, t, (finVec_mem_gLat_one T t).2 ht, rfl⟩
      convert Submodule.smul_mem _ c' h1 using 1
      funext i
      change a * t i * _ = (c' : D.host.E) * (a * t i)
      rw [hg, hc', ← hc, mul_comm]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro h
    have key : ∀ b, ∀ v ∈ Formalism.L2.Pj.latG T 1, (Matrix.of fun a j => v a * (Pi.single b 1 : Fin S.rank → D.host.E) j) ∈
        GlobalTheory.LatVac.latRat S T (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E)) (L0c D T) := by
      intro b v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hv
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single b 1, ?_, t, (finVec_mem_gLat_one T t).1 ht, ?_⟩
        · rw [SetLike.mem_coe, Formalism.L2.Pj.stdLat, Submodule.mem_pi]
          intro k _
          rw [Pi.single_apply]
          split_ifs
          · exact Submodule.mem_one.2 ⟨1, map_one _⟩
          · exact zero_mem _
        · ext i j
          simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, hg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
          split_ifs <;> simp
      | zero => convert (GlobalTheory.LatVac.latRat S T _ _).zero_mem using 1; ext i j; simp
      | add x y _ _ hx hy => convert add_mem hx hy; ext i j; simp [add_mul]
      | smul c x _ hx =>
        convert GlobalTheory.LatVac.smul_mem_latRat c hx using 1
        exact Matrix.ext fun i j => mul_assoc (c : D.host.E) (x i) _
    have e : M = ∑ b, Matrix.of fun a j => M a b * (Pi.single b 1 : Fin S.rank → D.host.E) j := by
      ext i j
      simp [Matrix.sum_apply, Pi.single_apply]
    rw [e]
    exact sum_mem fun b _ => key b _ (h b)

end GlobalTheory.LatRatStd
