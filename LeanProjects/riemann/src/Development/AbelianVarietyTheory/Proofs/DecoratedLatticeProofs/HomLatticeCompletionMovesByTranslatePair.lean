import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatPairMove

variable {D : D7}

def finGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (EAf D) where
  val := (mt V g).map (toEAf D)
  inv := (mt V g⁻¹).map (toEAf D)
  val_inv := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  inv_val := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mul (V : HSp D) (g h : GA D V) :
    (finGL V (g * h)).val = (mt V g).map (toEAf D) * (finGL V h).val := by
  change (mt V (g * h)).map (toEAf D) = _
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]
  rfl

theorem latFr_rfl (V : HSp D) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    GlobalTheory.AdForm.latFr V rfl N = (N : Set (Fin V.rank → D.host.E)) := by
  ext x
  exact Iff.rfl

theorem eq_lat_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) : N = GlobalTheory.NormSum.AdLattice.lat (finGL V g) := by
  ext x
  rw [GlobalTheory.NormSum.AdLattice.mem_lat, hN x]
  rfl

theorem latO_move : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (g s : GA D S) (h s' : GA D T) N N' N₁ N₁', Moves S hS g N → Moves T hT h N' → Moves S hS (s * g) N₁ → Moves T hT (s' * h) N₁' → ∀ u : WO S T, u ∈ (latO S T (latFr S hS N₁) (latFr T hT N₁') fun _ => True) ↔ ∃ u₀ ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), u = actO S T s s' u₀ := by
  intro D S T a b hS hT g s h s' N N' N₁ N₁' hN hN' hN₁ hN₁' u
  subst hS hT
  rw [latFr_rfl, latFr_rfl, latFr_rfl, latFr_rfl]
  obtain rfl := eq_lat_of_moves S g N hN
  obtain rfl := eq_lat_of_moves T h N' hN'
  obtain rfl := eq_lat_of_moves S (s * g) N₁ hN₁
  obtain rfl := eq_lat_of_moves T (s' * h) N₁' hN₁'
  exact GlobalTheory.AdelicLatMove.mem_latO_iff_exists_actO D S T s s' _ _ _ _ (finGL S g) (finGL S (s * g)) (finGL T h)
    (finGL T (s' * h)) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _)
    (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.NormSum.AdLattice.lat_isLattice _) (GlobalTheory.NormSum.AdLattice.lat_isLattice _)
    (GlobalTheory.NormSum.AdLattice.lat_isLattice _) (GlobalTheory.NormSum.AdLattice.lat_isLattice _) (finGL_mul S s g)
    (finGL_mul T s' h) u

end GlobalTheory.LatPairMove
