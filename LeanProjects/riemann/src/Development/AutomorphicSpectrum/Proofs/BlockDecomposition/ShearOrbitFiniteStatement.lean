import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_orbit_box_finite_of_isSmooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ (v : V) (r : kˣ), valuation k (r : k) < 1 → ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | exact GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | (intros; apply GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite <;> assumption)
