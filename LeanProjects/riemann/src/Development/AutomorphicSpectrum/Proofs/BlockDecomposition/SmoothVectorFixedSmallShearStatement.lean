import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_small_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ v : V, ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | exact GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | (intros; apply GlobalTheory.CompanionTheory.MirPair.shear_fix_vector <;> assumption)
