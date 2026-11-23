import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelsOfDepthZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupledStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodPin

set_option maxHeartbeats 2000000 in

theorem goodFTAll_pinned : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : NAt hL D cf nch tp), OPin a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hDZ hL D cf nch tp a hp hloc
  have h0 : GoodFTAll a.nt.D := by
    refine GlobalTheory.T.labels_of_depth_zero hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.row a.depth hp.lab
      (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) ?_ hloc
    intro I rc hrc k v
    refine GlobalTheory.T.tame_parameter_coupled hDZ hL a.nt.D a.nt.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) k v (a.nt.A.grp.kv k v) ?_
    rw [← hp.gen k]
    exact a.nt.A.grp.tg_tame k v
  have e : ∀ D', D' = withLoc a.nt.L → GoodFTAll D' := by
    rintro _ rfl
    exact h0
  exact e D a.nt.eq

end GlobalTheory.GoodPin
