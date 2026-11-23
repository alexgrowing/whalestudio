import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelsOfDepthZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspaceStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InfinitesimalCharacterReference
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodFirst

set_option maxHeartbeats 2000000 in

theorem goodFTAll_stA (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (a : StA hL D cf rep) (hlab : GlobalTheory.CoefDuty.OPinModel.LabFixed D)
    (hloc : ∀ (I : GlobalTheory.TypeRec.Ident D) cp, GlobalTheory.TypeRec.IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) : GoodFTAll D := by
  refine GlobalTheory.T.labels_of_depth_zero hG hZ hL D a.A.wdT a.A.row rep
    (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) a.row a.depth hlab
    (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (D.host.g k) ⟨D.host.g_prime k⟩) ?_ hloc
  intro I rc hrc k v
  refine GlobalTheory.TameRecord.tameParam_record hDZ hL D a.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) k v (a.A.grp.kv k v) ?_
  rw [← a.zeta k]
  exact a.A.grp.tg_tame k v

set_option maxHeartbeats 2000000 in

theorem goodFTAll_allSt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => LA hL x → GoodFTAll (Dof x) := by
  intro hP hL
  have h := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (GlobalTheory.T.conjugate_vector_in_subspace hP)
  refine EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp fo tr w s P x l => ?_
  have hloc := H kp fo tr w s P x
  have ty : TypesTrue (Dof x).ntypes (Fr.at (w.st x.o.Z) f).P (Fr.at (w.st x.o.Z) f).W := x.fits.grp
  exact goodFTAll_stA hP.green hP.zel hP.dz hL (Dof x) (cfOf x) (repOf x.r.Y) l.a
    (GlobalTheory.CoefDuty.OPinModel.labFixed_of_typesTrue ty) hloc

end GlobalTheory.GoodFirst
