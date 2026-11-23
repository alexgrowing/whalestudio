import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeVec
section Target
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem exists_typeVec_nonGalois_ne_zero : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (I : GlobalTheory.TypeRec.Ident (w.st Z).toD7) cp, GlobalTheory.TypeRec.IsComp I (repOf Y) cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g (w.st Z).toD7.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom (w.st Z).toD7 k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom (w.st Z).toD7.ntypes.e0 x = x := by
  intro _
  refine ⟨1, one_pos, ?_⟩
  intro eps C8 C5 c6 Cb _ _ _ _
  refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T _ _ _ _ _ w _ Z Wt hX z p0 Y _ _ _ _ _ I cp hcp σ
  exact typeVec_rows z.R z.F z.cG Y z.pins I cp hcp σ
end Target
end GlobalTheory.TypeVec
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGalois_typeVec_fixed_by_e0 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (I : GlobalTheory.TypeRec.Ident (w.st Z).toD7) cp, GlobalTheory.TypeRec.IsComp I (repOf Y) cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g (w.st Z).toD7.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom (w.st Z).toD7 k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom (w.st Z).toD7.ntypes.e0 x = x := by
  first | exact @_root_.GlobalTheory.TypeVec.exists_typeVec_nonGalois_ne_zero | exact _root_.GlobalTheory.TypeVec.exists_typeVec_nonGalois_ne_zero | (intros; apply _root_.GlobalTheory.TypeVec.exists_typeVec_nonGalois_ne_zero <;> assumption)
end
end
