import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LFun

open GlobalTheory.Doubling GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ideleAt_eq_prod_locIdele {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) :
    ideleAt F E v x = ∏ w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset.attach,
      locIdele F w.1 (Units.map (toCompl ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2)).toMonoidHom x) := by
  classical
  have hc : ∀ u' : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u') (AlgHom.id F E)
      (finTens F E (ideleAt F E v x)) = (unitFin F E u' (ideleAt F E v x) : Fv F u' ⊗[F] E) := fun u' => by
    change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
    rw [← Algebra.TensorProduct.map_comp]
    rfl
  refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
  · rw [Units.coe_prod, map_prod]
    simp only [infTens_locIdele, Finset.prod_const_one]
    exact map_extUnit_zero (fstA F) _ _ (fun a => rfl) x
  · rw [Units.coe_prod, map_prod (finTens F E), map_prod (finAdEquiv F E)]
    simp only [finTens_locIdele]
    change _ = evalV E u (∏ w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset.attach, _)
    rw [map_prod]
    by_cases hu : u.under (𝓞 F) = v
    · rw [finAdEquiv_apply hu, hc, unitFin_ideleAt_self]
      have hm : u ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset :=
        (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 hu
      rw [Finset.prod_eq_single_of_mem ⟨u, hm⟩ (Finset.mem_attach _ _)]
      · exact (finSingle_self u _).symm
      · rintro b - hb
        exact finSingle_ne (fun e => hb (Subtype.ext e.symm)) _
    · rw [finAdEquiv_apply rfl, hc, unitFin_ideleAt_ne hu, Units.val_one, map_one]
      refine (Finset.prod_eq_one fun b _ => ?_).symm
      have hb : b.1.under (𝓞 F) = v := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 b.2
      exact finSingle_ne (fun e : u = b.1 => hu (by rw [e]; exact hb)) _

theorem charAt_eq_one_of_unrAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : (AF F ⊗[F] E)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 F)) (y : (Fv F v ⊗[F] E)ˣ)
    (hy : (y : Fv F v ⊗[F] E) ∈ intLoc F E v) (hy' : ((y⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v)
    (hμ : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt μ w) : charAt μ v y = 1 := by
  show μ (ideleAt F E v y) = 1
  rw [ideleAt_eq_prod_locIdele, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have h : w.1.under (𝓞 F) = v := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2
  have hu : Formalism.L2.Host.IsUnitAt w.1 (Units.map (toCompl h).toMonoidHom y) := by
    refine (EulerTie.isUnitAt_iff w.1 _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (InertChart.toCompl_mem h hy)
    · rw [← map_inv]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (InertChart.toCompl_mem h hy')
  have := hμ w.1 h _ hu
  exact Circle.ext (congrArg Units.val this)

end GlobalTheory.LFun

theorem GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (v : FinPl D) (y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → ((y⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → charAt μ v y = 1 := by
  intro D μ v y hy hy' hμ
  exact GlobalTheory.LFun.charAt_eq_one_of_unrAt μ v y hy hy' hμ
