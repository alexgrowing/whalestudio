import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pTrRho_of :
    UpperTheory.Gal.CertificateRingHomMap.TrRho := by
  intro E _ _ _ n W g
  set e := GlobalTheory.BCT.TrKer.wspEquivVV W
  set F : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] GlobalTheory.BCT.TrKer.Wsp W :=
    PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v)) with hF
  have hcomp : Formalism.L2.DIV.rhoK W g ∘ₗ (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) =
      (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) ∘ₗ F := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext (fun u => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hF, PiTensorProduct.map_tprod]
    show Formalism.L2.DIV.rhoK W g (GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ u)) =
      GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ _)
    rw [GlobalTheory.BCT.TrKer.wspToVV_tprod, GlobalTheory.BCT.TrKer.wspToVV_tprod, rhoK_tenMul]
  have hconj : Formalism.L2.DIV.rhoK W g = e.conj F := by
    rw [LinearEquiv.conj_apply, ← hcomp]
    refine LinearMap.ext (fun x => ?_)
    simp
  rw [hconj, LinearMap.trace_conj', hF, GlobalTheory.BCT.TrKer.trace_piMap]
