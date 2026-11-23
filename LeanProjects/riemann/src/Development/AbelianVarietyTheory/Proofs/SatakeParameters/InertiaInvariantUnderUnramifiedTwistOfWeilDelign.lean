import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IneUnrTwist

open Formalism.MainNotions Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct

theorem wd_inePol_twist {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} (a χ : WD h) (h1 : χ.lpDim = 1)
    (hu : χ.unr) {s : G E Ω} (hs : s ∈ Ine (F := E) B) : (a.lpChar χ).inePol s = a.inePol s := by
  induction a using WD.ind with | hP n a => ?_
  induction χ using WD.ind with | hP m c => ?_
  rw [WD.lpDim_mk] at h1
  rw [WD.unr_mk] at hu
  rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs, WD.charPol_mk, WD.charPol_mk,
    WDRep.tensor_ρ, hu.2]
  let e : (Fin m → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simpa using h1)
  let E' := (TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) e).trans (TensorProduct.rid ℂ _)
  rw [← LinearEquiv.charpoly_conj E']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [E', LinearEquiv.conj_apply]

theorem main : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := fun D T w a χ h1 hu s hs => by
  rw [T.inePol w _ s hs, T.inePol w _ s hs, T.char w a χ h1]
  exact wd_inePol_twist _ _ ((T.dim w χ).trans h1) ((T.unr w χ).1 hu) hs

end GlobalTheory.IneUnrTwist
