import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem nil_of_eq {W : Type} [AddCommGroup W] [Module ℂ W] (M : End ℂ W) {p p' : Polynomial ℂ} (e : p = p')
    (h : IsNilpotent (Polynomial.aeval M p)) : IsNilpotent (Polynomial.aeval M p') := e ▸ h

theorem UpperTheory.Gal.crystallineComparison.phiKNil_of :
    DvdOfNil → NilWeil → NilRho → WdModel → PhiKOfNil := by
  intro hD hW hR hM
  unfold PhiKOfNil
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hcr Q hN s u hu hQ
  obtain ⟨T⟩ := hT
  haveI := LL.2
  have hSst : IsSst P (Bw.repE LL r') := GlobalTheory.CrysSst.isSst_of_isCrys P AI T _ hcr
  have hV : IsPst P (Bw.repE LL r') := GlobalTheory.GalCut.IwaTwist.isPst_of_isSst P AI T _ hSst
  haveI := hV.finite
  have hd : deg (frob h)⁻¹ = -1 := by rw [deg_inv, deg_frob]
  have h1 := hW l P E Ω A w h O Bw hj LL _ (Bw.repE LL r') hV hSst Q hN _ hd
  have h2 := nil_of_eq _ hQ (hR l P ι E Ω A w h O Bw hj LL _ (Bw.repE LL r') hV Q _ h1)
  obtain ⟨h3, _⟩ := hM l P ι E Ω A w h O Bw hj a r LL r' hm hV (frob h)⁻¹
  obtain ⟨m, hm'⟩ := hD ℂ _ _ s u hu h2
  exact ⟨(frob h)⁻¹, hd, m, h3 ▸ hm'⟩
