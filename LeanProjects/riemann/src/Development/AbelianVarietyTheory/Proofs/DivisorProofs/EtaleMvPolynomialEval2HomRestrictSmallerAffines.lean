import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EtaleRestrict

theorem etale_eval₂_res : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) (ι : Type) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → IsAffineOpen U' → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U) (hW'U' : W' ≤ q ⁻¹ᵁ U') (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).Etale := by
  intro X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  have h1 : (resG Y hW').Etale := GlobalTheory.TopForm.etale_resG hW hW'a hW'
  have h2 : ((resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ hN h1
  have h3 : (resG X hU').Etale := GlobalTheory.TopForm.etale_resG hU hU'a hU'
  have h4 : (MvPolynomial.map (σ := ι) (resG X hU')).Etale := by
    algebraize [resG X hU']
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := Γ(X, U)) (S := Γ(X, U'))
    exact RingHom.Etale.isStableUnderBaseChange Γ(X, U) Γ(X, U') (MvPolynomial ι Γ(X, U)) (MvPolynomial ι Γ(X, U')) h3
  have h5 : (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU')) = (resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE,
        ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    · intro i
      simp
  rw [← h5] at h2
  algebraize [MvPolynomial.map (σ := ι) (resG X hU'),
    MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a)),
    (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU'))]
  exact Algebra.Etale.of_restrictScalars (R := MvPolynomial ι Γ(X, U)) _ _

end GlobalTheory.EtaleRestrict
