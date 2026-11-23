import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerLocalEigenFrameStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open TopForm

theorem exists_logKS_div : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim) (D' : CartierDiv (X₀ TF.Y Z)) (r : K.bundle.ι → (X₀ TF.Y Z).functionFieldˣ), Presents D' K.bundle r → ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∀ D : CartierDiv (X₀ TF.Y Z), (∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)))) → ∃ h : (X₀ TF.Y Z).functionField, ∀ x : X₀ TF.Y Z, ∃ g g' : (X₀ TF.Y Z).functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧ RegAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ∧ (UnitAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hfn _ _ K D' r hr φ₀ f₀ hφ₀ D hD
  obtain ⟨D₀, hD₀⟩ := GlobalTheory.T.exists_logKodairaSpencer_genericEigenFrame E H Dw l Xo c TF Z hpq hfn φ₀ f₀ hφ₀
  obtain ⟨i₀, hi₀⟩ := exists_chart K.isLB (genericPoint (X₀ TF.Y Z))
  set T₀ := GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D₀ with hT₀
  refine ⟨(r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)), fun x => ?_⟩
  obtain ⟨φ, f, A, d, hφ, hd, hA, hDx⟩ := hD x
  obtain ⟨Dx, hDxKS, hloc⟩ := GlobalTheory.T.exists_logKodairaSpencer_local_eigenFrame E H Dw l Xo c TF Z hpq hfn x φ f hφ
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.logKodairaSpencer_wedge_frameChange E H Dw l Xo c TF Z hpq hfn _ _ D₀ Dx A d hD₀ hDxKS hA hd
  obtain ⟨i, hi⟩ := exists_chart K.isLB x
  refine ⟨_, r i, hDx, hr.isEqn i x hi, ?_⟩
  have hgi : genericPoint (X₀ TF.Y Z) ∈ K.bundle.U i := gen_mem hi
  have key : (r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)) =
      r i * T₀ (formOf _ hgi (K.om i)) := by
    have e1 := formOf_eq_ratio_smul hi₀ hgi (K.isFrame i₀) (K.isFrame i)
    have e2 := hr.isRatSec i₀ i (GlobalTheory.Cartier.memInf hi₀ hgi)
    rw [K.g_eq_ratio] at e2
    rw [e1, map_smul, smul_eq_mul, e2]
    ring
  have e : (r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)) *
      ((∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)) : (X₀ TF.Y Z).functionFieldˣ) :
        (X₀ TF.Y Z).functionField) / (r i : (X₀ TF.Y Z).functionField) =
      u * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) Dx (formOf _ hgi (K.om i)) := by
    rw [key, hu']
    have h1 : ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) :
        (X₀ TF.Y Z).functionField) * ((∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)) :
          (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]
      simp [← zpow_add]
    have h2 := (r i).ne_zero
    have h3 : ∀ (ri P Q a b : (X₀ TF.Y Z).functionField), ri ≠ 0 → P * Q = 1 →
        ri * (a * P * b) * Q / ri = a * b := fun ri P Q a b hri hPQ => by
      calc ri * (a * P * b) * Q / ri = (a * b * (P * Q)) * (ri / ri) := by ring
        _ = a * b := by rw [hPQ, div_self hri]; ring
    exact h3 _ _ _ _ _ h2 h1
  obtain ⟨hreg, hunit⟩ := hloc (K.bundle.U i) (K.om i) (K.isFrame i) hi
  have hu1 : UnitAt x u := by
    rcases hu with rfl | rfl
    · exact unitAt_one x
    · exact ⟨-1, isUnit_one.neg, by simp⟩
  rw [e]
  refine ⟨hu1.regAt.mul hreg, ⟨fun h => hunit.1 ?_, fun h => hu1.mul (hunit.2 h)⟩⟩
  have := hu1.inv.mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hu1.ne_zero, one_mul] at this

end GlobalTheory.LogKSDiv
