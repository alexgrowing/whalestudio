import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqOneOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfPullbackGenericallyEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullOfGenericallySmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticCoverOverModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPositivePullbackGenericallyEtaleStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SemiPullAll

theorem isometric_pull_pull {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem semiPull_of_principalisation : GlobalTheory.Published.Principalisation → SemiPull := by
  intro hP k _ X Y p q D E hp hq π hπ L hL
  have := hp.isIntegral
  have := hq.isIntegral
  obtain ⟨X', _, ρ, hρ, hsm, hgen, hdeg⟩ := GlobalTheory.GenRes.exists_birational_genSmooth hP k X p D hp
  obtain ⟨V, hV, het⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k X X' p (ρ ≫ p) D hp hρ ρ rfl hgen (by rw [hdeg]; exact one_ne_zero)
  have h₁ : (L.pull ρ rfl).SemiPos D := GlobalTheory.T.semiPositive_pullback_generically_etale k X X' p (ρ ≫ p) D hp hρ ρ rfl V hV het L hL
  have hπp : IsArithVar (π ≫ p) E := by rw [hπ]; exact hq
  obtain ⟨Y', _, g, π', hcomm, hY', hggen, hgdeg⟩ := GlobalTheory.T.exists_arithmeticCover_over_modification k X X' Y p D E ρ π hp hρ hπp hgen
  have hY'q : IsArithVar (g ≫ q) E := by rw [← hπ]; exact hY'
  have e₁ : π' ≫ ρ ≫ p = g ≫ q := by rw [← Category.assoc, hcomm, Category.assoc, hπ]
  have e₂ : (g ≫ π) ≫ p = g ≫ q := by rw [Category.assoc, hπ]
  have h₂ : ((L.pull ρ rfl).pull π' e₁).SemiPos E :=
    GlobalTheory.T.semiPos_pull_of_genericallySmooth k X' Y' (ρ ≫ p) (g ≫ q) D E hsm π' e₁ (L.pull ρ rfl) h₁
  have iso : ((L.pull ρ rfl).pull π' e₁).Isometric ((L.pull π hπ).pull g rfl) :=
    (isometric_pull_pull L ρ rfl π' e₁ (g ≫ π) e₂ hcomm).trans
      (isometric_pull_pull L π hπ g rfl (g ≫ π) e₂ rfl).symm
  have h₃ : ((L.pull π hπ).pull g rfl).SemiPos E :=
    (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric (GlobalTheory.MixHt.arCalc_of_principalisation hP) k Y' (g ≫ q) E hY'q _ _ iso).1 h₂
  obtain ⟨W, hW, hWet⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k Y Y' q (g ≫ q) E hq hY'q g rfl hggen hgdeg
  exact GlobalTheory.T.semiPos_of_pullback_generically_etale k Y Y' q (g ≫ q) E hq hY'q g rfl W hW hWet (L.pull π hπ) h₃

end GlobalTheory.SemiPullAll
