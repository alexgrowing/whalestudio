import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isometric_toZ_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (t : X ⟶ Sp ℤ) (t' : Y ⟶ Sp ℤ) (π : Y ⟶ X) (hπ : π ≫ p = q) (hπ' : π ≫ t = t') (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (hL' : ∀ τ, (wZ (L.pull π hπ) t' τ).IsCInf), (toZ (L.pull π hπ) t' hL').Isometric ((toZ L t hL).pull π hπ') := by
  intro k _ X Y p q t t' π hπ hπ' L hL hL'
  refine HermLB.isometric_of_eqOn fun τ a y _ => ?_
  have key : ∀ (σ σ' : k →+* ℂ) (_ : σ = σ') (z : CxPts p σ) (z' : CxPts p σ'), z.1 = z'.1 →
      (L.φ σ).φ (a PUnit.unit) z = (L.φ σ').φ (a PUnit.unit) z' := by
    rintro σ _ rfl z z' h
    rw [Subtype.ext h]
  refine (Weight.pull_φ (wZ L t τ) π hπ' a y).trans (Eq.trans ?_ (Weight.pull_φ (L.φ (emb q y)) π hπ a (unsheet q y)).symm)
  refine key _ _ ?_ _ _ rfl
  have e : (PtsOver.map π hπ' _ y).1 ≫ p = y.1 ≫ q := by
    rw [← hπ]
    exact Category.assoc _ _ _
  show (Spec.preimage ((PtsOver.map π hπ' _ y).1 ≫ p)).hom = (Spec.preimage (y.1 ≫ q)).hom
  rw [e]

end GlobalTheory.CompanionTheory.Ar.BaseZ
