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

theorem WOver.pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (m : ℕ) :
    WOver (fun σ => (φ σ).pow m) (ψ.pow m) := by
  intro σ j y hy
  refine (ψ.zpow_φ _ j _).trans (Eq.trans ?_ ((φ σ).zpow_φ _ j y).symm)
  exact congrArg _ (h σ _ y (mem_pow_iff.1 hy))

theorem WOver.restr {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (i : Z ⟶ X) :
    WOver (p := i ≫ p) (t := i ≫ t) (fun σ => (φ σ).pull i rfl) (ψ.pull i rfl) := by
  intro σ j y hy
  have hm : PtsOver.map i rfl _ y ∈ ptsIn p σ (B.U (j PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => PtsOver.map i rfl _ y) (fun _ => rfl) hy PUnit.unit
  refine (ψ.pull_φ i rfl j _).trans (Eq.trans ?_ ((φ σ).pull_φ i rfl j y).symm)
  exact h σ _ _ hm

theorem wOver_restr_pow : ∀ (k : Type) [CommRing k] (X Z : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (i : Z ⟶ X) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (τ : ℤ →+* ℂ), WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) ∧ ∀ m : ℕ, WOver ((L.restr i).pow m).φ ((((toZ L t hL).restr i).pow m).φ τ) := by
  intro k _ X Z p t i L hL τ
  have h : WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) := (wOver_wZ L t τ).restr i
  exact ⟨h, fun m => h.pow m⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
