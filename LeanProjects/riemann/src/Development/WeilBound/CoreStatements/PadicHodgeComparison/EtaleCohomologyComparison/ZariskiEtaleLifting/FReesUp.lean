import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompShiftZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.rees_up : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n : ℕ), ((∀ r, RI 1 n (Φ.S r).fn G) → RI 1 n Φ.rees G) ∧ (∀ μ' ξ : R, Φ.μ = μ' * ξ → (∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T) → (∀ r, Desc μ' (Φ.S r).fn G) → Desc (X : ℤ[X]) Φ.rees G) ∧ ∀ {T T' : C} (i : T ⟶ T') (g : T' ⟶ T'), Φ.FAcyc i g → Acyc1 (X : ℤ[X]) (Φ.rees.map i).hom (Φ.rees.map g).hom :=
  @GlobalTheory.CompanionTheory.ReesUp.main
