import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompShiftZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DescOfDes
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.DescTest

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem step_desc (hOut : D.Out l) (hk : k = false ∨ ρ = 0) (r : ℕ) :
    Desc (ε.qk 1 - 1) (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).fn (jE (F.pt κ)) :=
  desc_fil F κ ε k n ρ hρ hk r _ (des_qk hOut ε (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).1 n (ρ r))

theorem xi_thick (T : (F.pt κ).Elements) :
    ((gE F κ k n).obj T).i ((base l).cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i)) ∈ ((gE F κ k n).obj T).J :=
  xi_mem F κ k n T _ ((GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.1 T.1 n)

theorem mu_factor : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i :=
  (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.2.1

end

set_option maxHeartbeats 1000000 in

theorem main : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) →
    Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) := by
  intro l _ hOut O _ F κ ε k n ρ hρ hk
  exact desc_flt (b := bs l k n) (L := Lc F κ k n) (Λ := Acris l) (F.pt κ) ((base l).cris n) (gE F κ k n) ρ hρ
    ε.μ (ε.μ_mem k (base l) n) (jE (F.pt κ)) (ε.qk 1 - 1) (∑ i ∈ Finset.range l, ε.qk 1 ^ i)
    (mu_factor ε) (xi_thick F κ ε k n) (step_desc F κ ε k n ρ hρ hOut hk)

end GlobalTheory.CompanionTheory.DescTest
