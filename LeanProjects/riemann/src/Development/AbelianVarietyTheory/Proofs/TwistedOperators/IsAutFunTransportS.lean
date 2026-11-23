import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

open GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

structure RowMatchS (ch : Choice R) (G' : GlobalTheory.Grid.GridPre R) : Prop where

  V : ∀ i, i ≤ D.R.m → SameSp (ch.G.V (.grid i 0)) (G'.V i 0).V

  ν : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).ν (ch.M.ν (.grid i 0))

  fd : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).fd (ch.M.fd (.grid i 0))

  ker : ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
    GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f ∧ ∃ p,
      HEq (fun h g => thetaKO (G'.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f p))
        (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h)

theorem transport_stepS {A A' B B' : HSp D} (eA : SameSp A' A) (eB : SameSp B' B)
    {ν : Measure (GA D A)} {fd : Set (GA D A)} {ν' : Measure (GA D A')} {fd' : Set (GA D A')}
    (hν : HEq ν ν') (hfd : HEq fd fd') {K : GA D B → GA D A → ℂ} {K' : GA D A' → GA D B' → ℂ}
    (hK : HEq K (fun h g => K' g h)) {φ : GA D A → ℂ} {φ' : GA D A' → ℂ} (hφ : HEq φ φ') {ψ : GA D B → ℂ}
    (hI : ∀ h, IntegrableOn (fun g => K h g * φ g) fd ν) (hE : ∀ h, ∫ g in fd, K h g * φ g ∂ν = ψ h) :
    (∀ h, IntegrableOn (fun g => K' g h * φ' g) fd' ν') ∧ HEq ψ (fun h => ∫ g in fd', K' g h * φ' g ∂ν') := by
  obtain ⟨L, h1, h2, rfl⟩ := eA
  obtain ⟨L', h1', h2', rfl⟩ := eB
  obtain rfl := eq_of_heq hν
  obtain rfl := eq_of_heq hfd
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hK
  exact ⟨hI, heq_of_eq (funext hE).symm⟩

theorem isAutFun_transportS {V V' : HSp D} (e : SameSp V' V) {φ : GA D V → ℂ} {φ' : GA D V' → ℂ} (h : HEq φ φ')
    (hφ : IsAutFun V φ) : IsAutFun V' φ' := by
  obtain ⟨L, h1, h2, rfl⟩ := e
  obtain rfl := eq_of_heq h
  exact ⟨hφ.left, hφ.level, hφ.cont⟩

end GlobalTheory.RowLift

end
