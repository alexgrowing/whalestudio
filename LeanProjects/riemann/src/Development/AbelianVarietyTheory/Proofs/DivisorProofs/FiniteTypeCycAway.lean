import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

open CategoryTheory AlgebraicGeometry Limits NumberField in

theorem _root_.GlobalTheory.SiegelTor.finiteType_cycAway (n : ℕ) : Algebra.FiniteType ℤ (_root_.GlobalTheory.SiegelTor.cycAway n) := by
  have hfg : (Algebra.adjoin ℤ ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ)).FG := by
    rw [show ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ) = ↑({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Finset ℂ) by simp]
    exact Subalgebra.fg_adjoin_finset _
  have h := (Subalgebra.fg_iff_finiteType _).1 hfg
  rw [Algebra.adjoin_int] at h
  exact h

open CategoryTheory AlgebraicGeometry Limits NumberField in

theorem _root_.GlobalTheory.SiegelTor.arBase_cycAway : ∀ n : ℕ, n ≠ 0 → _root_.GlobalTheory.ZM.ArBase (_root_.GlobalTheory.SiegelTor.cycAway n).subtype := by
  intro n _
  exact ⟨_root_.GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n, _root_.GlobalTheory.SiegelTor.finiteType_cycAway n,
    Subtype.val_injective⟩

end GlobalTheory.SiegelTor
