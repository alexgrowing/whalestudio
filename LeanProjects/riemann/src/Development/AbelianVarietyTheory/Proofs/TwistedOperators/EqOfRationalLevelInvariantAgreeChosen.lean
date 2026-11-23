import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMovesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ExtInv

theorem eq_of_invariant : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  intro D S T C Lv M hM hM𝔪 gL hgL φ ψ hφ hψ hφk hψk hag
  have hΛ : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [Red.fmt_one]; exact Red.isMov_one _
  obtain ⟨-, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hI : C.under Lv ≠ ⊥ := (hL Lv 1 _ hΛ.1 hm1).2.2.1
  have hgrp := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.1
  have hcomm := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1
  funext g
  obtain ⟨γ, hγ, a, ha, g', hg', k, hk, hg, ht, -, hck, hcJ⟩ := GlobalTheory.T.exists_rational_real_trivialAt_congruent_factor D T C.X.Λ (C.under Lv) M hΛ hI hM g
  have hinv : fmt T g' * fmt T g'⁻¹ = 1 := by rw [← (hgrp g' g'⁻¹).2.1, mul_inv_cancel, Red.fmt_one]
  obtain ⟨L, hLf, hLm⟩ := ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ C.X.Λ hΛ).2.2.2 _ _ hinv).1
  have hLl : L ∈ Lv.lats := (hL Lv g' L hLf.1 hLm).2.1 ht
  obtain ⟨h1, h2, h3⟩ := hgL L hLl
  have hk1 : C.LevK Lv k 1 := Red.levK_one C Lv k hk hck.1 (hcJ _ hM𝔪)
  have hk2 : C.LevK Lv ((gL L)⁻¹ * g') 1 := GlobalTheory.T.level_group_congruent_of_two_lattice_moves D S T C Lv (gL L) g' L h1 hg' h2 ht hLf.1 h3 hLm
  have e : g = γ * (gL L * a * ((gL L)⁻¹ * g') * k) := by
    rw [hg, ← (hcomm a ha).2.2 _ h1]
    group
  rw [e, hφ γ hγ, hψ γ hγ, hφk k hk1, hψk k hk1, hφk _ hk2, hψk _ hk2]
  exact hag L hLl a ha

end GlobalTheory.Ker.ExtInv
