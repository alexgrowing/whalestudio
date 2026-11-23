import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareCharUnit

theorem exists_root_of_locIn {D : D7} {K : Type} [Field K] (σ : K →+* ℂ) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E)
    (h : ChrEq c χ) (hL : LocIn σ χ) (x : (AE D)ˣ) (hx : Formalism.L2.Pj.FinUnit x) :
    ∃ ζ : K, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ σ ζ = ((c x : Circle) : ℂ) := by
  have hmem : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
    obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
      (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
    rw [hprod x hx.1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
    exact prod_mem fun P _ => hL P _
  obtain ⟨ζ, hζ⟩ := hmem
  obtain ⟨-, -, -, m, hm, hpow⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c h.1.1
  refine ⟨ζ, ⟨m, hm, σ.injective ?_⟩, hζ⟩
  rw [map_pow, map_one, hζ, ← Circle.coe_pow, hpow x hx, Circle.coe_one]

theorem nu_finUnit_root : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (t : T) (x : (AE D)ˣ), Formalism.L2.Pj.FinUnit x →
    ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      D.what₂.embLL ζ = (((Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) /
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) x : Circle) : ℂ) := by
  intro D T Lc sc G μ₀ hL hC i j t x hx
  have hi := i.2
  obtain ⟨a, ⟨n₁, h₁, e₁⟩, ha⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.mu0 j) (hC.mu0 j) x hx
  obtain ⟨b, ⟨n₂, h₂, e₂⟩, hb⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.xi t) (hC.xi t) x hx
  obtain ⟨c, ⟨n₃, h₃, e₃⟩, hc⟩ := exists_root_of_locIn D.what₂.embLL _ _
    (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) (hC.chi (D.R.m - i) (by omega) (by omega)) x hx
  refine ⟨a * b / c, ⟨n₁ * n₂ * n₃, by positivity, ?_⟩, ?_⟩
  · rw [div_pow, mul_pow]
    have f₁ : a ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_assoc, pow_mul, e₁, one_pow]
    have f₂ : b ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_right_comm, mul_comm, pow_mul, e₂, one_pow]
    have f₃ : c ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_comm, pow_mul, e₃, one_pow]
    rw [f₁, f₂, f₃, one_mul, div_one]
  · rw [mul_div_mul_right_eq_div, map_div₀, map_mul, ha, hb, hc, MonoidHom.div_apply, Circle.coe_div]
    congr 1

end GlobalTheory.SquareCharUnit
