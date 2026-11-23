import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurInverseEqReversedNegStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShintaniFormulaGL3DiagStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShintaniFormulaGL3LongWeylDualStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShintaniFormulaGL2DiagStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShintaniFormulaGL2LongWeylDualStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CauchyIdentitySchurGL3GL2Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergEqLFactorStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.UnramifiedZeta

theorem norm_cpow_lt_one (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (s : ℂ) (hs : 0 < s.re) : ‖(residueCard F : ℂ) ^ (-s)‖ < 1 := by
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast GroundTheory.LocalField.one_lt_residueCard
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero GroundTheory.LocalField.residueCard_ne_zero)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simpa using hs)

theorem psi_trivial (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ψ : AddChar F Circle) (hψ : IsStd ψ) :
    (∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1) ∧
      (∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ⁻¹) x = 1) := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have key : ∀ x ∈ 𝒪[F], ψ x = 1 := fun x hx => ht x (mem_valBall_zero_iff.2 hx)
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · show ((ψ x : Circle) : ℂ) = 1
    rw [key x hx, Circle.coe_one]
  · show (((ψ⁻¹) x : Circle) : ℂ) = 1
    rw [AddChar.inv_apply, key (-x) (neg_mem hx), Circle.coe_one]

theorem unramified_sum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → IsUnramifiedChar ν → ∀ y : Fin 2 → ℂˣ, (∀ j, ‖((y j : ℂˣ) : ℂ)‖ = 1) → ∀ W' : GL (Fin 2) F → ℂ, (∀ g, W' g = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ⁻¹) y g) → ∀ s : ℂ, 0 < s.re → zU (sphW ψ ν) W' s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((y j : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ ∧ zU (GL2LocalData.dW3 (sphW ψ ν)) (GL2LocalData.dW2 W') s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ := by
  intro F _ _ _ _ _ _ ψ hψ ν hν _ y hy W' hW' s hs
  obtain ⟨h1, h2⟩ := psi_trivial F ψ hψ
  have hW : W' = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ⁻¹) y := funext hW'
  subst hW
  set x : Fin 3 → ℂˣ := ![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹] with hx
  have hα : ‖((ν (unifUnit F) : ℂˣ) : ℂ)‖ = 1 := hν.2 _
  have hxn : ∀ i, ‖(x i : ℂ)‖ = 1 := by
    intro i; fin_cases i <;> simp [hx, hα]
  have hxi : ∀ i, ‖(((x i)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    intro i; rw [Units.val_inv_eq_inv_val, norm_inv, hxn, inv_one]
  have hyi : ∀ j, ‖(((y j)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    intro j; rw [Units.val_inv_eq_inv_val, norm_inv, hy, inv_one]
  have hq := norm_cpow_lt_one F s hs
  constructor
  · refine GlobalTheory.T.unramified_rankin_selberg_eq_L_factor F (sphW ψ ν) _ (fun a b => Spherical.evalAt x (Spherical.schur ![a, b, 0]))
      (fun a b => Spherical.evalAt y (Spherical.schur ![a, b])) s _
      (fun a b => GlobalTheory.T.shintani_formula_GL3_diag F _ h1 x a b) (fun a b => GlobalTheory.T.shintani_formula_GL2_diag F _ h2 y a b) ?_
    exact GlobalTheory.T.cauchy_identity_schur_GL3_GL2 x y _ hxn hy hq
  · have key := GlobalTheory.T.cauchy_identity_schur_GL3_GL2 (fun i => (x i)⁻¹) (fun j => (y j)⁻¹) _ hxi hyi hq
    have hp : (∏ i, ∏ j, (1 - (((x i)⁻¹ : ℂˣ) : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹) =
        ∏ i, ∏ j, (1 - (x i : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ := by
      simp only [Fin.prod_univ_three, hx]
      simp
      ring
    rw [hp] at key
    refine GlobalTheory.T.unramified_rankin_selberg_eq_L_factor F _ _ (fun a b => Spherical.evalAt x (Spherical.schur ![0, -b, -a]))
      (fun a b => Spherical.evalAt y (Spherical.schur ![-b, -a])) s _
      (fun a b => GlobalTheory.T.shintani_formula_GL3_long_weyl_dual F _ h1 x a b) (fun a b => GlobalTheory.T.shintani_formula_GL2_long_weyl_dual F _ h2 y a b) ?_
    have e3 : ∀ a b : ℤ, Spherical.evalAt x (Spherical.schur ![0, -b, -a]) =
        Spherical.evalAt (fun i => (x i)⁻¹) (Spherical.schur ![a, b, 0]) := by
      intro a b
      rw [GlobalTheory.T.schur_inverse_eq_reversed_neg]
      congr 2
      funext i; fin_cases i <;> simp
    have e2 : ∀ a b : ℤ, Spherical.evalAt y (Spherical.schur ![-b, -a]) =
        Spherical.evalAt (fun i => (y i)⁻¹) (Spherical.schur ![a, b]) := by
      intro a b
      rw [GlobalTheory.T.schur_inverse_eq_reversed_neg]
      congr 2
      funext i; fin_cases i <;> simp
    simpa only [e3, e2] using key

end GlobalTheory.CompanionTheory.UnramifiedZeta
