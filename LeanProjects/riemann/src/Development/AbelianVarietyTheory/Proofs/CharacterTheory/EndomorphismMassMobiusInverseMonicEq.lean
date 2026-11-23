import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionCancelOfOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveMulEqVonMangoldtConvolutionStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassEqOfLinearEquivInvariantStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMulParabolicInductionTrivialStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEndomorphismDensityGLRecursionStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsiStatement

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem mass_comp_charpoly_eq_mul (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (P : F[X]) :
    mass (fun g : Module.End F V => s (LinearMap.charpoly g)) P =
      s P * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  have : Finite (Module.End F V) := Module.finite_of_finite F
  unfold mass
  have hfin : ({g : Module.End F V | LinearMap.charpoly g = P}).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have : LinearMap.charpoly g = P := by simpa using hg
  simp [this]

theorem mass_psi_eq_glCard_mul_mangoldt_div :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (s : F[X] → ℂ), IsAdditive s → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V →
      mass (psi s V) P = glCard F P.natDegree * mangoldt s P / ((Nat.card F : ℂ) ^ P.natDegree - 1) := by
  intro F _ _ V _ _ _ s hs P hP hdeg
  have hiso := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hmu1 : mu (1 : F[X]) = 1 := (GlobalTheory.T.charpolyEndomorphismDensityGL_recursion F 1 monic_one).2
  have hlog := GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution F (Nat.card F) hq s mu hs hmu1 (fun Q hQ => (GlobalTheory.T.charpolyEndomorphismDensityGL_recursion F Q hQ).1)
  have hmul : ∀ Q : F[X], Q.Monic → s Q * mu Q =
      conv (fun D => mass (psi s (Fin D.natDegree → F)) D / glCard F D.natDegree) mu Q := by
    intro Q hQ
    have h := GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial F (Fin Q.natDegree → F) (fun V _ _ _ => psi s V) hiso Q hQ (by simp)
    have h2 : (fun g : Module.End F (Fin Q.natDegree → F) =>
        ∑ᶠ W : {W : Submodule F (Fin Q.natDegree → F) // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2)) =
        fun g => s (LinearMap.charpoly g) := by
      funext g
      exact (GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F _ s g).symm
    rw [← h]
    rw [h2, mass_comp_charpoly_eq_mul, mu, mul_div_assoc]
  have hc := GlobalTheory.T.monicFactorizationConvolution_cancel_of_one F _ _ mu hmu1 (fun Q hQ => (hmul Q hQ).symm.trans (hlog Q hQ)) P hP
  have hV := GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F V (fun V _ _ _ => psi s V) hiso P hdeg
  have hg : glCard F P.natDegree ≠ 0 := by
    unfold glCard
    exact_mod_cast (Nat.card_pos (α := GL (Fin P.natDegree) F)).ne'
  rw [hV, mul_div_assoc, ← hc, mul_div_cancel₀ _ hg]

end GlobalTheory.CuspGL
