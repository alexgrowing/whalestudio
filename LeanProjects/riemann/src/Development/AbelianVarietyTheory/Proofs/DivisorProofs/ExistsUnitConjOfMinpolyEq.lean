import Mathlib
import GroundTheory.Brauer.SkolemNoether
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def evalQuot {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : AdjoinRoot q →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {q}) (Polynomial.aeval x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero])

theorem evalQuot_root {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : evalQuot q x hx (AdjoinRoot.root q) = x := by
  change Polynomial.aeval x Polynomial.X = x
  simp

section Generic2

variable {S : Type*} [Ring S]

theorem triv_change (σ : S →+* Sᵐᵒᵖ) (x u : Sˣ) (b : S) :
    ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop =
      x * b * (σ x).unop := by
  have h1 : (σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop
      = x * ((((u⁻¹ : Sˣ) : S) * u) * b * ((σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop)) * (σ x).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Generic2

namespace Pair

variable {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

theorem sh_units_mul_inv (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul, Units.inv_mul]; simp [sh]

theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm

theorem triv_conj (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ) (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]; rfl
  rw [e, triv_change, hx]

def conjBy (Q : Pair G) (y : G.Cˣ) (γ' : G.Cˣ) (hγ : (γ' : G.C) = y * Q.γ * ↑y⁻¹)
    (hreg : (minpoly G.F (γ' : G.C)).natDegree = G.n ∧ (minpoly G.F (γ' : G.C)).Separable) : Pair G where
  β := y * Q.β * Units.mk (sh G y) (sh G ((y⁻¹ : G.Cˣ) : G.C)) (sh_units_mul_inv y)
    (by rw [← sh_mul, Units.mul_inv]; simp [sh])
  γ := γ'
  c := Q.c
  sym := by
    simp only [Units.val_mul, Units.val_mk, sh_mul, sh_sh, Q.sym, mul_assoc]
  sim := by
    simp only [Units.val_mul, Units.val_mk]
    rw [hγ, sh_mul, sh_mul]
    have h1 : ((y⁻¹ : G.Cˣ) : G.C) * y = 1 := Units.inv_mul y
    have h2 : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := sh_units_mul_inv y
    calc (y : G.C) * Q.γ * ↑y⁻¹ * (y * Q.β * sh G y) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G ↑Q.γ * sh G y))
        = y * (Q.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * Q.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) *
            sh G Q.γ) * sh G y := by
          simp only [mul_assoc]
      _ = y * (algebraMap ℚ G.C Q.c * Q.β) * sh G y := by rw [h1, h2, mul_one, mul_one, Q.sim]
      _ = _ := by rw [← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc, mul_assoc]
  reg := hreg
  trivAf := by
    obtain ⟨x, t, hx⟩ := Q.trivAf
    exact ⟨_, t, by simpa only [Units.val_mul, Units.val_mk] using triv_conj (AfP p) Q.β y x t hx⟩
  trivR := by
    obtain ⟨z, hz⟩ := Q.trivR
    exact ⟨_, by simpa only [Units.val_mul, Units.val_mk] using triv_conj ℝ Q.β y z 1 hz⟩

end Pair

end GlobalTheory.LKMid
