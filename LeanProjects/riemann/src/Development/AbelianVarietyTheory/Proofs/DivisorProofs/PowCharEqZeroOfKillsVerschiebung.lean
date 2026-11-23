import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem frobProj_frobTwist_app {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (x : (frobTwist h G).A n) :
    ((frobProj h G).frobTwist h h).app n x = (frobProj h (frobTwist h G)).app n x := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add, hx, hy]
  | h1 r a =>
    rw [SemiBialgHom.smul_map, SemiBialgHom.smul_map, SemiHom.frobTwist_app_frobProj]

theorem pow_char_eq_zero_of_verschiebung (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n))
    (hχ : ∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) : χ ^ p = 0 := by
  refine CartierDual.ext_apply fun y => ?_
  induction y using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => rw [map_add, hx, hy, map_add]
  | h1 r a =>
    rw [map_smul, ← frobTwistDual_verschiebung h (G := frobTwist h G) n χ,
      ← SemiHom.app_verschiebung h h (frobProj h G), frobProj_frobTwist_app,
      frobTwistDual_frobProj, hχ, zero_pow (Fact.out : p.Prime).ne_zero, smul_zero]
    rfl

end GlobalTheory.PDivGroup
