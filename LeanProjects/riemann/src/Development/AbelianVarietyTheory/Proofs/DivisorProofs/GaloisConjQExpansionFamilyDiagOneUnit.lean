import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.GalFamily

theorem ch_one (N : ℕ) [NeZero N] : ch N 1 = Complex.exp ((2 * Real.pi * Complex.I) / N) := by
  unfold ch
  rcases Nat.lt_or_ge 1 N with h | h
  · haveI : Fact (1 < N) := ⟨h⟩
    rw [ZMod.val_one]; simp
  · have hN : N = 1 := by have := NeZero.pos N; omega
    subst hN
    have : (1 : ZMod 1).val = 0 := rfl
    rw [this]; simp [Complex.exp_two_pi_mul_I]

theorem diag_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    Matrix.diagonal ![1, ((((a : ZMod N).val : ℕ) : ℤ) : ZMod N)] = ((dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem qConj_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  intro hE F _ _ _ hf s N _ L hs hL z hz g a κ κ' y hg hκ hy α
  have hact := GlobalTheory.WpFam.Act.rightActions N
  have hy' : vmul y α ≠ 0 := fun h ↦ hy ((hact.2.2.2.2.1 y α).1 h)
  have hq := (GlobalTheory.T.qConj_torsion_points N g a hg (vmul y α)).2.2 hy'
  rw [hact.2.2.1] at hq
  have hcop : IsCoprime (((a : ZMod N).val : ℕ) : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime a)
  have hz1 : g (Complex.exp ((2 * Real.pi * Complex.I) / N)) =
      Complex.exp ((2 * Real.pi * Complex.I) * ((((a : ZMod N).val : ℕ) : ℤ) : ℂ) / N) := by
    rw [← ch_one, hg 1, mul_one, ch, Int.cast_natCast]
  have h := GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients hE F hf s N (twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N))) hs (NeZero.pos N)
    (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL) z hz g _ κ κ' _ _ hcop hz1 hκ hq
  rw [diag_eq, GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul F N L _ _ hL.2, ← Units.val_mul] at h
  exact h

end GlobalTheory.HilbFam.GalFamily
