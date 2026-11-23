import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FinitePartAdelicPointMatrix
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem chi_exp {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) (hχ : IsHeckeChar D χ) {m : ℕ}
    (hη : ResEta D χ m) (τ : D.what₂.Tau) :
    ∃ k : ℤ, Even (k - (m : ℤ)) ∧ ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ k := by
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ m τ hθ hχ hη
  have ha' := ha
  obtain ⟨k, hk, hall⟩ := ha
  refine ⟨k, ?_, hall.2 θ hθ⟩
  obtain ⟨η, -, hη2, hη3, -⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨k', hk', hall'⟩ := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist ha' (hη2 τ) m
  have ek : k' = k - m := by
    have : (k' : ℚ) = k - m := by rw [hk', hk]; ring
    exact_mod_cast this
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom hσ
  let w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1)
  have ww : w * w = 1 := by
    funext τ'
    simp only [w, Pi.mul_apply, Pi.one_apply, Pi.mulSingle_apply]
    split_ifs <;> simp
  let x0 : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have hx0 : (x0 : AE D) = e w := rfl
  have hfix : cA D (x0 : AE D) = x0 := by
    refine GlobalTheory.SplitCharExp.ext_of_chart hσ ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x0 : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x0 : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig _
      rw [e3, hx0, e1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, hx0, e2]
      simp only [w, Pi.mulSingle_apply]
      split_ifs <;> simp
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_unit D x0 hfix
  obtain ⟨⟨η0, hη0⟩, hχ0⟩ := hη
  have hξ : (χ * (η ^ m)⁻¹) x0 = 1 := by
    rw [← hb, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, hχ0 η0 hη0 b, hη3.2 η0 hη0 b, pow_one,
      mul_inv_cancel]
  have hv := hall'.2 θ hθ x0 (by rw [hx0, e1]) fun τ' h => by rw [hx0, e2]; simp [w, Pi.mulSingle_eq_of_ne h]
  rw [hξ, hx0, e2] at hv
  simp only [w, Pi.mulSingle_eq_same, norm_neg, norm_one, Complex.ofReal_one, div_one, Circle.coe_one] at hv
  rw [← ek]
  have hv' : ((-1 : ℂ)) ^ k' = 1 := by simpa using hv.symm
  rcases Int.even_or_odd k' with h | h
  · exact h
  · exfalso
    rw [h.neg_one_zpow] at hv'
    norm_num at hv'

def mOf (a : GL (Fin n) ℂ) : PositivityTheory.Rg.Sw.GR n where
  val :=
    { val := fromBlocks a.1 0 0 (a⁻¹).1ᴴ
      inv := fromBlocks (a⁻¹).1 0 0 a.1ᴴ
      val_inv := by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← conjTranspose_mul, Units.mul_inv,
          conjTranspose_one]
        exact fromBlocks_one
      inv_val := by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← conjTranspose_mul, Units.inv_mul,
          conjTranspose_one]
        exact fromBlocks_one }
  property := by
    show InG (fromBlocks a.1 0 0 (a⁻¹).1ᴴ)
    simp only [InG, JJ, fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_conjTranspose, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul, Units.inv_mul, ← conjTranspose_mul, Units.mul_inv, conjTranspose_one, neg_zero]

theorem mR_mOf (a : GL (Fin n) ℂ) : mR (mOf a) = fromBlocks a.1 0 0 (a⁻¹).1ᴴ := rfl

theorem mR_mOf_inv (a : GL (Fin n) ℂ) : mR (mOf a)⁻¹ = fromBlocks (a⁻¹).1 0 0 a.1ᴴ := rfl

theorem component_block_matrix {R : Type} (θ : InfFam D) (τ : D.what₂.Tau) (a b c d : Matrix (Fin n) (Fin n) (AE D)) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  rw [compAt_eq_map, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]; rfl

theorem finite_part_block_matrix_map (a b c d : Matrix (Fin n) (Fin n) (AE D)) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  rw [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]; rfl

theorem block_matrix_diagonal_one_eq_one {R : Type} [Zero R] [One R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, fromBlocks_one, submatrix_one_equiv]

theorem compAt_adj {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (X : Matrix (Fin n) (Fin n) (AE D)) :
    compAt θ τ (adj X) = (compAt θ τ X)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.FockCompare.comp_cA hθ]
  rfl

theorem finPart_adj (X : Matrix (Fin n) (Fin n) (AE D)) (hX : X.map (finPart D) = 1) : (adj X).map (finPart D) = 1 := by
  ext i j
  have e3 : finPart D (cA D (X j i)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (X j i)) :=
    GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig _
  have := congrFun (congrFun hX j) i
  simp only [Matrix.map_apply] at this
  simp only [adj, Matrix.map_apply, Matrix.transpose_apply, e3, this, Matrix.one_apply]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

end PositivityTheory.Rg.Sw.Glob.LocLawH
