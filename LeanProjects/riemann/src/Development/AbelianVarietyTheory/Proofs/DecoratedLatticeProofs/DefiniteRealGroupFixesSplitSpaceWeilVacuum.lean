import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumExponentSum

noncomputable section
open scoped Matrix ComplexOrder
open Formalism.IndefR.Datum

namespace GlobalTheory.VacuumSplitReal

theorem trace_cartan_of_sig {k t : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) (hs : IsCartanInv G s)
    (hG : Formalism.UG.HasSignature G t t) (hk : k = 2 * t) : s.trace = 0 := by
  obtain ⟨e, P, hP⟩ := hG
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ, Q = (P : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ,
      Q' = ((P⁻¹ : GL (Fin t ⊕ Fin t) ℂ) : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  have hQQ : Q' * Q = 1 := by rw [hQ, hQ', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let B0 : Matrix (Fin t ⊕ Fin t) (Fin t) ℂ := Matrix.fromRows 1 1
  let C0 : Matrix (Fin t) (Fin t ⊕ Fin t) ℂ := Matrix.fromCols 1 0
  have hC0 : C0 * B0 = 1 := by
    simp [C0, B0, Matrix.fromCols_mul_fromRows]
  have hPP : Qᴴ * G.reindex e e * Q = Formalism.UG.Jpq t t := by
    rw [← hP, hQ]; rfl
  have hB0 : B0ᴴ * Formalism.UG.Jpq t t * B0 = 0 := by
    simp [B0, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin k) (Fin t) ℂ, B = (Q * B0).submatrix e id := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin t) (Fin k) ℂ, C = (C0 * Q').submatrix id e := ⟨_, rfl⟩
  have h1 : C * B = 1 := by
    rw [hB, hC, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_assoc, ← Matrix.mul_assoc Q', hQQ,
      Matrix.one_mul, hC0]
  have h2 : Bᴴ * G * B = 0 := by
    have hG' : G = (G.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hB, Matrix.conjTranspose_submatrix, hG', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    have h3 : (Q * B0)ᴴ * G.reindex e e * (Q * B0) = B0ᴴ * (Qᴴ * G.reindex e e * Q) * B0 := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [h3, hPP, hB0]
  exact GlobalTheory.SplitVacSum.trace_eq_zero hs.1 hs.2.2 (m := t) (by rw [Fintype.card_fin, hk]) B C h1 h2

end GlobalTheory.VacuumSplitReal

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.VacuumSplitReal

theorem vacuum_fixed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (t : ℕ) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) 1) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → HSpace.SigOK H → H.rank = 2 * t → (∀ τ, H.sig τ = (t, t)) → ∀ f, IsThetaFunO ψ A H f → (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO 1 (sH τ)) f) → ∀ b ∈ GinfC A, om (b, 1) f = f := by
  intro D ψ θ A H t χA om sH hθ ⟨η, hη⟩ hW hA hH hsig hrank hsigt f hf hv b hb
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ A (fun τ => hdet (hA τ)) b hb
  have mt1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt H 1) = 1 := fun τ => by
    unfold Formalism.L2.Theta.mt compAt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (by simp) (by simp)
  have h1 : ∀ τ, HasInfExp D 1 τ 0 := fun τ => ⟨0, by norm_num, ⟨θ, hθ⟩, fun _ _ _ _ _ => by simp⟩
  have hexp : ∀ τ, HasInfExp D (1 * (η ^ H.rank)⁻¹) τ ((-(t : ℤ) : ℤ) : ℚ) := fun τ => by
    have h := GlobalTheory.VacuumCharacter.hasInfExp_twist (h1 τ) (hη.2.2.2 τ) H.rank
    convert h using 1
    rw [hrank]; push_cast; ring
  have hν := hxv _ (fun _ => -(t : ℤ)) hexp
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std A H θ hθ χA 1 om η hη hW (fun _ => 1) sH hA hH b hb 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [mt1, one_mul, mul_one]) x 1 hx ?_ f hf hv]
  · conv_rhs => rw [← one_smul ℂ f]
    congr 1
    rw [Circle.coe_mul, Circle.coe_inv, hν, MonoidHom.map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := A.rank) (sH τ) (hH τ).1
    have htr : (sH τ).trace = 0 := by
      have hs := hsig (tauE D τ)
      rw [hsigt] at hs
      exact trace_cartan_of_sig (gramAt D H τ) (sH τ) (hH τ) hs hrank
    have hpt : p = t := by
      have : (p : ℂ) = t := by
        rw [htr, hrank] at hp; push_cast at hp; linear_combination -hp / 2
      exact_mod_cast this
    have inv : (compAt θ τ (Formalism.L2.Theta.mt A b)).det * (compAt θ τ (Formalism.L2.Theta.mt A b⁻¹)).det = 1 := by
      rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
      unfold Formalism.L2.Theta.mt
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
    have d0 := left_ne_zero_of_mul_eq_one inv
    rw [mt1, (hd _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, hpt, mul_one,
      show (1 / 2 : ℂ) • (1 + sH τ) + (1 / 2 : ℂ) • (1 - sH τ) = 1 by module, Matrix.det_one, one_pow, one_mul,
      zpow_neg, inv_inv, zpow_natCast, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ d0)]
  · unfold Formalism.L2.Theta.IsDetRoot
    simp

end GlobalTheory.VacuumSplitReal

end
