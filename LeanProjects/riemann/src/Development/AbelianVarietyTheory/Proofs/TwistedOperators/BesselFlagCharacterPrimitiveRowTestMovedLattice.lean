import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimAtOfMonoId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem colMul_besDecAt (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (hjm : j < D.R.m) (i : Fin σ)
    (t : AE D) : colMul (besDecAt G j σ hj).jX i t = fun k => (incA D (D.host.xi0 ^ (i : ℕ)) * t) *
      incA D ((G.rowDec j hjm).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [colMul, HypDec.jX, rat, Matrix.map_apply, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id, map_mul]
  ring

theorem rowId_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p := by
  rw [rowId, tiltSc, if_neg hj, FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem primAt_rowN {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (G : GridData L sc) (j σ : ℕ)
    (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) : PrimAt ψ (besDecAt G j σ hj) (rowN G j) v := by
  have hjm : j < D.R.m := by omega
  have hodd : ¬ Odd j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  obtain ⟨-, f2, f3, -, f5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero

  set I : Fin σ → FI D := fun i => FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (i : ℕ))⁻¹ *
    stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) (Fin.castLE (by omega) i) with hIdef
  have hI0 : ∀ i, I i ≠ 0 := fun i => mul_ne_zero
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (inv_ne_zero (pow_ne_zero _ hξ))) (stairId_ne_zero _ _)
  have sub : ∀ (𝔞 : FI D) a, a ∈ idV 𝔞 v → a ∈ idAt D (· = v) := fun 𝔞 a ha => by
    have := (f3 𝔞 1 one_ne_zero a).1 (by rwa [FractionalIdeal.spanSingleton_one, one_mul])
    exact this.2
  have line : ∀ i (t : AE D), t ∈ idAt D (· = v) →
      (colMul (besDecAt G j σ hj).jX i t ∈ latV _ (rowN G j) (· = v) ↔ t ∈ idV (I i) v) := by
    intro i t ht
    rw [colMul_besDecAt G j σ hj hjm, rowN, dif_pos hjm,
      (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff (G.rowDec j hjm) (neg_ne_zero.2 one_ne_zero) _ _ _ v _).1, rowId_even hodd,
      hIdef, f3 _ _ (inv_ne_zero (pow_ne_zero _ hξ)), inv_inv]
    exact ⟨fun h => ⟨h, ht⟩, fun h => h.1⟩
  intro i i' hii s hs
  have key : (∀ a : AE D, colMul (besDecAt G j σ hj).jX i' a ∈ latV _ (rowN G j) (· = v) →
      colMul (besDecAt G j σ hj).jX i (s * a) ∈ latV _ (rowN G j) (· = v)) ↔
      ∀ a ∈ idV (I i') v, s * a ∈ idV (I i) v := by
    constructor
    · intro h a ha
      have haA := sub _ a ha
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).1 (h a ((line i' a haA).2 ha))
    · intro h a hc
      have haA := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul _ hc
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).2 (h a ((line i' a haA).1 hc))
  have hratio : I i * (I i')⁻¹ = dI D := by
    have hst := stairId_succ (𝔞 := D.host.AA) (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (Fin.castLE (by omega) i : Fin (D.R.m - 1 - j))
      (Fin.castLE (by omega) i') (by simp only [Fin.val_castLE]; exact hii)
    have e : I i = dI D * I i' := by
      simp only [hIdef, dI, hst, hii]
      have e2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (D.host.xi0 ^ (i : ℕ))⁻¹ =
          FractionalIdeal.spanSingleton _ D.host.xi0 * FractionalIdeal.spanSingleton _ (D.host.xi0 ^ ((i : ℕ) + 1))⁻¹ := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        congr 1
        rw [pow_succ, mul_inv, mul_comm (D.host.xi0 ^ (i : ℕ))⁻¹, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
      rw [e2]
      ring
    rw [e, mul_inv_cancel_right₀ (hI0 i')]
  rw [key, f2 _ _ (hI0 i') (hI0 i) s hs, hratio]
  exact f5 s hs

end GlobalTheory.RowShape

namespace GlobalTheory.RowShape

theorem big_primAt_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.PrimAt ch.W.ψ (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) v :=
  big_mono (fun ch h j σ hj v => primAt_rowN h ch.G j σ hj v) GlobalTheory.BigTop.Fun.OneSqTie.big_std

end GlobalTheory.RowShape

end
