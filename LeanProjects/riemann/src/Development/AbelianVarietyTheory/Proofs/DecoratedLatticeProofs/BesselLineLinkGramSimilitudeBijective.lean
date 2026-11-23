import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LinkSimil
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.LinkGram

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem exists_inv_of_rank_one {m n : ℕ} (hm : m = 1) (hn : n = 1) (τ : Matrix (Fin m) (Fin n) D.host.E) (h : τ ≠ 0) :
    ∃ σ : Matrix (Fin n) (Fin m) D.host.E, σ * τ = 1 ∧ τ * σ = 1 := by
  subst hm; subst hn
  have hd : IsUnit τ.det := by
    rw [Matrix.det_unique, isUnit_iff_ne_zero]
    intro h0; apply h; ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h0]; rfl
  exact ⟨τ⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

theorem scalar_one : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
  have h := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
  rw [map_mul, map_one, cA_cA, mul_comm] at h
  exact h

theorem ofAdj_starAdj (L S : HSp D) (x : WO L S) : ofAdj L S (starAdj L S x) = x := by
  rw [starAdj, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    scalar_one, one_smul]
  simp only [Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

theorem link_gram : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' →
    ∀ l : Link B L' ζ', l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram ∧
      ∀ S : HSp D, Function.Bijective (l.κ S) ∧
        ∀ w, l.κ S w ∈ ratMx D S.rank B.L.rank → w ∈ ratMx D L'.rank S.rank := by
  intro D ρ B L' ζ' h l
  refine ⟨by rw [Int.cast_one, one_mul]; exact GlobalTheory.Unf.StCheck.link_simil h l, fun S => ?_⟩
  have hτ : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : B.ζ = 0 := neg_eq_zero.mp e.symm
    apply B.line.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := exists_inv_of_rank_one B.line.1 h.1 l.τ hτ
  have key : ∀ w, (rat σ : Mx D L'.rank B.L.rank) ⬝ starAdj B.L S (l.κ S w) = w := by
    intro w
    rw [Link.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  refine ⟨⟨fun w w' e => by rw [← key w, ← key w', e], fun x => ⟨(rat σ : Mx D L'.rank B.L.rank) ⬝ starAdj B.L S x, ?_⟩⟩,
    fun w hw => ?_⟩
  · rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, ofAdj_starAdj]
  · rw [← key w]
    refine ratMx_mul (rat_mem σ) ?_
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 hw
    rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
    exact rat_mem _

end GlobalTheory.Unf.LinkGram
