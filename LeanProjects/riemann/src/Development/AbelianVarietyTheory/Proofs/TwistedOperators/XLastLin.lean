import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.JacMean

variable {D : D7}

theorem xLast_lin {T T₀ A L : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (o : OrthDec T₀ A L) {ζ : Fin L.rank → D.host.E}
    (hζ : IsLineVec L ζ) : ∃ x : Matrix (Fin T.rank) (Fin (σ + 1)) D.host.E,
      LinearIndependent D.host.E x.transpose ∧ xLast d (vecB o ζ) = rat x := by
  set z : Fin T.rank → D.host.E := d.i₀ *ᵥ (o.iB *ᵥ ζ) with hz
  set x : Matrix (Fin T.rank) (Fin (σ + 1)) D.host.E :=
    Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (d.e k) (z k) with hxdef
  refine ⟨x, ?_, ?_⟩
  · refine (show LinearIndependent D.host.E x.col from ?_)
    rw [← Matrix.mulVec_injective_iff]
    intro v w hvw
    have key : ∀ u : Fin (σ + 1) → D.host.E, x *ᵥ u = d.e *ᵥ (fun j => u j.castSucc) + u (Fin.last σ) • z := by
      intro u; ext k
      simp only [x, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    set u := v - w with hu
    have h0 : x *ᵥ u = 0 := by rw [hu, Matrix.mulVec_sub, hvw, sub_self]
    have hi : d.e'ᴴ * T.gram * d.i₀ = 0 := by
      have := congrArg Matrix.conjTranspose d.i₀e'
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have hZ : (d.e'ᴴ * T.gram) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_mulVec, hi, Matrix.zero_mulVec]
    have h1 : (fun j : Fin σ => u j.castSucc) = 0 := by
      have := congrArg (fun y => (d.e'ᴴ * T.gram) *ᵥ y) ((key u).symm.trans h0)
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hZ, smul_zero, add_zero, Matrix.mulVec_mulVec, d.e'e,
        Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    have hzne : z ≠ 0 := by
      intro hz0
      apply hζ.2
      have e1 : L.gram *ᵥ ζ = (o.iBᴴ * d.i₀ᴴ * T.gram) *ᵥ z := by
        rw [hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← o.isoB, ← d.iso]
        simp only [Matrix.mul_assoc]
      rw [e1, hz0, Matrix.mulVec_zero, dotProduct_zero]
    have h2 : u (Fin.last σ) = 0 := by
      have := (key u).symm.trans h0
      rw [h1, Matrix.mulVec_zero, zero_add] at this
      exact (smul_eq_zero.1 this).resolve_right hzne
    have hu0 : u = 0 := by
      funext i
      refine Fin.lastCases h2 (fun j => congrFun h1 j) i
    exact sub_eq_zero.1 hu0
  · ext k i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [xLast, x, z, vecB, HypDec.j0, rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.of_apply, Fin.snoc_last, Matrix.map_apply]
    · simp [xLast, x, HypDec.jX, rat]

end GlobalTheory.JacMean
