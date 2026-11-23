import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSylvester

theorem neg_card_eq_sig : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau),
    (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  intro D V hV A τ
  set ε := A.ε τ with hε
  set a := (Finset.univ.filter fun i => ε i = true).card with ha_def
  set b := (Finset.univ.filter fun i => ε i = false).card with hb_def
  have ha : Fintype.card {i // ε i = true} = a := by rw [Fintype.card_subtype]
  have hb : Fintype.card {i // ¬ ε i = true} = b := by
    rw [Fintype.card_subtype]; simp [b]
  let e0 : Fin V.rank ≃ Fin a ⊕ Fin b :=
    (Equiv.sumCompl (fun i => ε i = true)).symm.trans
      (Equiv.sumCongr (Fintype.equivFinOfCardEq ha) (Fintype.equivFinOfCardEq hb))
  have hl : ∀ k : Fin a, ε (e0.symm (Sum.inl k)) = true := fun k => by
    simp [e0]
    exact ((Fintype.equivFinOfCardEq ha).symm k).2
  have hr : ∀ k : Fin b, ε (e0.symm (Sum.inr k)) = false := fun k => by
    simp [e0]
    simpa using ((Fintype.equivFinOfCardEq hb).symm k).2
  have hcard : Fintype.card (Fin V.rank) = a + b := by simpa using Fintype.card_congr e0
  set F := A.fr τ with hF_def
  have hF : IsUnit F := A.fr_unit τ
  have hFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hF)
  have hJ : (F⁻¹)ᴴ * gramAt D V τ * F⁻¹ = Formalism.REAL.Jm ε := by
    rw [← A.fr_gram τ]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = (F * F⁻¹)ᴴ * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFi]; simp
  let Q : Matrix (Fin V.rank) (Fin a ⊕ Fin b) ℂ := (F⁻¹).submatrix id e0.symm
  have hQ : Qᴴ * gramAt D V τ * Q = Formalism.UG.Jpq a b := by
    have h2 : Qᴴ * gramAt D V τ * Q = ((F⁻¹)ᴴ * gramAt D V τ * F⁻¹).submatrix e0.symm e0.symm := by
      ext r s; simp only [Q, Matrix.mul_apply, submatrix_apply, conjTranspose_apply, id]
    rw [h2, hJ]
    ext (r | r) (s | s) <;>
      simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, hl, hr, e0.symm.injective.eq_iff] <;>
      split_ifs <;> simp
  have hsig1 : Formalism.UG.HasSignature (V.gram.map (tauE D τ)) a b :=
    GlobalTheory.FrameComplement.hasSignature_of_frame hcard Q hQ
  have hsig2 := hV (tauE D τ)
  have heq : a = (V.sig (tauE D τ)).1 := GlobalTheory.SylvesterInertia.hasSignature_fst_unique hsig1 hsig2
  obtain ⟨e2, _, _⟩ := hsig2
  have h2 : V.rank = (V.sig (tauE D τ)).1 + (V.sig (tauE D τ)).2 := by simpa using Fintype.card_congr e2
  have h3 : V.rank = a + b := by simpa using hcard
  omega

end GlobalTheory.FrameSylvester
