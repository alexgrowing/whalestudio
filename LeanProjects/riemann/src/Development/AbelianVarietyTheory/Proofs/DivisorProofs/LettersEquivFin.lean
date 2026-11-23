import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet

namespace GlobalTheory.LetterCount

theorem two_mul_sum_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : 2 * ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (E →+* ℂ) * (Dw.p + Dw.q) := by
  have hinv : Function.Involutive (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := fun τ =>
    RingHom.ext fun x => by simp [conjEmb]
  have h2 : ∑ τ : E →+* ℂ, Dw.mult τ = ∑ τ : E →+* ℂ, Dw.mult (conjEmb τ) :=
    (Equiv.sum_comp hinv.toPerm Dw.mult).symm
  rw [two_mul]
  nth_rewrite 2 [h2]
  rw [← Finset.sum_add_distrib]
  simp [GlobalTheory.ShFam.Pad.AdmExist.mult_add_mult_conj, Finset.sum_const, Finset.card_univ]

theorem nonempty_equiv_letter : ∀ (D : D7) (O : Setup D), Nonempty (Fin (D.R.f * O.N) ≃ Pad.Letter O.S.Dw) := by
  intro D O
  refine ⟨Fintype.equivOfCardEq ?_⟩
  rw [Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h := two_mul_sum_mult O.S.Dw
  rw [O.S.rank_eq, NumberField.Embeddings.card, Formalism.MainNotions.Gaps.LevGap.finrank_hostE_eq D.host] at h
  have h' := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (h.trans (mul_assoc _ _ _))
  first | exact h'.symm | exact h' | linarith

end GlobalTheory.LetterCount
