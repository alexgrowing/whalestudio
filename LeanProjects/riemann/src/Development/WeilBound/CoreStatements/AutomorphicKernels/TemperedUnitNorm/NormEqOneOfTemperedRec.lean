import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneUnitary
import ReciprocityTheory.GaloisValuations.Global
import GroundTheory.PAdicHodge.AInfGalois

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TempSatGal

theorem comp_complexConj {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (τ : E →+* Qbar l) :
    ι.toRingHom.comp (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) =
      ComplexEmbedding.conjugate (ι.toRingHom.comp τ) := by
  refine RingHom.ext fun x => ?_
  have := IsCMField.complexEmbedding_complexConj (K := E) (ι.toRingHom.comp τ) x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact this

theorem sum_map_affine (M : Multiset ℂ) (u v : ℂ) :
    (M.map fun z => u + v * z).sum = (M.card : ℂ) * u + v * M.sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons, Multiset.sum_cons]
    push_cast; ring

end GlobalTheory.TempSatGal
