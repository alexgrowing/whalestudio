import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapOfAlgebraMaximalRealSubfieldInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapNormToMaxRealInfiniteIdeleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapInfDiagMaxRealSubfieldCmStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldProdEmbeddingsRegroupMaximalRealStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbeddingStatement

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.CMRealAlg

theorem isAlgPos_of_compNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)),
    (∀ τ : E →+* ℂ, ∃ k : ℤ, expo (compNorm E χ) τ = k) → ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  intro E _ _ _ χ h
  choose k hk using h
  have hkc : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ := fun τ => by
    have := (hk _).symm.trans ((GlobalTheory.T.exponent_heckeChar_compNorm_conjEmbedding E χ τ).trans (hk τ))
    exact_mod_cast this
  obtain ⟨n, hn⟩ := GlobalTheory.T.cmField_prod_embeddings_regroup_maximalReal E k hkc
  refine ⟨n, fun x hx => ?_⟩
  have hpos : ∀ φ : maximalRealSubfield E →+* ℂ,
      ((‖φ (x : maximalRealSubfield E)‖ : ℝ) : ℂ) = φ x ∧ 0 < ‖φ (x : maximalRealSubfield E)‖ := by
    intro φ
    have hr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have h0 := hx hr.embedding
    rw [← hr.coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    exact ⟨rfl, h0⟩
  let z : Cinf E := fun w => ((Real.log (w ((x : maximalRealSubfield E) : E)) / 2 : ℝ) : ℂ)
  let u : (Cinf E)ˣ := expU z
  have hu : u * Units.map (starRingEnd (Cinf E)).toMonoidHom u =
      Units.map (diagInf E).toMonoidHom (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
    apply Units.ext
    funext w
    have e1 := hpos (w.embedding.comp (algebraMap _ E))
    have e2 : ‖w.embedding ((x : maximalRealSubfield E) : E)‖ = w ((x : maximalRealSubfield E) : E) :=
      InfinitePlace.norm_embedding_eq w _
    change Complex.exp (z w) * starRingEnd ℂ (Complex.exp (z w)) = pInf E (algebraMap E (Ad E) ((x : maximalRealSubfield E) : E)) w
    rw [pInf_algebraMap, ← Complex.exp_conj, Complex.conj_ofReal, ← Complex.exp_add, ← Complex.ofReal_add,
      ← Complex.ofReal_exp, show Real.log (w ((x : maximalRealSubfield E) : E)) / 2 + Real.log (w ((x : maximalRealSubfield E) : E)) / 2 =
        Real.log (w ((x : maximalRealSubfield E) : E)) by ring, Real.exp_log (e2 ▸ e1.2), ← e2]
    exact e1.1
  have hN : ideleNorm E (infId E u) = infDiag x := GlobalTheory.T.ideleMapOfAlgebra_maximalRealSubfield_injective E (by rw [GlobalTheory.T.ideleMap_normToMaxReal_infiniteIdele, hu, ← infDiag_eq, GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm])
  have e1 : ((χ.inf x : ℂˣ) : ℂ) = ((chiInf (compNorm E χ) u : ℂˣ) : ℂ) := by
    rw [HChar.inf, MonoidHom.comp_apply, ← hN]; rfl
  rw [e1, chiInf_eq_prod _ k hk]
  let g : (maximalRealSubfield E →+* ℂ) → ℂ := fun φ =>
    Complex.exp ((Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ)
  have hc : ∀ τ : E →+* ℂ, coord τ (u : Cinf E) = g (τ.comp (algebraMap _ E)) := by
    intro τ
    rw [coord_expU]
    congr 1
    have e3 : z (InfinitePlace.mk τ) = ((Real.log ‖(τ.comp (algebraMap (maximalRealSubfield E) E)) (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ) := by
      simp only [z, InfinitePlace.apply]; rfl
    unfold coord
    split_ifs
    · exact e3
    · change starRingEnd ℂ (z (InfinitePlace.mk τ)) = _
      rw [e3, Complex.conj_ofReal]
  simp only [hc]
  rw [hn g]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [zpow_mul, zpow_two, ← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_exp,
    show Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 + Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 =
      Real.log ‖φ (x : maximalRealSubfield E)‖ by ring, Real.exp_log (hpos φ).2, (hpos φ).1]

end GlobalTheory.CMRealAlg
