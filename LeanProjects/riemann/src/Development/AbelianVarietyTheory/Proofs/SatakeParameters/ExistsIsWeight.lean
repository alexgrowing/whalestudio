import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRealSubfieldAlgebraicOfCompNormIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldProdEmbeddingsRegroupMaximalReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.PolarizedWeight

theorem exists_isWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∃ wt : ℤ, IsWeight π wt := by
  intro E _ _ _ l a ha π χ h
  obtain ⟨hreg, hpol, -⟩ := h
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ with hψ
  have key : ∀ τ : E →+* ℂ, (CG.mk π).infChar (ComplexEmbedding.conjugate τ) =
      ((CG.mk π).infChar τ).map fun z => -(z + expo ψ⁻¹ τ) := fun τ => by
    have h1 := (hm τ).twist ψ⁻¹
    rw [GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (ComplexEmbedding.conjugate τ)), Multiset.map_map]
    rfl

  have hint : ∀ τ : E →+* ℂ, ∃ k : ℤ, expo ψ τ = k := fun τ => by
    obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
      Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
    obtain ⟨n, hn⟩ := (hreg τ).2 z hz
    have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (ComplexEmbedding.conjugate τ) := by
      rw [key]
      exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
    obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
    refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
    rw [GlobalTheory.RegAlgCharAlg.expo_inv'] at hn'
    push_cast
    linear_combination hn' + hn
  choose k hk using hint
  have hkc : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ := fun τ => by
    have := (hk _).symm.trans ((GlobalTheory.T.exponent_heckeChar_compNorm_conjEmbedding E χ τ).trans (hk τ))
    exact_mod_cast this
  let n : (maximalRealSubfield E →+* ℂ) → ℤ := fun φ => k (ComplexEmbedding.lift E φ)
  have hkn : ∀ τ : E →+* ℂ, k τ = n (τ.comp (algebraMap (maximalRealSubfield E) E)) := fun τ => by
    rcases GlobalTheory.cm_eq_or_conj_of_comp_eq E (ComplexEmbedding.lift E (τ.comp (algebraMap (maximalRealSubfield E) E))) τ
      (ComplexEmbedding.lift_comp_algebraMap E _).symm with h | h
    · exact congrArg k h
    · exact (congrArg k h).trans (hkc _)

  have hn : ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ,
      ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ = ∏ φ, g φ ^ (2 * n φ) := by
    classical
    intro g
    rw [← Finset.prod_fiberwise Finset.univ
      (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]
    refine Finset.prod_congr rfl fun φ _ => ?_
    set τ₀ := ComplexEmbedding.lift E φ with hτ₀
    have h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ :=
      ComplexEmbedding.lift_comp_algebraMap E φ
    have h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ := by
      rw [GlobalTheory.cm_conj_comp_eq, h0]
    have hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀ := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)
    have hfib : Finset.univ.filter
        (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) =
        {τ₀, ComplexEmbedding.conjugate τ₀} := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        exact GlobalTheory.cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)
      · rintro (rfl | rfl)
        · exact h0
        · exact h1
    rw [hfib, Finset.prod_pair hne, h0, h1, hkc, mul_comm (2 : ℤ), zpow_mul, zpow_two]
  have hAlg : IsAlgPos χ n := fun x hx => by
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
    have hN : ideleNorm E (infId E u) = infDiag x := GlobalTheory.T.ideleMapOfAlgebra_maximalRealSubfield_injective E (by rw [GlobalTheory.T.ideleMap_normToMaxReal_infiniteIdele, hu, ← InfType.infDiag_eq, GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm])
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
  have hpar := UpperTheory.heckeChar_parallel_weight (maximalRealSubfield E) χ n hAlg
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  refine ⟨(a : ℤ) - 1 - n φ₀, fun τ => ?_⟩
  have hconj : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = ComplexEmbedding.conjugate τ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E τ x
  have hb : expo ψ⁻¹ τ = -(n φ₀ : ℂ) := by
    rw [GlobalTheory.RegAlgCharAlg.expo_inv', hk, hkn, hpar _ φ₀]
  rw [hconj, key]
  refine Multiset.map_congr rfl fun z _ => ?_
  rw [hb]
  push_cast
  ring

end GlobalTheory.PolarizedWeight
