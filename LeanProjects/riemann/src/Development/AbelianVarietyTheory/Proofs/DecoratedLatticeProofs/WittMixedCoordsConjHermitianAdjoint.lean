import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)

variable {D : D7}

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y := by
  simp only [dagger, adj_add, Matrix.add_mul, Matrix.mul_add]

theorem hO_dagger (S T : HSp D) (x y : WO S T) : hO T S (dagger S T x) (dagger S T y) = hO S T y x := by
  simp only [hO_eq_trace, dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplOH_dagger (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  rw [symplOH_eq, hO_dagger, ← symplOH_eq, symplOH_skew]

theorem conj_psi_of_std {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h3 : ψ a * starRingEnd ℂ (ψ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hne : ψ a ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h3.trans h2.symm)

theorem adelicConj_incl_neg_inv_hermitianScalar : cA D (incA D (-D.host.xi0⁻¹)) = incA D D.host.xi0⁻¹ := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

section Target

variable {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)

theorem dagger_incAdj (y : Mx D S.rank ρ) :
    dagger S T (d.incAdj S y) = d.extX S (incA D D.host.xi0⁻¹ • y) := by
  rw [dagger, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.extX_apply, d.pX_eq, adj_mul, adj_smul, adj_mul, adj_adj,
    adj_gA, adelicConj_incl_neg_inv_hermitianScalar]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, giA_gA_cancel]

theorem dagger_incX (ξ : Mx D ρ S.rank) : dagger S T (d.incX S ξ) = d.extY S (giA S ⬝ adj ξ) := by
  simp only [dagger, HypDec.incX_apply, HypDec.extY_apply, d.pY_eq, adj_mul, Matrix.mul_assoc]

theorem hermitianAdjointHomSpace_wittCoreInclusion (w : WO S T₀) : dagger S T (d.inc0 S w) = d.ext0 S (dagger S T₀ w) := by
  simp only [dagger, HypDec.wittDecomp_inclAnisotropicHom_apply, HypDec.matrixExtendByZero_apply, d.p0_eq, adj_mul, Matrix.mul_assoc, gA_giA_cancel]

end Target

end GlobalTheory.MixSwap

end

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)
open scoped Pointwise

variable {D : D7}

theorem borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

attribute [local instance] borelMx

def adjE (S : HSp D) (ρ : ℕ) : Mx D ρ S.rank ≃+ Mx D S.rank ρ where
  toFun ξ := giA S ⬝ adj ξ
  invFun a := adj (gA S ⬝ a)
  left_inv ξ := by simp only [gA_giA_cancel, adj_adj]
  right_inv a := by simp only [adj_adj, giA_gA_cancel]
  map_add' ξ ξ' := by simp only [adj_add, Matrix.mul_add]

theorem adjE_apply (S : HSp D) (ρ : ℕ) (ξ : Mx D ρ S.rank) : adjE S ρ ξ = giA S ⬝ adj ξ := rfl

theorem adjE_symm_apply (S : HSp D) (ρ : ℕ) (a : Mx D S.rank ρ) : (adjE S ρ).symm a = adj (gA S ⬝ a) := rfl

theorem continuous_adjE (S : HSp D) (ρ : ℕ) : Continuous (adjE S ρ) :=
  continuous_const.matrix_mul continuous_adj

theorem continuous_adjE_symm (S : HSp D) (ρ : ℕ) : Continuous (adjE S ρ).symm :=
  continuous_adj.comp (continuous_const.matrix_mul continuous_id)

def adjM (S : HSp D) (ρ : ℕ) : Mx D ρ S.rank ≃ᵐ Mx D S.rank ρ :=
  (Homeomorph.mk (adjE S ρ).toEquiv (continuous_adjE S ρ) (continuous_adjE_symm S ρ)).toMeasurableEquiv

theorem coe_adjM (S : HSp D) (ρ : ℕ) : ⇑(adjM S ρ) = ⇑(adjE S ρ) := rfl

theorem coe_adjM_symm (S : HSp D) (ρ : ℕ) : ⇑(adjM S ρ).symm = ⇑(adjE S ρ).symm := rfl

theorem adjE_mem {S : HSp D} {ρ : ℕ} {ξ : Mx D ρ S.rank} (h : ξ ∈ ratMx D ρ S.rank) : adjE S ρ ξ ∈ ratMx D S.rank ρ :=
  ratMx_mul (rat_mem _) (ratMx_adj h)

theorem adjE_symm_mem {S : HSp D} {ρ : ℕ} {a : Mx D S.rank ρ} (h : a ∈ ratMx D S.rank ρ) :
    (adjE S ρ).symm a ∈ ratMx D ρ S.rank :=
  ratMx_adj (ratMx_mul (rat_mem _) h)

theorem isCovolOne_map {S : HSp D} {ρ : ℕ} {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) :
    IsCovolOne (ratMx D S.rank ρ) (μ.map (adjM S ρ)) (adjM S ρ '' 𝓕) := by
  obtain ⟨hH, hF, h1⟩ := hμ
  have P : MeasurePreserving (adjM S ρ) μ (μ.map (adjM S ρ)) := (adjM S ρ).measurable.measurePreserving μ
  have Q : MeasurePreserving (adjM S ρ).symm (μ.map (adjM S ρ)) μ := P.symm (adjM S ρ)
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_adjM]
    exact (adjE S ρ).isAddHaarMeasure_map μ (continuous_adjE S ρ) (continuous_adjE_symm S ρ)
  · rw [MeasurableEquiv.image_eq_preimage_symm]
    refine ⟨hF.nullMeasurableSet.preimage Q.quasiMeasurePreserving, ?_, ?_⟩
    · filter_upwards [Q.quasiMeasurePreserving.ae hF.ae_covers] with a ha
      obtain ⟨g, hg⟩ := ha
      refine ⟨⟨adjE S ρ g, adjE_mem g.2⟩, ?_⟩
      rw [Set.mem_preimage, AddSubgroup.vadd_def, vadd_eq_add, coe_adjM_symm, map_add,
        AddEquiv.symm_apply_apply]
      rw [AddSubgroup.vadd_def, vadd_eq_add, coe_adjM_symm] at hg
      exact hg
    · have key : ∀ g : ratMx D S.rank ρ, g +ᵥ ((adjM S ρ).symm ⁻¹' 𝓕) =
          (adjM S ρ).symm ⁻¹' ((⟨(adjE S ρ).symm g, adjE_symm_mem g.2⟩ : ratMx D ρ S.rank) +ᵥ 𝓕) := by
        intro g
        ext x
        simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, AddSubgroup.vadd_def, vadd_eq_add,
          coe_adjM_symm, map_add, map_neg]
      intro g g' hne
      have hne' : (⟨(adjE S ρ).symm g, adjE_symm_mem g.2⟩ : ratMx D ρ S.rank) ≠ ⟨(adjE S ρ).symm g', adjE_symm_mem g'.2⟩ := by
        intro h
        apply hne
        exact Subtype.ext ((adjE S ρ).symm.injective (congrArg Subtype.val h))
      show AEDisjoint _ (g +ᵥ _) (g' +ᵥ _)
      rw [key g, key g']
      exact (hF.aedisjoint hne').preimage Q.quasiMeasurePreserving
  · rw [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image, h1]

end GlobalTheory.MixSwap

end

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)

attribute [local instance] borelMx

theorem mixS_cj_dagger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∃ (μ' : Measure (Mx D S.rank ρ)) (𝓕' : Set (Mx D S.rank ρ)), IsCovolOne (ratMx D S.rank ρ) μ' 𝓕' ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incAdj S y) = d.extX S (incA D D.host.xi0⁻¹ • y)) ∧ (∀ ξ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incX S ξ) = d.extY S (giA S ⬝ adj ξ)) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.inc0 S w) = d.ext0 S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T₀ w)) ∧ ∀ (f : WO S T → ℂ) y, d.mixS S ψ μ' 𝓕' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) (incA D D.host.xi0⁻¹ • y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T₀ S) (d.mixT S ψ μ 𝓕 f y) := by
  intro D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  refine ⟨μ.map (adjM S ρ), adjM S ρ '' 𝓕, isCovolOne_map hμ, dagger_incAdj d S, dagger_incX d S, hermitianAdjointHomSpace_wittCoreInclusion d S, ?_⟩
  intro f y
  funext w
  have P : MeasurePreserving (adjM S ρ) μ (μ.map (adjM S ρ)) := (adjM S ρ).measurable.measurePreserving μ
  have hint : ∀ G : Mx D S.rank ρ → ℂ,
      ∫ a in adjM S ρ '' 𝓕, G a ∂(μ.map (adjM S ρ)) = ∫ ξ in 𝓕, G (adjM S ρ ξ) ∂μ :=
    fun G => P.setIntegral_image_emb (adjM S ρ).measurableEmbedding G 𝓕
  simp only [HypDec.mixS, HypDec.mixT, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hint, ← integral_conj]
  congr 1
  funext ξ
  rw [HypDec.integrandS_eq, HypDec.integrandT_eq]
  have e1 : d.extY S (adjM S ρ ξ) = dagger S T (d.incX S ξ) := (dagger_incX d S ξ).symm
  have e2 : d.extX S (incA D D.host.xi0⁻¹ • y) = dagger S T (d.incAdj S y) := (dagger_incAdj d S y).symm
  have e3 : d.ext0 S w = dagger S T (d.inc0 S (dagger T₀ S w)) := by rw [hermitianAdjointHomSpace_wittCoreInclusion, dagger_dagger]
  rw [e1, e2, e3, symplOH_dagger, ← dagger_add, ← dagger_add]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger, map_mul, conj_psi_of_std hψ]

end GlobalTheory.MixSwap

end
