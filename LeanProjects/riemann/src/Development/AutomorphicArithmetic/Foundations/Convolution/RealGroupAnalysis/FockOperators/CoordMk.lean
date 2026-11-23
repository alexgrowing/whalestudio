import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Fo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem continuous_coordE (τ : E →+* ℂ) : Continuous (coord τ) :=
  AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by
    simpa using FieldIso.norm_coord_le τ x

private theorem continuous_infEqE_symm : Continuous (GlobalTheory.CuspRep.infEq E).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)

private theorem continuous_infEqF_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cw_rt (w : InfinitePlace F) (k : F) :
    cw w (rt k) = w.embedding k := by
  have h : TR.pInf F (rt k) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) k :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) _
  rw [cw, h, InfinitePlace.embedding_of_isReal_apply]

private theorem embedding_pl (τ : E →+* ℂ) (k : F) :
    (pl F τ).embedding k = τ (algebraMap F E k) := by
  have h : (pl F τ).IsReal := IsTotallyReal.isReal _
  have h' := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 h)
  exact RingHom.congr_fun h' k

private theorem cw_rt_pl (τ : E →+* ℂ) (k : F) : cw (pl F τ) (rt k) = τ (algebraMap F E k) := by
  rw [cw_rt, embedding_pl]

private theorem coord_adeleMap (τ : E →+* ℂ) (a : A F) :
    coord τ (pInf E (AdeleBaseChange.adeleMap F E a)) = cw (pl F τ) a := by
  have key : (fun b : InfiniteAdeleRing F =>
        coord τ ((GlobalTheory.CuspRep.infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) b))) =
      fun b => (((TR.infEq F).symm b (pl F τ) : ℝ) : ℂ) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((continuous_coordE τ).comp (continuous_infEqE_symm.comp
        GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap))
      (Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_infEqF_symm)) (funext fun k => ?_)
    have h1 := cw_rt_pl (E := E) τ k
    have h2 := coord_algebraMap τ (algebraMap F E k)
    simp only [Function.comp_apply]
    rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap]
    exact h2.trans h1.symm
  exact congrFun key a.1

end UpperTheory.ConvolutionTheory.R2.Fo

open UpperTheory.ConvolutionTheory.R2.Fo in
theorem UpperTheory.ConvolutionTheory.R2.Fo.coordMk :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), (∀ (τ : E →+* ℂ) u t, coord τ (pInf E (D.mkE u t)) = cw (pl F τ) u + τ D.θ * cw (pl F τ) t) ∧
    (∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) ∧ starRingEnd ℂ (τ D.θ) = -τ D.θ ∧ τ D.θ ≠ 0) ∧
    (∀ w, cw w (rt D.δ) ≠ 0) ∧ ∀ w, ∃ τ : E →+* ℂ, pl F τ = w := by
  intro F E _ _ _ _ _ _ _ D
  have hneg : ∀ w : InfinitePlace F, ∃ r : ℝ, r < 0 ∧ cw w (rt D.δ) = r := fun w =>
    ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) D.δ, D.neg _, by
      rw [cw_rt, InfinitePlace.embedding_of_isReal_apply]⟩
  have hsq : ∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) := fun τ => by
    rw [cw_rt_pl, ← map_pow, D.sq]
  refine ⟨fun τ u t => ?_, fun τ => ⟨hsq τ, ?_, ?_⟩, fun w => ?_, fun w => ?_⟩
  · rw [Dat.mkE, map_add, map_add, map_mul, map_mul, coord_adeleMap, coord_adeleMap, coord_algebraMap, mul_comm (cw _ t)]
  · obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have h0 : (τ D.θ).re = 0 := by
      by_contra hc
      have : (τ D.θ).im = 0 := by
        have : (τ D.θ).re * (τ D.θ).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hc
      rw [this] at hre
      nlinarith [mul_self_nonneg (τ D.θ).re]
    apply Complex.ext <;> simp [h0]
  · intro h0
    obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    rw [h0] at h
    have : (r : ℂ) = 0 := by simpa using h.symm
    exact hr.ne (by exact_mod_cast this)
  · obtain ⟨r, hr, e⟩ := hneg w
    rw [e]
    exact_mod_cast hr.ne
  · obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
    refine ⟨W.embedding, ?_⟩
    rw [← hW]
    change InfinitePlace.mk (W.embedding.comp (algebraMap F E)) = W.comap (algebraMap F E)
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]

end
