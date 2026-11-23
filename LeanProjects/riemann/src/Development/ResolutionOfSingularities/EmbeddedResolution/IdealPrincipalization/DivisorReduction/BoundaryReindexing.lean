import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem map_comap_id (X : Scheme.{u}) (E : List X.IdealSheafData) :
    E.map (fun D => D.comap (𝟙 X)) = E := by
  induction E with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, Scheme.IdealSheafData.comap_id, ih]

theorem get_eq_comap_id {X : Scheme.{u}} (E₁ E₂ : List X.IdealSheafData) (j₁ j₂ : ℕ)
    (hj₁ : j₁ < E₁.length) (hj₂ : j₂ < E₂.length)
    (heq : E₁.get ⟨j₁, hj₁⟩ = E₂.get ⟨j₂, hj₂⟩) :
    E₂.get ⟨j₂, hj₂⟩ = (E₁.get ⟨j₁, hj₁⟩).comap (𝟙 X) := by
  rw [Scheme.IdealSheafData.comap_id, heq]

private theorem eq_comap_id_of_eq {X : Scheme.{u}} {A B : X.IdealSheafData} (h : A = B) :
    A = B.comap (𝟙 X) := by
  rw [Scheme.IdealSheafData.comap_id]
  exact h

private theorem sameNontrivialBoundary_map_comap_id {X : Scheme.{u}} {A B : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary A (B.map fun D => D.comap (𝟙 X)) := by
  rw [map_comap_id]
  exact h

private theorem get_append_cons_length {X : Scheme.{u}} (E₁ : List X.IdealSheafData)
    (D : X.IdealSheafData) (E₂ : List X.IdealSheafData)
    (h : E₁.length < (E₁ ++ D :: E₂).length) :
    (E₁ ++ D :: E₂).get ⟨E₁.length, h⟩ = D := by
  induction E₁ with
  | nil => rfl
  | cons a l ih => exact ih _

private theorem eraseIdx_append_cons_length {X : Scheme.{u}} (E₁ : List X.IdealSheafData)
    (D : X.IdealSheafData) (E₂ : List X.IdealSheafData) :
    (E₁ ++ D :: E₂).eraseIdx E₁.length = E₁ ++ E₂ := by
  induction E₁ with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem isomorphic_of_isStrictPullbackAlongId {X : Scheme.{u}} (A B : SequenceOfBlowups X)
    (h : IsStrictPullbackBlowupSeq (𝟙 X) A B) : A.Isomorphic B := by
  unfold IsStrictPullbackBlowupSeq at h
  obtain ⟨hlen, σ, h0, hpb, hc⟩ := h
  have hiso : ∀ (i : ℕ) (hi : i ≤ A.length), IsIso (σ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hh : σ 0 hi = A.isoZero.hom ≫ B.isoZero.inv := by
          rw [Iso.eq_comp_inv]
          simpa using h0
        rw [hh]
        infer_instance
    | succ k ih =>
        intro hi
        have hk : k < A.length := hi
        exact (hpb k hk).isIso_fst_of_isIso (ih (le_of_lt hk))
  unfold SequenceOfBlowups.Isomorphic
  exact ⟨hlen, fun i hi => @asIso Scheme _ _ _ (σ i hi) (hiso i hi), by simpa using h0,
    fun i hi => (hpb i hi).w, fun i hi => (hc i hi).symm⟩

namespace DivisorReduction

theorem containedComponentsIdeal_withBoundary_congr (T : MarkedIdealWithBoundary.{u})
    (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ)
    (hj₂ : j₂ < L₂.length) (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) :
    containedComponentsIdeal (T.withBoundary L₁) j₁ hj₁ = containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂ := by
  rw [containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T.withBoundary L₁) j₁ hj₁,
    containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T.withBoundary L₂) j₂ hj₂]
  show componentsInOrderLocusIdeal T.ideal T.mult (L₁.get ⟨j₁, hj₁⟩)
      = componentsInOrderLocusIdeal T.ideal T.mult (L₂.get ⟨j₂, hj₂⟩)
  rw [heq]

structure BoundaryReindexingInvariance : Prop where
  smooth_id : ∀ X : Scheme.{u}, AlgebraicGeometry.Smooth (𝟙 X)
  surjective_id : ∀ X : Scheme.{u}, AlgebraicGeometry.Surjective (𝟙 X)
  lowerIdealPre_shift :
    ∀ (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ)
      (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length),
      L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩ →
      lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁
  boundaryEquiv_restrictedBoundary_reindex :
    ∀ (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ)
      (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length),
      L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩ →
      MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁) →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
        (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁))

private theorem isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_smooth (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (S : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < S.boundary.length)
    (I₀ : S.scheme.IdealSheafData) (E₀ : List S.scheme.IdealSheafData)
    (D' : S.scheme.IdealSheafData)
    (ψ : D'.subscheme ⟶ (restrictToBoundaryDivisor S j hj I₀ E₀).scheme)
    [AlgebraicGeometry.Smooth ψ] [AlgebraicGeometry.Surjective ψ]
    (hq : ψ ≫ (restrictToBoundaryDivisor S j hj I₀ E₀).structMap = D'.subschemeι ≫ S.structMap)
    (I₀' : S.scheme.IdealSheafData) (F : List S.scheme.IdealSheafData)
    (hid : (I₀.comap (S.boundary.get ⟨j, hj⟩).subschemeι).comap ψ = I₀'.comap D'.subschemeι)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun Dd => Dd.comap ψ)
        (List.map (fun Dd => Dd.comap (S.boundary.get ⟨j, hj⟩).subschemeι)
          (List.take (S.boundary.length - 1) (E₀.eraseIdx j))))
      (List.map (fun Dd => Dd.comap D'.subschemeι) F))
    (hV₁ : (restrictToBoundaryDivisor S j hj I₀ E₀).IsAdmissible)
    (hd₁ : (restrictToBoundaryDivisor S j hj I₀ E₀).krullDimSucc < n)
    (hV₂ : (S.withSchemeIdealBoundary D'.subscheme (D'.subschemeι ≫ S.structMap) (I₀'.comap D'.subschemeι)
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).IsAdmissible)
    (hd₂ : (S.withSchemeIdealBoundary D'.subscheme (D'.subschemeι ≫ S.structMap) (I₀'.comap D'.subschemeι)
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).krullDimSucc < n) :
    IsStrictPullbackBlowupSeq ψ
      (L (S.withSchemeIdealBoundary D'.subscheme (D'.subschemeι ≫ S.structMap) (I₀'.comap D'.subschemeι)
        (List.map (fun Dd => Dd.comap D'.subschemeι) F))).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor S j hj I₀ E₀)).toSequenceOfBlowups := by
  rw [← hid] at hV₂ hd₂ ⊢
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((restrictToBoundaryDivisor S j hj I₀ E₀).pullbackAlong D'.subscheme
        (D'.subschemeι ≫ S.structMap) ψ).boundary
      (List.map (fun Dd => Dd.comap D'.subschemeι) F) := hBE
  have hVp : (((restrictToBoundaryDivisor S j hj I₀ E₀).pullbackAlong D'.subscheme
      (D'.subschemeι ≫ S.structMap) ψ).withBoundary
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).IsAdmissible := hV₂
  have hdp : (((restrictToBoundaryDivisor S j hj I₀ E₀).pullbackAlong D'.subscheme
      (D'.subschemeι ≫ S.structMap) ψ).withBoundary
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).krullDimSucc < n := hd₂
  exact hL.smooth_pullback_strict (restrictToBoundaryDivisor S j hj I₀ E₀) hV₁ hd₁ D'.subscheme
    (D'.subschemeι ≫ S.structMap) ψ hq (List.map (fun Dd => Dd.comap D'.subschemeι) F)
    hBE' hVp hdp

theorem isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq
    (hbc : SmoothPullbackCompatibility.{u}) (hsh : BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (I₀' : T.scheme.IdealSheafData) (E₀' : List T.scheme.IdealSheafData)
    (hI : I₀' = I₀.comap (𝟙 T.scheme))
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) (E₀'.eraseIdx j₂))
      (List.map (fun D => D.comap (𝟙 T.scheme))
        (List.take (L₁.length - 1) (E₀.eraseIdx j₁))))
    (hV₁ : (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀).IsAdmissible)
    (hd₁ : (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀).krullDimSucc < n)
    (hV₂ : (restrictToBoundaryDivisor (T.withBoundary L₂) j₂ hj₂ I₀' E₀').IsAdmissible)
    (hd₂ : (restrictToBoundaryDivisor (T.withBoundary L₂) j₂ hj₂ I₀' E₀').krullDimSucc < n) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq))
      (L (restrictToBoundaryDivisor (T.withBoundary L₂) j₂ hj₂ I₀' E₀')).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀)).toSequenceOfBlowups := by
  have hD : L₂.get ⟨j₂, hj₂⟩ = (L₁.get ⟨j₁, hj₁⟩).comap (𝟙 T.scheme) :=
    get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq
  have hsmid : AlgebraicGeometry.Smooth (𝟙 T.scheme) := hsh.smooth_id T.scheme
  have hsuid : AlgebraicGeometry.Surjective (𝟙 T.scheme) := hsh.surjective_id T.scheme
  have hsq := isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme
    (𝟙 T.scheme) (L₂.get ⟨j₂, hj₂⟩) hD
  have hsmo : AlgebraicGeometry.Smooth
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme T.scheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subscheme (L₂.get ⟨j₂, hj₂⟩).subscheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι (L₂.get ⟨j₂, hj₂⟩).subschemeι
      (𝟙 T.scheme)
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) hsq.flip hsmid
  have hsur : AlgebraicGeometry.Surjective
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) :=
    @surjective_snd_of_isPullback_of_surjective T.scheme T.scheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subscheme (L₂.get ⟨j₂, hj₂⟩).subscheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι (L₂.get ⟨j₂, hj₂⟩).subschemeι
      (𝟙 T.scheme)
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) hsuid hsq.flip
  have hw : (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
      (L₂.get ⟨j₂, hj₂⟩) hD) ≫ ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι
      = (L₂.get ⟨j₂, hj₂⟩).subschemeι := by
    simpa using hsq.w
  have h2 : ((divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) ≫ ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι)
        ≫ (T.withBoundary L₁).structMap
      = (L₂.get ⟨j₂, hj₂⟩).subschemeι ≫ (T.withBoundary L₁).structMap :=
    congrArg (fun f => f ≫ (T.withBoundary L₁).structMap) hw
  have hq : (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
      (L₂.get ⟨j₂, hj₂⟩) hD) ≫ (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀).structMap
      = (L₂.get ⟨j₂, hj₂⟩).subschemeι ≫ (T.withBoundary L₁).structMap :=
    (Category.assoc _ _ _).symm.trans h2
  refine @isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_smooth n L O hL (T.withBoundary L₁) j₁ hj₁ I₀ E₀
    (L₂.get ⟨j₂, hj₂⟩)
    (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
      (L₂.get ⟨j₂, hj₂⟩) hD) hsmo hsur hq I₀'
    (List.take (L₂.length - 1) (E₀'.eraseIdx j₂)) ?_ ?_ hV₁ hd₁ hV₂ hd₂
  · rw [hI]
    exact comap_subschemeMapOfComap (𝟙 T.scheme) ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩)
      (L₂.get ⟨j₂, hj₂⟩) hD I₀
  · exact (sameNontrivialBoundary_comap_subschemeι (𝟙 T.scheme)
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩) (L₂.get ⟨j₂, hj₂⟩) hD
      (List.take (L₁.length - 1) (E₀.eraseIdx j₁))
      (List.take (L₂.length - 1) (E₀'.eraseIdx j₂)) hE).symm

theorem isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hbc : SmoothPullbackCompatibility.{u}) (hsh : BoundaryReindexingInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁))
    (hV₁ : (T.withBoundary L₁).IsAdmissible)
    (hdim₁ : (T.withBoundary L₁).krullDimSucc ≤ n)
    (hO₁ : (T.withBoundary L₁).IsOrderBoundedByMult)
    (hDB₁ : (T.withBoundary L₁).IsBalanced hV₁.locallyOfFiniteType)
    (hcs₁ : (orderAtLeastLocus (T.withBoundary L₁).ideal (T.withBoundary L₁).mult).Nonempty)
    (hV₂ : (T.withBoundary L₂).IsAdmissible)
    (hdim₂ : (T.withBoundary L₂).krullDimSucc ≤ n)
    (hO₂ : (T.withBoundary L₂).IsOrderBoundedByMult)
    (hDB₂ : (T.withBoundary L₂).IsBalanced hV₂.locallyOfFiniteType)
    (hcs₂ : (orderAtLeastLocus (T.withBoundary L₂).ideal (T.withBoundary L₂).mult).Nonempty)
    (hZ : containedComponentsIdeal (T.withBoundary L₁) j₁ hj₁ = ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ (lowerIdealWithoutBlowup (T.withBoundary L₁))
        (lowerBoundaryWithoutBlowup (T.withBoundary L₁)) T.scheme (𝟙 T.scheme) (L₂.get ⟨j₂, hj₂⟩)
        (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq))
      (L (restrictToDivisor (T.withBoundary L₂) j₂ hj₂)).toSequenceOfBlowups
      (L (restrictToDivisor (T.withBoundary L₁) j₁ hj₁)).toSequenceOfBlowups := by
  have hZ₂ : containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂ = ⊤ := by
    rw [← containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
    exact hZ
  have hlen₁ : (L₁.eraseIdx j₁).length = L₁.length - 1 := by
    simp [List.length_eraseIdx, hj₁]
  have hlen₂ : (L₂.eraseIdx j₂).length = L₂.length - 1 := by
    simp [List.length_eraseIdx, hj₂]
  have ht₁ : List.take (L₁.length - 1) (L₁.eraseIdx j₁) = L₁.eraseIdx j₁ := by
    rw [← hlen₁]; simp
  have ht₂ : List.take (L₂.length - 1) (L₂.eraseIdx j₂) = L₂.eraseIdx j₂ := by
    rw [← hlen₂]; simp
  have hI : lowerIdealWithoutBlowup (T.withBoundary L₂)
      = (lowerIdealWithoutBlowup (T.withBoundary L₁)).comap (𝟙 T.scheme) :=
    (Scheme.IdealSheafData.comap_id _).symm
  have hE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryWithoutBlowup (T.withBoundary L₂)).eraseIdx j₂))
      (List.map (fun D => D.comap (𝟙 T.scheme))
        (List.take (L₁.length - 1) ((lowerBoundaryWithoutBlowup (T.withBoundary L₁)).eraseIdx j₁))) := by
    rw [lowerBoundaryWithoutBlowup_eq (T.withBoundary L₂), lowerBoundaryWithoutBlowup_eq (T.withBoundary L₁)]
    show MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (L₂.length - 1) (L₂.eraseIdx j₂))
        (List.map (fun D => D.comap (𝟙 T.scheme)) (List.take (L₁.length - 1) (L₁.eraseIdx j₁)))
    rw [ht₁, ht₂, map_comap_id]
    exact hBE
  have hVa : (restrictToDivisor (T.withBoundary L₁) j₁ hj₁).IsAdmissible :=
    hfacts.valid_lowerTop (T.withBoundary L₁) hV₁ hO₁ hDB₁ j₁ hj₁ hZ
  have hVb : (restrictToDivisor (T.withBoundary L₂) j₂ hj₂).IsAdmissible :=
    hfacts.valid_lowerTop (T.withBoundary L₂) hV₂ hO₂ hDB₂ j₂ hj₂ hZ₂
  have hda : (restrictToDivisor (T.withBoundary L₁) j₁ hj₁).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₁) hV₁ hcs₁ j₁ hj₁
      (lowerIdealWithoutBlowup (T.withBoundary L₁)) (lowerBoundaryWithoutBlowup (T.withBoundary L₁))) hdim₁
  have hdb : (restrictToDivisor (T.withBoundary L₂) j₂ hj₂).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₂) hV₂ hcs₂ j₂ hj₂
      (lowerIdealWithoutBlowup (T.withBoundary L₂)) (lowerBoundaryWithoutBlowup (T.withBoundary L₂))) hdim₂
  exact isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq hbc hsh n L O hL T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    (lowerIdealWithoutBlowup (T.withBoundary L₁)) (lowerBoundaryWithoutBlowup (T.withBoundary L₁))
    (lowerIdealWithoutBlowup (T.withBoundary L₂)) (lowerBoundaryWithoutBlowup (T.withBoundary L₂))
    hI hE hVa hda hVb hdb

theorem isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hbc : SmoothPullbackCompatibility.{u}) (hsh : BoundaryReindexingInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁))
    (hV₁ : (T.withBoundary L₁).IsAdmissible)
    (hdim₁ : (T.withBoundary L₁).krullDimSucc ≤ n)
    (hO₁ : (T.withBoundary L₁).IsOrderBoundedByMult)
    (hDB₁ : (T.withBoundary L₁).IsBalanced hV₁.locallyOfFiniteType)
    (hcs₁ : (orderAtLeastLocus (T.withBoundary L₁).ideal (T.withBoundary L₁).mult).Nonempty)
    (hV₂ : (T.withBoundary L₂).IsAdmissible)
    (hdim₂ : (T.withBoundary L₂).krullDimSucc ≤ n)
    (hO₂ : (T.withBoundary L₂).IsOrderBoundedByMult)
    (hDB₂ : (T.withBoundary L₂).IsBalanced hV₂.locallyOfFiniteType)
    (hcs₂ : (orderAtLeastLocus (T.withBoundary L₂).ideal (T.withBoundary L₂).mult).Nonempty)
    (hZ : containedComponentsIdeal (T.withBoundary L₁) j₁ hj₁ ≠ ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ (lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁)
        (lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁) T.scheme (𝟙 T.scheme) (L₂.get ⟨j₂, hj₂⟩)
        (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq))
      (L (restrictTwistedToDivisor (T.withBoundary L₂) j₂ hj₂)).toSequenceOfBlowups
      (L (restrictTwistedToDivisor (T.withBoundary L₁) j₁ hj₁)).toSequenceOfBlowups := by
  have hZ₂ : containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂ ≠ ⊤ := by
    rw [← containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
    exact hZ
  have hI := eq_comap_id_of_eq (hsh.lowerIdealPre_shift T L₁ L₂ j₁ hj₁ j₂ hj₂ heq)
  have hE := sameNontrivialBoundary_map_comap_id (hsh.boundaryEquiv_restrictedBoundary_reindex T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE)
  have hVa : (restrictTwistedToDivisor (T.withBoundary L₁) j₁ hj₁).IsAdmissible :=
    hfacts.valid_lowerPre (T.withBoundary L₁) hV₁ hO₁ hDB₁ j₁ hj₁ hZ
  have hVb : (restrictTwistedToDivisor (T.withBoundary L₂) j₂ hj₂).IsAdmissible :=
    hfacts.valid_lowerPre (T.withBoundary L₂) hV₂ hO₂ hDB₂ j₂ hj₂ hZ₂
  have hda : (restrictTwistedToDivisor (T.withBoundary L₁) j₁ hj₁).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₁) hV₁ hcs₁ j₁ hj₁
      (lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁)
      (lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁)) hdim₁
  have hdb : (restrictTwistedToDivisor (T.withBoundary L₂) j₂ hj₂).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₂) hV₂ hcs₂ j₂ hj₂
      (lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂)
      (lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂)) hdim₂
  exact isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq hbc hsh n L O hL T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    (lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁) (lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁)
    (lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂) (lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂)
    hI hE hVa hda hVb hdb

structure StrictBoundaryReindexingInvariance (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ)
    (L : PrincipalizationAssignment.{u}) : Prop where
  isStrictPullbackSeq_divisorFamily :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (L₁ L₂ : List T.scheme.IdealSheafData)
      (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length),
      L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩ →
      MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁) →
      (T.withBoundary L₁).IsAdmissible → (T.withBoundary L₂).IsAdmissible →
      IsStrictPullbackBlowupSeq (𝟙 T.scheme)
        (((canonicalAlgorithmRules hres).divisorFamily L j₂ (T.withBoundary L₂)).toSequenceOfBlowups)
        (((canonicalAlgorithmRules hres).divisorFamily L j₁ (T.withBoundary L₁)).toSequenceOfBlowups)

theorem isBoundaryPositionInvariant_divisorFamily (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ)
    (L : PrincipalizationAssignment.{u}) (hsh : StrictBoundaryReindexingInvariance hres n L) :
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j := by
  refine ⟨?_⟩
  intro T hdim hO hft hbal E₁ E₂ E₁' E₂' D hBE1 hBE2 hV1 hV2
  have hlen1 : E₁.length < (E₁ ++ D :: E₂).length := by simp
  have hlen2 : E₁'.length < (E₁' ++ D :: E₂').length := by simp
  have hget : (E₁' ++ D :: E₂').get ⟨E₁'.length, hlen2⟩
      = (E₁ ++ D :: E₂).get ⟨E₁.length, hlen1⟩ := by
    rw [get_append_cons_length, get_append_cons_length]
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary ((E₁ ++ D :: E₂).eraseIdx E₁.length)
      ((E₁' ++ D :: E₂').eraseIdx E₁'.length) := by
    rw [eraseIdx_append_cons_length, eraseIdx_append_cons_length]
    exact hBE1.append hBE2
  have hmain := hsh.isStrictPullbackSeq_divisorFamily (T.withBoundary (E₁' ++ D :: E₂')) hV2
    hdim hO hbal (E₁' ++ D :: E₂') (E₁ ++ D :: E₂) E₁'.length hlen2 E₁.length hlen1
    hget hbe hV2 hV1
  exact isomorphic_of_isStrictPullbackAlongId _ _ hmain

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
