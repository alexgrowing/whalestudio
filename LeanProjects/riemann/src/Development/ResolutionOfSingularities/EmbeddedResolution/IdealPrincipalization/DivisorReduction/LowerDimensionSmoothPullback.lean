import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyPulledBackCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

def PullbackSmoothOfDimLT (n : ℕ) (L : PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc < n →
        IsPullbackBlowupSequence h (L ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
          (L T).toSequenceOfBlowups

theorem pullbackSmoothOfDimLT_of_isMaxOrderReduction (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) : PullbackSmoothOfDimLT n L := by
  intro T hV hdim Y q h hsm hq E' hBE hV' hdim'
  have := hsm
  exact hL.smooth_pullback T hV hdim Y q h hq E' hBE hV' hdim'

theorem isPullbackSequenceOfBlowups_of_length_eq_zero (X X' : Scheme.{u}) (φ : X' ⟶ X) (B' : SequenceOfBlowups X')
    (B : SequenceOfBlowups X) (hB' : B'.length = 0) (hB : B.length = 0) : IsPullbackBlowupSequence φ B' B := by
  unfold IsPullbackBlowupSequence
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero => exact B'.isoZero ≪≫ (asIso (Limits.pullback.fst φ (B.projectionToBase 0))).symm
    | succ k => exact absurd hi (by rw [hB']; exact Nat.not_succ_le_zero k)
  · intro i hi
    rw [hB'] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i k hk hik
    rw [hB'] at hk
    exact absurd hik (by omega)
  · exact hB.symm
  · intro i hi
    rw [hB] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · rintro (_ | k) hi
    · show (B'.isoZero ≪≫ (asIso (Limits.pullback.fst φ (B.projectionToBase 0))).symm).hom ≫
          Limits.pullback.fst φ (B.projectionToBase 0) = B'.projectionToBase 0
      simp [SequenceOfBlowups.projectionToBase_zero]
    · exact absurd hi (by rw [hB']; exact Nat.not_succ_le_zero k)
  · intro i hi _
    exact absurd hi (by rw [hB']; exact Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (by rw [hB']; exact Nat.not_lt_zero i)

private theorem forall_ofSequenceOfBlowups_transitionMap_eq {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    ∀ (j i : ℕ) (h : i ≤ j), (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h = s.transitionMap h := by
  intro j
  induction j with
  | zero =>
    intro i h
    have hi : i = 0 := Nat.le_zero.mp h
    subst hi
    exact (SequenceOfBlowups.transitionMap_self _ h).trans (SequenceOfBlowups.transitionMap_self s h).symm
  | succ k ih =>
    intro i h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq
      exact (SequenceOfBlowups.transitionMap_self _ h).trans (SequenceOfBlowups.transitionMap_self s h).symm
    · have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
      have hb : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (Nat.le_succ k) = s.transitionMap (Nat.le_succ k) := by
        have e1 : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMapSucc k = s.transitionMapSucc k :=
          (BlowupSequenceData.toSequenceOfBlowups_blowupMorphism (BlowupSequenceData.ofSequenceOfBlowups s) k).trans (BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism s k)
        exact ((SequenceOfBlowups.blowupMorphism_eq_transitionMap _ k).symm.trans e1).trans
          (SequenceOfBlowups.blowupMorphism_eq_transitionMap s k)
      have E1 : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h
          = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (Nat.le_succ k) ≫
            (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap hik :=
        (SequenceOfBlowups.transitionMap_trans _ hik (Nat.le_succ k)).symm
      have E2 : s.transitionMap h = s.transitionMap (Nat.le_succ k) ≫ s.transitionMap hik :=
        (SequenceOfBlowups.transitionMap_trans s hik (Nat.le_succ k)).symm
      have c1 := congrArg (fun g => g ≫ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap hik) hb
      have c2 := congrArg (fun g => s.transitionMap (Nat.le_succ k) ≫ g) (ih i hik)
      exact E1.trans ((c1.trans c2).trans E2.symm)

private theorem ofSequenceOfBlowups_transitionMap {X : Scheme.{u}} (s : SequenceOfBlowups X) {i j : ℕ} (h : i ≤ j) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h = s.transitionMap h :=
  forall_ofSequenceOfBlowups_transitionMap_eq s j i h

private theorem ofSequenceOfBlowups_tower {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.tower = s.tower := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  have hf : (homOfLE (leOfHom f.unop)).op = f :=
    congrArg (fun g => Quiver.Hom.op g) (homOfLE_leOfHom f.unop)
  have h1 : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.tower.map f
      = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (leOfHom f.unop) := by
    rw [SequenceOfBlowups.transitionMap_def, hf]
  have h2 : s.tower.map f = s.transitionMap (leOfHom f.unop) := by
    rw [SequenceOfBlowups.transitionMap_def, hf]
  have key : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.tower.map f = s.tower.map f :=
    h1.trans ((ofSequenceOfBlowups_transitionMap s (leOfHom f.unop)).trans h2.symm)
  have hid : s.tower.map f
      = 𝟙 (s.tower.obj a) ≫ s.tower.map f ≫ 𝟙 (s.tower.obj b) := by
    simp
  exact key.trans hid

private theorem sequenceOfBlowups_eq_of_tower_eq {X : Scheme.{u}} (s t : SequenceOfBlowups X)
    (ht : s.tower = t.tower) (hl : s.length = t.length)
    (hiso : HEq s.isoZero t.isoZero) (hc : HEq s.center t.center) : s = t := by
  obtain ⟨l₁, F, i₁, c₁, b₁⟩ := s
  obtain ⟨l₂, G, i₂, c₂, b₂⟩ := t
  have hl' : l₁ = l₂ := hl
  have ht' : F = G := ht
  subst hl'
  subst ht'
  have hiso' : HEq i₁ i₂ := hiso
  have hc' : HEq c₁ c₂ := hc
  obtain rfl := eq_of_heq hiso'
  obtain rfl := eq_of_heq hc'
  rfl

private theorem ofSequenceOfBlowups_toSequenceOfBlowups {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups = s :=
  sequenceOfBlowups_eq_of_tower_eq _ _ (ofSequenceOfBlowups_tower s) rfl (HEq.refl _) (HEq.refl _)

theorem isPullbackBlowupSequence_ofMarkedSequence (A B : MarkedIdealWithBoundary.{u})
    (φ : A.scheme ⟶ B.scheme) (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups)
    (hs : IsPullbackBlowupSequence φ sA.toSequenceOfBlowups sB.toSequenceOfBlowups) :
    IsPullbackBlowupSequence φ (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups
      (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups := by
  have hA : (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups = sA.toSequenceOfBlowups :=
    ofSequenceOfBlowups_toSequenceOfBlowups _
  have hB : (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups = sB.toSequenceOfBlowups :=
    ofSequenceOfBlowups_toSequenceOfBlowups _
  rw [hA, hB]
  exact hs

private theorem markedIdealWithBoundary_mk_ideal_congr {k : Type u} [inst : Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ} {E : List X.IdealSheafData}
    {I₁ I₂ : X.IdealSheafData} (hI : I₁ = I₂) :
    (@MarkedIdealWithBoundary.mk k inst X p I₁ m E) = (@MarkedIdealWithBoundary.mk k inst X p I₂ m E) := by
  rw [hI]

private theorem isPullbackSequenceOfBlowups_apply_congr (L : PrincipalizationAssignment.{u})
    {X : Scheme.{u}} (B : SequenceOfBlowups X) (S S' : MarkedIdealWithBoundary.{u}) (hS : S = S')
    (φ : S.scheme ⟶ X) (φ' : S'.scheme ⟶ X) (hφ : HEq φ φ')
    (hpb : IsPullbackBlowupSequence φ (L S).toSequenceOfBlowups B) :
    IsPullbackBlowupSequence φ' (L S').toSequenceOfBlowups B := by
  subst hS
  have hee : φ = φ' := eq_of_heq hφ
  subst hee
  exact hpb

private theorem isPullbackBlowupSequence_restrictToBoundaryDivisor (n : ℕ) (L : PrincipalizationAssignment.{u})
    (hL : PullbackSmoothOfDimLT n L) (hbc : DivisorReduction.SmoothPullbackCompatibility.{u})
    (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    (hsm : AlgebraicGeometry.Smooth h) (hq : h ≫ T.structMap = q)
    (E' : List Y.IdealSheafData) (hjE : j < E'.length)
    (hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h)
    (I₀' : Y.IdealSheafData) (E₀' : List Y.IdealSheafData)
    (hI : I₀' = I₀.comap h)
    (hEq : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1) (E₀'.eraseIdx j))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) (E₀.eraseIdx j))))
    (hadmissible : (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hdS : (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < n)
    (hVS' : (DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE
      I₀' E₀').IsAdmissible)
    (hdS' : (DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE
      I₀' E₀').krullDimSucc < n) :
    IsPullbackBlowupSequence (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)
      (L (DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE
        I₀' E₀')).toSequenceOfBlowups
      (L (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups := by
  have := hsm
  have hsm0 : AlgebraicGeometry.Smooth
      (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme Y (T.boundary.get ⟨j, hj⟩).subscheme
      (E'.get ⟨j, hjE⟩).subscheme (T.boundary.get ⟨j, hj⟩).subschemeι
      (E'.get ⟨j, hjE⟩).subschemeι h
      (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)
      ((hbc.isPullback_inducedHom T.scheme Y h (T.boundary.get ⟨j, hj⟩)
        (E'.get ⟨j, hjE⟩) hD).flip) hsm
  have hic : (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      (T.boundary.get ⟨j, hj⟩).subschemeι = (E'.get ⟨j, hjE⟩).subschemeι ≫ h :=
    DivisorReduction.subschemeMapOfComap_comp h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
  have a1 : (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      = ((DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
        (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    (Category.assoc _ _ _).symm
  have a2 : ((DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = ((E'.get ⟨j, hjE⟩).subschemeι ≫ h) ≫ T.structMap :=
    congrArg (fun g => g ≫ T.structMap) hic
  have a3 : ((E'.get ⟨j, hjE⟩).subschemeι ≫ h) ≫ T.structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ (h ≫ T.structMap) := Category.assoc _ _ _
  have a4 : (E'.get ⟨j, hjE⟩).subschemeι ≫ (h ≫ T.structMap)
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q :=
    congrArg (fun g => (E'.get ⟨j, hjE⟩).subschemeι ≫ g) hq
  have hq₀ : (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q :=
    a1.trans (a2.trans (a3.trans a4))
  have hIdeal : ((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).ideal).comap
      (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)
      = I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι := by
    rw [hI]
    exact DivisorReduction.comap_subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD I₀
  have heq : (((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))
      = DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE I₀' E₀' :=
    markedIdealWithBoundary_mk_ideal_congr hIdeal
  have hBE₀ : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).boundary)
      (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
        (List.take (E'.length - 1) (E₀'.eraseIdx j))) :=
    (DivisorReduction.sameNontrivialBoundary_comap_subschemeι h (T.boundary.get ⟨j, hj⟩)
      (E'.get ⟨j, hjE⟩) hD (List.take (T.boundary.length - 1) (E₀.eraseIdx j))
      (List.take (E'.length - 1) (E₀'.eraseIdx j)) hEq).symm
  have hV₀ : ((((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))).IsAdmissible := by
    rw [heq]; exact hVS'
  have hd₀ : ((((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))).krullDimSucc < n := by
    rw [heq]; exact hdS'
  have hmain := hL (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀) hadmissible hdS
    (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
    (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) hq₀
    (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
      (List.take (E'.length - 1) (E₀'.eraseIdx j))) hBE₀ hV₀ hd₀
  exact isPullbackSequenceOfBlowups_apply_congr L
    (L (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups _ _ heq _ _
    (HEq.refl (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)) hmain

theorem restrictedSmoothPullback_of_pullbackSmoothOfDimLT
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u})
    (hdt : DivisorReduction.EmptyPulledBackCenterCompatibility.{u})
    (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (hL : PullbackSmoothOfDimLT n L) :
    DivisorReduction.RestrictedPrincipalizationSmoothPullback n L j := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hV hdim hO hbal hj hcs Y q h hsm hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZc
      hZ'
    have := hsm
    have hIc : DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')
        = (DivisorReduction.lowerIdealAfterBlowup T j hj).comap h := by
      rw [DivisorReduction.lowerIdealWithoutBlowup_withBoundary T Y q h E']
      exact (hdt.lowerIdealPre_comap_eq_lowerIdealTop_comap T hV hO j hj Y h hZc).symm
    have hEc : MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (E'.length - 1)
          ((DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).eraseIdx j))
        (List.map (fun D => D.comap h)
          (List.take (T.boundary.length - 1)
            ((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j))) :=
      (DivisorReduction.sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE).trans
        (hdt.boundaryEquiv_restrictedBoundary_comap_of_center_comap_eq_top T hV j hj Y h hZc).symm
    exact isPullbackBlowupSequence_restrictToBoundaryDivisor n L hL hbc T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
      (DivisorReduction.lowerBoundaryAfterBlowup T j hj) Y q h hsm hq E' hjE
      (DivisorReduction.get_eq_comap_get_boundary T j hj Y q h E' hjE htake)
      (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      hIc hEc
      (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj
        (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim)
      (hfacts.valid_lowerTop ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ')
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E')
        hV' hcs' j hjE
        (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
        (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))) hdim')
  · intro T hV hdim hO hbal hj hcs Y q h hsm hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    have := hsm
    exact isPullbackBlowupSequence_restrictToBoundaryDivisor n L hL hbc T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
      (DivisorReduction.lowerBoundaryWithoutBlowup T) Y q h hsm hq E' hjE
      (DivisorReduction.get_eq_comap_get_boundary T j hj Y q h E' hjE htake)
      (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      (DivisorReduction.lowerIdealWithoutBlowup_withBoundary T Y q h E')
      (DivisorReduction.sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE)
      (hfacts.valid_lowerTop T hV hO hbal j hj hZ)
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)) hdim)
      (hfacts.valid_lowerTop ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ')
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E')
        hV' hcs' j hjE
        (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
        (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))) hdim')
  · intro T hV hdim hO hbal hj hcs Y q h hsm hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZc
      hZ'
    have := hsm
    have hZ'' : DivisorReduction.containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE ≠ ⊤ := by
      rw [hZ']; exact hZc
    exact isPullbackBlowupSequence_restrictToBoundaryDivisor n L hL hbc T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
      (DivisorReduction.lowerBoundaryAfterBlowup T j hj) Y q h hsm hq E' hjE
      (DivisorReduction.get_eq_comap_get_boundary T j hj Y q h E' hjE htake)
      (DivisorReduction.lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
      (DivisorReduction.lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
      (hbc.lowerIdealPre_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ')
      (hbc.boundaryEquiv_restrictedBoundary_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ')
      (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj
        (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim)
      (hfacts.valid_lowerPre ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ'')
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E')
        hV' hcs' j hjE
        (DivisorReduction.lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
        (DivisorReduction.lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)) hdim')

theorem restrictedSmoothPullback_of_isMaxOrderReduction
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u})
    (hdt : DivisorReduction.EmptyPulledBackCenterCompatibility.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    DivisorReduction.RestrictedPrincipalizationSmoothPullback n L j :=
  restrictedSmoothPullback_of_pullbackSmoothOfDimLT hres hfacts hbc hdt n L j
    (pullbackSmoothOfDimLT_of_isMaxOrderReduction n L O hL)

theorem pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ)
    (hdel : ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (_hj : j < T.boundary.length)
      (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h],
      h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        (orderAtLeastLocus T.ideal T.mult).Nonempty →
        orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
        ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
          IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)) :
    DivisorReduction.IsPullbackSeqOfEmptyBlowupSeq hres L j :=
  { isPullbackSeq_of_coSupport_empty := hdel
    isPullbackSeq_of_length_eq_zero := fun X X' φ B' B hB' hB =>
      isPullbackSequenceOfBlowups_of_length_eq_zero X X' φ B' B hB' hB
    isPullbackSeq_ofMarkedSeq := fun A B φ sA sB hs =>
      isPullbackBlowupSequence_ofMarkedSequence A B φ sA sB hs }

end FunctorialResolution.EmbeddedResolution
