import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem map_comap_id {W : Scheme.{u}} (l : List W.IdealSheafData) :
    List.map (fun D : W.IdealSheafData => D.comap (𝟙 W)) l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [Scheme.IdealSheafData.comap_id]

private theorem take_eraseIdx_append_singleton {α : Type*} (A : List α) (e : α) (j n : ℕ)
    (hj : j < A.length) (hn : n = A.length - 1) :
    List.take n ((A ++ [e]).eraseIdx j) = A.eraseIdx j := by
  subst hn
  have hlen : (A.eraseIdx j).length = A.length - 1 := by
    rw [List.length_eraseIdx, if_pos hj]
  rw [List.eraseIdx_append_of_lt_length hj, ← hlen, List.take_left]

private theorem take_length_sub_one_eraseIdx {α : Type*} (A : List α) (j n : ℕ) (hj : j < A.length)
    (hn : n = A.length - 1) : List.take n (A.eraseIdx j) = A.eraseIdx j := by
  subst hn
  refine List.take_of_length_le ?_
  rw [List.length_eraseIdx, if_pos hj]

private theorem top_pow {Y : Scheme.{u}} (m : ℕ) :
    (⊤ : Y.IdealSheafData) ^ m = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

private theorem residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A F : X.IdealSheafData) (F' : Y.IdealSheafData) (m : ℕ) (hF' : F' = F.comap g)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor F') (hex : ∃ B : X.IdealSheafData, F ^ m * B = A) :
    residualByPow (A.comap g) F' m = (residualByPow A F m).comap g := by
  have hdown : F ^ m * residualByPow A F m = A := pow_mul_residualByPow A F m hex
  have hup : F' ^ m * (residualByPow A F m).comap g = A.comap g := by
    rw [hF', ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul, hdown]
  have hup2 : F' ^ m * residualByPow (A.comap g) F' m = A.comap g :=
    pow_mul_residualByPow (A.comap g) F' m ⟨_, hup⟩
  exact (hcart.pow m).eq_of_mul_eq_mul (hup2.trans hup.symm)

private theorem sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hX : AlgebraicGeometry.IsNoetherian X) (hY : AlgebraicGeometry.IsNoetherian Y)
    (hflat : AlgebraicGeometry.Flat g)
    (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (Z' : Y.IdealSheafData) (hZ' : Z' = Z.comap g)
    (B : List X.IdealSheafData) (E : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap g) B) E)
    (j : ℕ) (hj : j < B.length) (hjE : j < E.length)
    (htake : List.take (j + 1) E = List.take (j + 1) (List.map (fun D => D.comap g) B)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 Y) Z') (List.map (fun D => D.comap (𝟙 Y)) E)
          ++ [Blowup.exceptionalIdeal (𝟙 Y) Z']).eraseIdx j))
      (List.map (fun D => D.comap g)
        (List.take (B.length - 1)
          ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
            ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx j))) := by
  have := hX
  have := hY
  have := hflat
  subst hZ'
  have hst : ∀ D : X.IdealSheafData,
      (Blowup.strictTransform (𝟙 X) Z D).comap g
        = Blowup.strictTransform (𝟙 Y) (Z.comap g) (D.comap g) := fun D =>
    comap_strictTransform_of_flat_of_isLocallyNoetherian (𝟙 X) g (𝟙 Y) g
      (CategoryTheory.IsPullback.id_vert g) Z D hZ
  have hcomp : List.map ((fun D : X.IdealSheafData => D.comap g)
        ∘ Blowup.strictTransform (𝟙 X) Z) B
      = List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
          (List.map (fun D : X.IdealSheafData => D.comap g) B) := by
    rw [List.map_map]
    exact List.map_congr_left (fun D _ => hst D)
  rw [map_comap_id, map_comap_id,
    take_eraseIdx_append_singleton (List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g)) E)
      (Blowup.exceptionalIdeal (𝟙 Y) (Z.comap g)) j (E.length - 1) (by simpa using hjE) (by simp),
    take_eraseIdx_append_singleton (List.map (Blowup.strictTransform (𝟙 X) Z) B)
      (Blowup.exceptionalIdeal (𝟙 X) Z) j (B.length - 1) (by simpa using hj) (by simp),
    ← List.eraseIdx_map, List.map_map, hcomp]
  refine ((MarkedIdealWithBoundary.SameNontrivialBoundary.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
    (strictTransform_top (𝟙 Y) (Z.comap g)) hBE).eraseIdx j ?_).symm
  rw [← List.map_take, ← List.map_take, ← List.map_take, htake, List.map_take]

theorem lowerIdealAfterBlowup_pullbackAlong_of_smooth
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (lowerIdealAfterBlowup T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hOx : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).1 hO
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hOx j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) := by
    have hb := hblow ((T.pullbackAlong Y q h).withBoundary E') hV' j hjE
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hb
    rwa [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor h T.ideal (containedComponentsIdeal T j hj)
      (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) T.mult hpre hcart hex
  simp only [lowerIdealAfterBlowup, Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact key

theorem lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              MarkedIdealWithBoundary.SameNontrivialBoundary
                (List.take (E'.length - 1)
                  ((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).eraseIdx j))
                (List.map (fun D => D.comap h)
                  (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hsmooth : AlgebraicGeometry.Smooth h := hsm
  have hbdry : (T.pullbackAlong Y q h).boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h
  rw [hbdry] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat h hV.isNoetherian hV'.isNoetherian inferInstance
    (containedComponentsIdeal T j hj) (hblow T hV j hj)
    (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) hpre
    T.boundary E' hBE j hj hjE htake

theorem comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (_hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    (lowerIdealAfterBlowup T j hj).comap h = (lowerIdealWithoutBlowup T).comap h := by
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hdown : containedComponentsIdeal T j hj ^ T.mult * residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult = T.ideal :=
    pow_mul_residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult hex
  have hup := congrArg (fun I : T.scheme.IdealSheafData => I.comap h) hdown
  simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, htop,
    top_pow, Scheme.IdealSheafData.top_mul] at hup
  simp only [lowerIdealAfterBlowup, lowerIdealWithoutBlowup, Blowup.exceptionalIdeal_eq_comap,
    Scheme.IdealSheafData.comap_id]
  exact hup

theorem comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (_hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  have hnoT : AlgebraicGeometry.IsNoetherian T.scheme := hV.isNoetherian
  have hstT : ∀ D : T.scheme.IdealSheafData,
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj) D).comap h = D.comap h := by
    intro D
    have hg : ((containedComponentsIdeal T j hj).comap (𝟙 T.scheme)).comap h = ⊤ := by
      rw [Scheme.IdealSheafData.comap_id]; exact htop
    have h2 := strictTransform_comap_of_comap_center_eq_top (𝟙 T.scheme) (containedComponentsIdeal T j hj) D h hg
    rw [h2, Scheme.IdealSheafData.comap_id]
  have hR0 : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
          (List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary)
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := rfl
  have hR : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := by
    rw [hR0, map_comap_id]
  have key : List.map (fun D : T.scheme.IdealSheafData => D.comap h)
        ((List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j)
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) (T.boundary.eraseIdx j) := by
    rw [← List.eraseIdx_map, ← List.eraseIdx_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun D _ => hstT D)
  rw [hR, lowerBoundaryWithoutBlowup_eq T,
    take_eraseIdx_append_singleton
      (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary)
      (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) j (T.boundary.length - 1)
      (by simpa using hj) (by simp),
    take_length_sub_one_eraseIdx T.boundary j (T.boundary.length - 1) hj rfl, key]
  exact MonomialCenter.sameNontrivialBoundary_refl _

theorem lowerIdealAfterBlowup_fieldBaseChange
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.baseChange K f).boundary)
    (hjE : j < E'.length)
    (_htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hpre : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)) :
    lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE =
      (lowerIdealAfterBlowup T j hj).comap (fieldBaseChangeProjection T K f) := by
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) := by
    have hb := hblow ((T.baseChange K f).withBoundary E') hV' j hjE
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hb
    rwa [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor (fieldBaseChangeProjection T K f) T.ideal
      (containedComponentsIdeal T j hj)
      (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) T.mult hpre hcart hex
  simp only [lowerIdealAfterBlowup, Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact key

theorem lowerBoundaryAfterBlowup_fieldBaseChange
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.baseChange K f).boundary)
    (hjE : j < E'.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hpre : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE).eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) := by
  have hbdry : (T.baseChange K f).boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap (fieldBaseChangeProjection T K f))
          T.boundary := MarkedIdealWithBoundary.baseChange_boundary T K f
  rw [hbdry] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat (fieldBaseChangeProjection T K f) hV.isNoetherian
    hV'.isNoetherian inferInstance
    (containedComponentsIdeal T j hj) (hblow T hV j hj)
    (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) hpre
    T.boundary E' hBE.symm j hj hjE htake

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
