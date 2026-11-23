import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BoundarySeparationByMaxContact

def BoundarySeparated (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (n : ℕ) : Prop :=
  ∀ (i : ℕ), i < n → ∀ hi : i < (s.boundary s.length).length,
    orderAtLeastLocus (s.ideal s.length) S.mult ∩
        ((((s.boundary s.length).get ⟨i, hi⟩).support : Set ↥(s.obj s.length))) = ∅

def SeparateBoundaryInvariant (S : MarkedIdealWithBoundary.{u}) (H : S.scheme.IdealSheafData)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (n : ℕ) : Prop :=
  BoundarySeparated S s n ∧ (∀ i < s.length, s.center i ≠ ⊤) ∧
    InStrictNormalCrossingPosition (s.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform s H 0]

private theorem ne_top_of_support_nonempty {X : Scheme.{u}} {J : X.IdealSheafData}
    (h : ((J.support : Set ↥X)).Nonempty) : J ≠ ⊤ := by
  intro hc
  obtain ⟨x, hx⟩ := h
  rw [hc] at hx
  have h1 : (1 : ℕ∞) ≤ orderAt (⊤ : X.IdealSheafData) x :=
    (one_le_orderAt_iff_mem_support (⊤ : X.IdealSheafData) x).2 hx
  rw [orderAt_top] at h1
  exact absurd h1 (by simp)

private theorem comap_hom_ne_top_of_ne_top {X Y : Scheme.{u}} (e : X ≅ Y) (J : Y.IdealSheafData)
    (hJ : J ≠ ⊤) : J.comap e.hom ≠ ⊤ := by
  have hs : ((J.support : Set ↥Y)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    exact hJ ((AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty J).2 hc)
  obtain ⟨y, hy⟩ := hs
  have h2 : e.hom (e.inv y) = y := by simp
  have h3 : e.hom.base (e.inv.base y) ∈ J.support := by
    rw [show e.hom.base (e.inv.base y) = y from h2]
    exact hy
  have h4 : e.inv.base y ∈ (J.comap e.hom).support :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.2 h3
  exact ne_top_of_support_nonempty ⟨e.inv.base y, h4⟩

private theorem comap_eqToHom_ne_top {X Y : Scheme.{u}} (h : X = Y)
    (J : Y.IdealSheafData) (hJ : J ≠ ⊤) : J.comap (eqToHom h) ≠ ⊤ :=
  comap_hom_ne_top_of_ne_top (eqToIso h) J hJ

private theorem comap_iso_inv_ne_top {X Y : Scheme.{u}} (e : X ≅ Y)
    (J : X.IdealSheafData) (hJ : J ≠ ⊤) : J.comap e.inv ≠ ⊤ :=
  comap_hom_ne_top_of_ne_top e.symm J hJ

private theorem orderAtLeastLocus_inter_support_eq_empty_of_eq {X : Scheme.{u}} {I I' D D' : X.IdealSheafData}
    {m : ℕ} (hI : I = I') (hD : D = D')
    (h : orderAtLeastLocus I' m ∩ (D'.support : Set ↥X) = ∅) :
    orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅ := by
  subst hI
  subst hD
  exact h

private theorem orderAtLeastLocus_comap_iso_inter_support_eq_empty {X Y : Scheme.{u}} (hinv : ComapIsoInvariance.{u})
    (e : X ≅ Y) (I D : Y.IdealSheafData) (m : ℕ)
    (h : orderAtLeastLocus I m ∩ (D.support : Set ↥Y) = ∅) :
    orderAtLeastLocus (I.comap e.hom) m ∩ ((D.comap e.hom).support : Set ↥X) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hx1, hx2⟩
  rw [hinv.coSupport_comap e I m] at hx1
  have hx2c : x ∈ (D.comap e.hom).support := hx2
  have hx2' : e.hom.base x ∈ D.support :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hx2c
  have hmem : e.hom.base x ∈ orderAtLeastLocus I m ∩ (D.support : Set ↥Y) := ⟨hx1, hx2'⟩
  rw [h] at hmem
  exact hmem

private theorem orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty {X Y : Scheme.{u}} (hinv : ComapIsoInvariance.{u})
    (h : X = Y) (I D : Y.IdealSheafData) (m : ℕ)
    (hsep : orderAtLeastLocus I m ∩ (D.support : Set ↥Y) = ∅) :
    orderAtLeastLocus (I.comap (eqToHom h)) m ∩ ((D.comap (eqToHom h)).support : Set ↥X) = ∅ :=
  orderAtLeastLocus_comap_iso_inter_support_eq_empty hinv (eqToIso h) I D m hsep

private theorem orderAtLeastLocus_inter_support_eq_empty_of_comap_iso {X Y : Scheme.{u}} (hinv : ComapIsoInvariance.{u})
    (e : X ≅ Y) (I D : Y.IdealSheafData) (m : ℕ)
    (h : orderAtLeastLocus (I.comap e.hom) m ∩ ((D.comap e.hom).support : Set ↥X) = ∅) :
    orderAtLeastLocus I m ∩ (D.support : Set ↥Y) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hy1, hy2⟩
  have h2 : e.hom (e.inv y) = y := by simp
  have k1 : e.inv.base y ∈ orderAtLeastLocus (I.comap e.hom) m := by
    rw [hinv.coSupport_comap e I m]
    show e.hom.base (e.inv.base y) ∈ orderAtLeastLocus I m
    rw [show e.hom.base (e.inv.base y) = y from h2]
    exact hy1
  have k2 : e.inv.base y ∈ ((D.comap e.hom).support : Set ↥X) := by
    have hy2' : e.hom.base (e.inv.base y) ∈ D.support := by
      rw [show e.hom.base (e.inv.base y) = y from h2]
      exact hy2
    exact AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.2 hy2'
  have hmem : e.inv.base y ∈
      orderAtLeastLocus (I.comap e.hom) m ∩ ((D.comap e.hom).support : Set ↥X) := ⟨k1, k2⟩
  rw [h] at hmem
  exact hmem

private theorem getElem_eq_of_list_eq {α : Type*} {L L' : List α} (h : L = L') (n : ℕ)
    (hn : n < L.length) (hn' : n < L'.length) : L[n]'hn = L'[n]'hn' := by
  subst h
  rfl

private theorem getElem_map_of_lt {α β : Type*} (f : α → β) :
    ∀ (L : List α) (n : ℕ) (hn : n < L.length) (hn' : n < (L.map f).length),
      (L.map f)[n]'hn' = f (L[n]'hn) := by
  intro L
  induction L with
  | nil =>
      intro n hn _
      exact absurd hn (Nat.not_lt_zero n)
  | cons a L ih =>
      intro n hn hn'
      cases n with
      | zero => rfl
      | succ r =>
          have h1 : r < L.length := by
            simp only [List.length_cons] at hn
            omega
          have h2 : r < (L.map f).length := by
            simp only [List.length_map, List.length_cons] at hn' ⊢
            omega
          exact ih r h1 h2

private theorem getElem_map_append_of_lt {α β : Type*} (f : α → β) :
    ∀ (L : List α) (R : List β) (n : ℕ) (hn : n < L.length)
      (hn' : n < (L.map f ++ R).length), (L.map f ++ R)[n]'hn' = f (L[n]'hn) := by
  intro L
  induction L with
  | nil =>
      intro R n hn _
      exact absurd hn (Nat.not_lt_zero n)
  | cons a L ih =>
      intro R n hn hn'
      cases n with
      | zero => rfl
      | succ r =>
          have h1 : r < L.length := by
            simp only [List.length_cons] at hn
            omega
          have h2 : r < (L.map f ++ R).length := by
            simp only [List.length_append, List.length_map, List.length_cons] at hn' ⊢
            omega
          exact ih R r h1 h2

private theorem boundary_getElem_eq_iteratedStrictTransform {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (u : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ u.length) (n : ℕ) (hn : n < E.length)
    (hn' : n < (u.boundary i).length) :
    (u.boundary i)[n]'hn' = u.iteratedStrictTransform i (E[n]'hn) := by
  have h1 : u.boundary i = E.map (u.iteratedStrictTransform i) ++ u.boundaryFrom ([] : List X.IdealSheafData) i := by
    rw [← MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq u i hi]
    exact BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append u.toBlowupSequenceData E i
  have h2 : n < (E.map (u.iteratedStrictTransform i) ++ u.boundaryFrom ([] : List X.IdealSheafData) i).length := by
    rw [← h1]
    exact hn'
  rw [getElem_eq_of_list_eq h1 n hn' h2]
  exact getElem_map_append_of_lt (u.iteratedStrictTransform i) E
    (u.boundaryFrom ([] : List X.IdealSheafData) i) n hn h2

private theorem orderAtLeastLocus_append_succ_subset_preimage (hstar : MaxContactCoverProperties.{u}) {k : Type u} [Field k]
    {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (r : ℕ) (hr : r < (s.append t hinv).length) :
    orderAtLeastLocus ((s.append t hinv).ideal (r + 1)) m ⊆
      ⇑((s.append t hinv).map r) ⁻¹' orderAtLeastLocus ((s.append t hinv).ideal r) m := by
  have hlen := MarkedBlowupSequenceData.append_length s t hinv
  have hrlen : r < (s.appendToBlowupSequenceData t).length := by
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_length]
    omega
  have hb : Blowup.IsBlowupAlongIdealSheaf ((s.append t hinv).map r) ((s.append t hinv).center r) :=
    (s.append t hinv).isBlowup r hr
  have heq : Blowup.exceptionalIdeal ((s.append t hinv).map r) ((s.append t hinv).center r) ^ m *
      (s.append t hinv).ideal (r + 1)
        = ((s.append t hinv).ideal r).comap ((s.append t hinv).map r) :=
    MarkedBlowupSequenceData.exceptionalIdeal_pow_mul_appendIdeal_succ s t hinv r hrlen
  have hsupp : (((s.append t hinv).center r).support : Set ↥((s.append t hinv).obj r)) ⊆
      orderAtLeastLocus ((s.append t hinv).ideal r) m :=
    MarkedBlowupSequenceData.center_support_subset_orderAtLeastLocus_appendIdeal s t hinv r hrlen
  exact hstar.coSupport_le_preimage ((s.append t hinv).map r) ((s.append t hinv).center r) hb
    ((s.append t hinv).ideal r) ((s.append t hinv).ideal (r + 1)) m heq hsupp

private theorem separateBoundaryInvariant_append (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (S : MarkedIdealWithBoundary.{u}) (H : S.scheme.IdealSheafData) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
      (s.boundary s.length))
    (j : ℕ) (hj : j < S.boundary.length) (hbj : j < (s.boundary s.length).length)
    (hfacts : SeparateBoundaryInvariant S H s j)
    (hN : ∀ i, i ≤ t.length → AlgebraicGeometry.IsLocallyNoetherian (t.obj i))
    (K : ∀ r : ℕ, (t.obj r).IdealSheafData)
    (h0 : K 0 = ((s.boundary s.length)[j]'hbj).comap t.isoZero.hom)
    (hstep : ∀ r, r < t.length →
      K (r + 1) = Blowup.strictTransform (t.map r) (t.center r) (K r) ∨
        K (r + 1) = (K r).comap (t.map r))
    (hsepK : ∀ r, r = t.length →
      orderAtLeastLocus (t.ideal r) S.mult ∩ ((K r).support : Set ↥(t.obj r)) = ∅)
    (hcent : ∀ r, r < t.length → t.center r ≠ ⊤) :
    SeparateBoundaryInvariant S H (s.append t hinv) (j + 1) := by
  have hsub : ∀ r, r ≤ t.length →
      ((t.iteratedStrictTransform r ((s.boundary s.length)[j]'hbj)).support : Set ↥(t.obj r)) ⊆
        ((K r).support : Set ↥(t.obj r)) := by
    intro r hr
    exact BlowupSequenceData.support_iteratedStrictTransform_subset_support t.toBlowupSequenceData hN
      ((s.boundary s.length)[j]'hbj) K h0 hstep r hr
  have hsepT : ∀ r, r ≤ t.length →
      orderAtLeastLocus (t.ideal r) S.mult ∩ ((K r).support : Set ↥(t.obj r)) = ∅ →
      orderAtLeastLocus (t.ideal r) S.mult ∩
        ((t.iteratedStrictTransform r ((s.boundary s.length)[j]'hbj)).support : Set ↥(t.obj r)) = ∅ := by
    intro r hr hsep
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx1, hx2⟩
    have hmem : x ∈ orderAtLeastLocus (t.ideal r) S.mult ∩ ((K r).support : Set ↥(t.obj r)) :=
      ⟨hx1, hsub r hr hx2⟩
    rw [hsep] at hmem
    exact hmem
  have hulen : (s.append t hinv).length = s.length + t.length :=
    MarkedBlowupSequenceData.append_length s t hinv
  have hsle : s.length ≤ (s.append t hinv).length := by omega
  have hdesc : ∀ r, r < (s.append t hinv).length →
      orderAtLeastLocus ((s.append t hinv).ideal (r + 1)) S.mult ⊆
        ⇑((s.append t hinv).map r) ⁻¹' orderAtLeastLocus ((s.append t hinv).ideal r) S.mult :=
    fun r hr => orderAtLeastLocus_append_succ_subset_preimage hstar s t hinv r hr
  have hblenU : ∀ r, r ≤ (s.append t hinv).length →
      ((s.append t hinv).boundary r).length = S.boundary.length + r :=
    fun r hr => MarkedBlowupSequenceData.boundary_length (s.append t hinv) r hr
  have hobj0 : (s.appendToBlowupSequenceData t).obj s.length = s.obj s.length :=
    MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.length)
  have hid0 : (s.append t hinv).ideal s.length = (s.ideal s.length).comap (eqToHom hobj0) := by
    rw [MarkedBlowupSequenceData.append_ideal s t hinv s.length,
      MarkedBlowupSequenceData.appendIdeal_of_le_length s t (le_refl s.length)]
  have hbd0 : (s.append t hinv).boundary s.length
      = (s.boundary s.length).map (fun D => D.comap (eqToHom hobj0)) := by
    rw [MarkedBlowupSequenceData.append_boundary s t hinv s.length,
      MarkedBlowupSequenceData.appendBoundary_of_le_length s t (le_refl s.length)]
  have hstep0 : ∀ (i : ℕ) (hiS : i < (s.boundary s.length).length)
      (hiU : i < ((s.append t hinv).boundary s.length).length),
      orderAtLeastLocus (s.ideal s.length) S.mult ∩
          (((s.boundary s.length)[i]'hiS).support : Set ↥(s.obj s.length)) = ∅ →
        orderAtLeastLocus ((s.append t hinv).ideal s.length) S.mult ∩
          ((((s.append t hinv).boundary s.length)[i]'hiU).support :
            Set ↥((s.append t hinv).obj s.length)) = ∅ := by
    intro i hiS hiU hsep
    have himap : i < ((s.boundary s.length).map
        (fun D => D.comap (eqToHom hobj0))).length := by simpa using hiS
    have hbeli : ((s.append t hinv).boundary s.length)[i]'hiU
        = ((s.boundary s.length)[i]'hiS).comap (eqToHom hobj0) :=
      (getElem_eq_of_list_eq hbd0 i hiU himap).trans
        (getElem_map_of_lt
          (fun D : (s.obj s.length).IdealSheafData => D.comap (eqToHom hobj0))
          (s.boundary s.length) i hiS himap)
    exact orderAtLeastLocus_inter_support_eq_empty_of_eq hid0 hbeli
      (orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty hinv hobj0 (s.ideal s.length)
        ((s.boundary s.length)[i]'hiS) S.mult hsep)
  have hmid : ∀ (hjU : j < ((s.append t hinv).boundary (s.length + t.length)).length),
      orderAtLeastLocus ((s.append t hinv).ideal (s.length + t.length)) S.mult ∩
        ((((s.append t hinv).boundary (s.length + t.length))[j]'hjU).support :
          Set ↥((s.append t hinv).obj (s.length + t.length))) = ∅ := by
    intro hjU
    rcases Nat.eq_zero_or_pos t.length with hz | hpos
    · have hI0 : t.ideal 0 = (s.ideal s.length).comap t.isoZero.hom := t.ideal_zero
      have hjun : orderAtLeastLocus (s.ideal s.length) S.mult ∩
          (((s.boundary s.length)[j]'hbj).support : Set ↥(s.obj s.length)) = ∅ := by
        refine orderAtLeastLocus_inter_support_eq_empty_of_comap_iso hinv t.isoZero (s.ideal s.length)
          ((s.boundary s.length)[j]'hbj) S.mult ?_
        have h1 := hsepT 0 (Nat.zero_le _) (hsepK 0 hz.symm)
        rw [BlowupSequenceData.iteratedStrictTransform_zero] at h1
        exact orderAtLeastLocus_inter_support_eq_empty_of_eq hI0.symm rfl h1
      have hjU0 : j < ((s.append t hinv).boundary s.length).length := by
        have h := hblenU s.length hsle
        omega
      exact (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hj hsle
        (hstep0 j hbj hjU0 hjun) (s.length + t.length) (Nat.le_add_right _ _)
        (le_of_eq hulen.symm)
    · have hobjT : (s.appendToBlowupSequenceData t).obj (s.length + t.length) = t.obj t.length :=
        MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_length_add_length s t hpos
      have hidT : (s.append t hinv).ideal (s.length + t.length)
          = (t.ideal t.length).comap (eqToHom hobjT) :=
        MarkedBlowupSequenceData.append_ideal_length_add_length s t hinv hpos
      have hbdT : (s.append t hinv).boundary (s.length + t.length)
          = (t.boundary t.length).map (fun D => D.comap (eqToHom hobjT)) :=
        MarkedBlowupSequenceData.append_boundary_length_add_length s t hinv hpos
      have hjtt : j < (t.boundary t.length).length := by
        have h := MarkedBlowupSequenceData.boundary_length t t.length (le_refl t.length)
        omega
      have hjmapT : j < ((t.boundary t.length).map
          (fun D => D.comap (eqToHom hobjT))).length := by simpa using hjtt
      have hbelT : ((s.append t hinv).boundary (s.length + t.length))[j]'hjU
          = ((t.boundary t.length)[j]'hjtt).comap (eqToHom hobjT) :=
        (getElem_eq_of_list_eq hbdT j hjU hjmapT).trans
          (getElem_map_of_lt
            (fun D : (t.obj t.length).IdealSheafData => D.comap (eqToHom hobjT))
            (t.boundary t.length) j hjtt hjmapT)
      have hbel : (t.boundary t.length)[j]'hjtt
          = t.iteratedStrictTransform t.length ((s.boundary s.length)[j]'hbj) :=
        boundary_getElem_eq_iteratedStrictTransform t t.length (le_refl t.length) j hbj hjtt
      refine orderAtLeastLocus_inter_support_eq_empty_of_eq hidT hbelT ?_
      refine orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty hinv hobjT (t.ideal t.length)
        ((t.boundary t.length)[j]'hjtt) S.mult ?_
      exact orderAtLeastLocus_inter_support_eq_empty_of_eq rfl hbel
        (hsepT t.length (le_refl t.length) (hsepK t.length rfl))
  have htop : ∀ (hjU : j < ((s.append t hinv).boundary ((s.append t hinv).length)).length),
      orderAtLeastLocus ((s.append t hinv).ideal ((s.append t hinv).length)) S.mult ∩
        ((((s.append t hinv).boundary ((s.append t hinv).length))[j]'hjU).support :
          Set ↥((s.append t hinv).obj ((s.append t hinv).length))) = ∅ := by
    intro hjU
    have hjmid : j < ((s.append t hinv).boundary (s.length + t.length)).length := by
      have h := hblenU (s.length + t.length) (le_of_eq hulen.symm)
      omega
    exact (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hj (le_of_eq hulen.symm)
      (hmid hjmid) ((s.append t hinv).length) (le_of_eq hulen.symm) (le_refl _)
  refine ⟨?_, ?_, inStrictNormalCrossingPosition_iteratedStrictTransform_zero S (s.append t hinv) H hH⟩
  · intro i hi hii
    simp only [List.get_eq_getElem]
    rcases Nat.lt_or_ge i j with hij | hij
    · have hiE : i < S.boundary.length := lt_trans hij hj
      have hiU0 : i < ((s.append t hinv).boundary s.length).length := by
        have h := hblenU s.length hsle
        omega
      have hiS : i < (s.boundary s.length).length := by
        have h := MarkedBlowupSequenceData.boundary_length s s.length (le_refl s.length)
        omega
      have hbase : orderAtLeastLocus (s.ideal s.length) S.mult ∩
          (((s.boundary s.length)[i]'hiS).support : Set ↥(s.obj s.length)) = ∅ := by
        have h := hfacts.1 i hij hiS
        simp only [List.get_eq_getElem] at h
        exact h
      exact (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hiE hsle
        (hstep0 i hiS hiU0 hbase) ((s.append t hinv).length) hsle (le_refl _)
    · have hije : i = j := by omega
      subst hije
      exact htop hii
  · intro r hr
    rw [MarkedBlowupSequenceData.append_toBlowupSequenceData]
    rcases lt_trichotomy r s.length with h | h | h
    · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_lt_length s t h]
      exact comap_eqToHom_ne_top _ _ (hfacts.2.1 r h)
    · subst h
      rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length s t]
      have hpos : 0 < t.length := by omega
      exact comap_eqToHom_ne_top _ _
        (comap_iso_inv_ne_top t.isoZero (t.center 0) (hcent 0 hpos))
    · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_length_lt s t h]
      have hlt : r - s.length < t.length := by omega
      exact comap_eqToHom_ne_top _ _ (hcent (r - s.length) hlt)

theorem separateBoundaryInvariant_appendLowerDimReduction (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (j : ℕ) (hj : j < S.boundary.length) (hfacts : SeparateBoundaryInvariant S H s j) :
    SeparateBoundaryInvariant S H
      (MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) S s [] 0 j) (j + 1) := by
  classical
  have hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap) :=
    locallyOfFiniteType_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  have hm : 1 ≤ S.mult := hV.one_le_mult
  have hbj : j < (s.boundary s.length).length := by
    have h := MarkedBlowupSequenceData.boundary_length s s.length (le_refl s.length)
    omega
  have hsncAll : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap) (s.boundary s.length) := by
    have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length (le_refl s.length)).snc
    simp at h
    with_unfolding_all exact h
  have hsnc0 : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      (([] : List ((s.obj s.length)).IdealSheafData) ++ (s.boundary s.length).drop 0) := by
    simpa using hsncAll
  have hVc : (MaxContactCoverData.derivedTriple S s hft [] 0).IsAdmissible :=
    isAdmissible_derivedTriple hstar S hV s hft [] 0 hsnc0
  have hdimC : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ T.krullDimSucc := by
    have h1 := hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length (le_refl s.length)
    have h2 : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ S.krullDimSucc := by
      with_unfolding_all exact h1
    exact le_trans h2 hdimS
  have hPC : P (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc := hmono _ _ hdimC hPdimT
  have hordBound := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbalanced := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbdC : (MaxContactCoverData.derivedTriple S s hft [] 0).boundary = s.boundary s.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    simp
  have hjC' : j < (MaxContactCoverData.derivedTriple S s hft [] 0).boundary.length := by
    rw [hbdC]
    exact hbj
  have hjC : j < (([] : List ((s.obj s.length)).IdealSheafData)
      ++ (s.boundary s.length).drop 0).length := by simpa using hbj
  have hsepC : ∀ D ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅ := by
    intro D hD
    simp at hD
  obtain ⟨hmk, hceq, hcos⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B j (hspec j)
    (MaxContactFunctoriality.lowerDimensionalFamily A T) (fun _ _ _ => rfl) S hV hm hO s [] 0 hft hdimC hPC hVc
    hjC hsepC
  obtain ⟨Dv, bv, _, hC2, _, hC4, hC5, hC6, _⟩ :=
    (hspec j).shape (MaxContactCoverData.derivedTriple S s hft [] 0) hVc hPC hordBound hbalanced hjC'
  have hget : ((MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j, hjC'⟩)
      = (s.boundary s.length)[j]'hbj := by
    simp only [List.get_eq_getElem]
    exact getElem_eq_of_list_eq hbdC j hjC' hbj
  rw [hceq]
  refine separateBoundaryInvariant_append hstar hinv S H hH s _ j hj hbj hfacts ?_ Dv ?_ ?_ ?_ ?_
  · intro i hi
    exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar S hV s hft [] 0 hVc
      (A j (MaxContactCoverData.derivedTriple S s hft [] 0)) i hi
  · rw [hC2, hget]
    with_unfolding_all rfl
  · intro r hr
    by_cases hb : bv = true ∧ r = 0
    · obtain ⟨hb1, hb2⟩ := hb
      subst hb2
      exact Or.inr (hC4 hb1).2.2
    · exact Or.inl (hC5 r hr hb)
  · intro r hrr
    have hrr' : r = (A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length := hrr
    subst hrr'
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx1, hx2⟩
    have hc := hcos ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length) (le_refl _)
    have hx1' : x ∈ orderAtLeastLocus
        ((BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups).controlledTransform
          (s.ideal s.length) S.mult ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length))
        S.mult := hx1
    rw [hc] at hx1'
    have hmem : x ∈ orderAtLeastLocus
        (MarkedSequenceOfBlowups.lastIdeal (A j (MaxContactCoverData.derivedTriple S s hft [] 0)))
        (MaxContactCoverData.derivedTriple S s hft [] 0).mult ∩
        (((Dv ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length)).support) :
          Set ↥((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).schemeAt
            ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length))) := ⟨hx1', hx2⟩
    rw [hC6] at hmem
    exact hmem
  · intro r hr htop
    exact ((hspec j).center_nonempty (MaxContactCoverData.derivedTriple S s hft [] 0) hVc hPC hordBound hbalanced
      hjC' r hr).ne_empty
      ((AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).1 htop)

abbrev separateBoundarySeq (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (j : ℕ) :
    MarkedBlowupSequenceData (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.coverTriple T hv).mult
      (MaxContactCoverData.coverTriple T hv).boundary :=
  MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
    (MaxContactCoverData.coverTriple T hv) j

abbrev separateAllBoundary (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) :
    MarkedBlowupSequenceData (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.coverTriple T hv).mult
      (MaxContactCoverData.coverTriple T hv).boundary :=
  separateBoundarySeq T hv hinv A (MaxContactCoverData.coverTriple T hv).boundary.length

abbrev reduceAlongHypersurfaceTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u})
    (hft : AlgebraicGeometry.LocallyOfFiniteType
      ((separateAllBoundary T hv hinv A).proj (separateAllBoundary T hv hinv A).length ≫
        (MaxContactCoverData.coverTriple T hv).structMap)) : MarkedIdealWithBoundary.{u} :=
  MaxContactCoverData.derivedTriple (MaxContactCoverData.coverTriple T hv) (separateAllBoundary T hv hinv A) hft
    [MaxContactReduction.strictTransformAtLength (separateAllBoundary T hv hinv A) (MaxContactCoverData.coverMaxContactIdeal T hv)]
    (MaxContactCoverData.coverTriple T hv).boundary.length

theorem separateBoundaryInvariant_separateBoundarySeq (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (j : ℕ) (hj : j ≤ (MaxContactCoverData.coverTriple T h.valid).boundary.length) :
    SeparateBoundaryInvariant (MaxContactCoverData.coverTriple T h.valid)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) (separateBoundarySeq T h.valid hinv A j) j := by
  revert hj
  induction j with
  | zero =>
      intro _
      have h0 : separateBoundarySeq T h.valid hinv A 0
          = emptyMarkedBlowupSequenceData (MaxContactCoverData.coverTriple T h.valid).structMap
              (MaxContactCoverData.coverTriple T h.valid).ideal
              (MaxContactCoverData.coverTriple T h.valid).mult
              (MaxContactCoverData.coverTriple T h.valid).boundary :=
        MaxContactCoverData.separateBoundary_zero hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid)
      refine And.intro ?_ (And.intro ?_ ?_)
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
      · rw [h0]
        intro i hi
        exact absurd hi (Nat.not_lt_zero i)
      · exact inStrictNormalCrossingPosition_iteratedStrictTransform_zero (MaxContactCoverData.coverTriple T h.valid)
          (separateBoundarySeq T h.valid hinv A 0) (MaxContactCoverData.coverMaxContactIdeal T h.valid)
          (inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  | succ n ih =>
      intro hj
      have hn : n < (MaxContactCoverData.coverTriple T h.valid).boundary.length := hj
      have hfacts := ih (Nat.le_of_succ_le hj)
      have hsucc : separateBoundarySeq T h.valid hinv A (n + 1)
          = MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
              (MaxContactCoverData.coverTriple T h.valid) (separateBoundarySeq T h.valid hinv A n) [] 0 n :=
        MaxContactCoverData.separateBoundary_succ hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid) n
      rw [hsucc]
      exact separateBoundaryInvariant_appendLowerDimReduction hstar hinv P hmono A B hspec T h.dim_prop
        (MaxContactCoverData.coverTriple T h.valid) (isAdmissible_coverTriple hstar P T h)
        (orderAt_coverTriple_ideal_le_mult hstar P T h) (hstar.coverTriple_dim_le T h.valid)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid) (inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
        (separateBoundarySeq T h.valid hinv A n) n hn hfacts

private theorem forall_mem_take_of_forall_lt {α : Type*} (Q : α → Prop) :
    ∀ (L : List α) (n : ℕ),
      (∀ i : ℕ, i < n → ∀ hi : i < L.length, Q (L.get ⟨i, hi⟩)) → ∀ a ∈ L.take n, Q a := by
  intro L
  induction L with
  | nil =>
      intro n _ a ha
      simp at ha
  | cons b L ih =>
      intro n hQ a ha
      cases n with
      | zero => simp at ha
      | succ m =>
          have ha' : a ∈ b :: L.take m := ha
          rcases List.mem_cons.mp ha' with rfl | ha''
          · exact hQ 0 (Nat.succ_pos m) (by simp)
          · exact ih m
              (fun i him hi => hQ (i + 1) (Nat.succ_lt_succ him) (Nat.succ_lt_succ hi)) a ha''

theorem exists_cover_eq_separateAllBoundary_append (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∃ hft : AlgebraicGeometry.LocallyOfFiniteType
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap),
      ∃ _hV : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsAdmissible,
        P (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc ∧
        ∃ hmk : (BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).IsMarked
            ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
              (MaxContactCoverData.coverTriple T h.valid).structMap)
            ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
            (MaxContactCoverData.coverTriple T h.valid).mult
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length),
          MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T) =
              (separateAllBoundary T h.valid hinv A).append
                (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
                  (separateAllBoundary T h.valid hinv A)
                  hft
                  [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
                    (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
                  (MaxContactCoverData.coverTriple T h.valid).boundary.length
                  (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) hinv ∧
            ∀ i ≤ (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups.length,
              orderAtLeastLocus
                  ((BlowupSequenceData.ofSequenceOfBlowups
                      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).controlledTransform
                    ((separateAllBoundary T h.valid hinv A).ideal
                      (separateAllBoundary T h.valid hinv A).length)
                    (MaxContactCoverData.coverTriple T h.valid).mult i)
                  (MaxContactCoverData.coverTriple T h.valid).mult =
                orderAtLeastLocus ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i)
                  (tuningExponent (MaxContactCoverData.coverTriple T h.valid).mult) := by
  have hV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hO : ∀ x : ↥(MaxContactCoverData.coverTriple T h.valid).scheme,
      orderAt (MaxContactCoverData.coverTriple T h.valid).ideal x ≤
        ((MaxContactCoverData.coverTriple T h.valid).mult : ℕ∞) :=
    orderAt_coverTriple_ideal_le_mult hstar P T h
  have hft : AlgebraicGeometry.LocallyOfFiniteType
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap) :=
    locallyOfFiniteType_projectionToBase_comp hstar (MaxContactCoverData.coverTriple T h.valid) hV
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hadm := isMaxContactHypersurface_coverMaxContactIdeal hstar P T h
  have hzero := inStrictNormalCrossingPosition_iteratedStrictTransform_zero (MaxContactCoverData.coverTriple T h.valid)
    (separateAllBoundary T h.valid hinv A) (MaxContactCoverData.coverMaxContactIdeal T h.valid)
    (inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  have hsnc := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (MaxContactCoverData.coverTriple T h.valid)
    hV hO (MaxContactCoverData.coverMaxContactIdeal T h.valid) hadm (separateAllBoundary T h.valid hinv A) hzero
    (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hsnc' : InStrictNormalCrossingPosition
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ([MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)] ++
        ((separateAllBoundary T h.valid hinv A).boundary
          (separateAllBoundary T h.valid hinv A).length).drop
            (MaxContactCoverData.coverTriple T h.valid).boundary.length) := by
    exact hsnc
  have hVc : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsAdmissible :=
    isAdmissible_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hV
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hsnc'
  have hdim : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc ≤ T.krullDimSucc := by
    have h1 := hstar.schemeDim_level_le (MaxContactCoverData.coverTriple T h.valid) hV
      (separateAllBoundary T h.valid hinv A).toMarkedSequenceOfBlowups (separateAllBoundary T h.valid hinv A).length
      (le_refl _)
    have h2 := hstar.coverTriple_dim_le T h.valid
    have h3 : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc ≤
        (MaxContactCoverData.coverTriple T h.valid).krullDimSucc := by
      with_unfolding_all exact h1
    exact le_trans h3 h2
  have hP : P (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc := hmono _ _ hdim h.dim_prop
  have hj : 0 < ([MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)] ++
      ((separateAllBoundary T h.valid hinv A).boundary
        (separateAllBoundary T h.valid hinv A).length).drop
          (MaxContactCoverData.coverTriple T h.valid).boundary.length).length := by
    rw [List.singleton_append, List.length_cons]
    omega
  have hfacts := separateBoundaryInvariant_separateBoundarySeq hstar hinv P hmono A B hspec T h
    (MaxContactCoverData.coverTriple T h.valid).boundary.length (le_refl _)
  have htop : BoundarySeparated (MaxContactCoverData.coverTriple T h.valid) (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverTriple T h.valid).boundary.length := And.left hfacts
  have hsep : ∀ D ∈ ((separateAllBoundary T h.valid hinv A).boundary
        (separateAllBoundary T h.valid hinv A).length).take
          (MaxContactCoverData.coverTriple T h.valid).boundary.length,
      orderAtLeastLocus ((separateAllBoundary T h.valid hinv A).ideal
            (separateAllBoundary T h.valid hinv A).length)
          (MaxContactCoverData.coverTriple T h.valid).mult ∩
        ((D.support : Set ↥((separateAllBoundary T h.valid hinv A).obj
          (separateAllBoundary T h.valid hinv A).length))) = ∅ :=
    forall_mem_take_of_forall_lt _ _ _ htop
  obtain ⟨hmk, heq, hcos⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (MaxContactFunctoriality.lowerDimensionalFamily A T) (fun _ _ _ => rfl)
    (MaxContactCoverData.coverTriple T h.valid) hV hV.one_le_mult hO
    (separateAllBoundary T h.valid hinv A)
    [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
    (MaxContactCoverData.coverTriple T h.valid).boundary.length hft hdim hP hVc hj hsep
  have hcover : MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T) =
      MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
        (MaxContactCoverData.coverTriple T h.valid) (separateAllBoundary T h.valid hinv A)
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length 0 :=
    MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
      (MaxContactCoverData.coverTriple T h.valid) (MaxContactCoverData.coverMaxContactIdeal T h.valid)
  refine ⟨hft, hVc, hP, hmk, ?_, hcos⟩
  rw [hcover]
  exact heq

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
