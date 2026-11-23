import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def monomialBlowupStep (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) :=
  ofSingleBlowup (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)
    (centerAtLast s) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_length (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).length = 1 :=
  ofSingleBlowup_length h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_schemeAt_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).obj 0 = s.obj s.length :=
  ofSingleBlowup_schemeAt_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_schemeAt_succ (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) (i : ℕ) :
    (monomialBlowupStep s h).obj (i + 1) = Blowup.blowup (centerAtLast s) :=
  ofSingleBlowup_schemeAt_succ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 i

@[simp]
theorem monomialBlowupStep_center_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).center 0 = centerAtLast s :=
  ofSingleBlowup_center_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_blowupMorphism_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).map 0 = Blowup.blowup.proj (centerAtLast s) :=
  ofSingleBlowup_blowupMorphism_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_projectionToBase_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).proj 1 = Blowup.blowup.proj (centerAtLast s) :=
  ofSingleBlowup_projectionToBase_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_ideal_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).ideal 1 =
      residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
        ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m :=
  ofSingleBlowup_ideal_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_boundary_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).boundary 1 =
      List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
          (s.boundary s.length) ++
        [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)] :=
  ofSingleBlowup_boundary_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem monomialBlowupStep_isoObjZero_inv (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).isoZero.inv = eqToHom (monomialBlowupStep_schemeAt_zero s h).symm :=
  rfl

theorem blowupAtCenter_eq_append (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    blowupAtCenter hinv s = s.append (monomialBlowupStep s h) hinv := by
  unfold blowupAtCenter monomialBlowupStep
  rw [dif_pos h]

theorem blowupAtCenter_length (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).length = s.length + 1 := by
  rw [blowupAtCenter_eq_append hinv s h, append_length, monomialBlowupStep_length]

theorem isStationaryAt_iff_not_isAdmissibleCenter (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) (n : ℕ) :
    IsStationaryAt hinv s n ↔ ¬ IsAdmissibleCenter (monomialBlowupIterate hinv s n) := by
  constructor
  · intro h hstep
    have hl := blowupAtCenter_length hinv (monomialBlowupIterate hinv s n) hstep
    have h' : (blowupAtCenter hinv (monomialBlowupIterate hinv s n)).length
        = (monomialBlowupIterate hinv s n).length := h
    rw [hl] at h'
    omega
  · intro h
    show (blowupAtCenter hinv (monomialBlowupIterate hinv s n)).length
        = (monomialBlowupIterate hinv s n).length
    unfold blowupAtCenter
    rw [dif_neg h]

theorem blowupAtCenter_schemeAt_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).obj (s.length + 1) = Blowup.blowup (centerAtLast s) := by
  have hlt : s.length < s.length + 1 := Nat.lt_succ_self s.length
  rw [blowupAtCenter_eq_append hinv s h, append_schemeAt_of_length_lt s (monomialBlowupStep s h) hinv hlt]
  have he : s.length + 1 - s.length = 0 + 1 := by omega
  rw [he, monomialBlowupStep_schemeAt_succ s h 0]

theorem blowupAtCenter_ideal_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).ideal (s.length + 1) =
      (residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
          ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m).comap
        (eqToHom (blowupAtCenter_schemeAt_succ hinv s h)) := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = s.append (monomialBlowupStep s h) hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.ideal (s.length + 1) =
          (residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
              ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m).comap (eqToHom hobj) := by
    rintro d rfl hobj
    rewrite [append_ideal, appendIdeal_length_succ, monomialBlowupStep_ideal_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)

private theorem boundary_succ_of_eq_append (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) (d : MarkedBlowupSequenceData p I m E)
    (hd : d = s.append (monomialBlowupStep s h) hinv)
    (e : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s)) :
    d.boundary (s.length + 1) =
      List.map (fun D => D.comap (eqToHom e))
        (List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)]) := by
  subst hd
  refine Eq.trans (append_boundary s (monomialBlowupStep s h) hinv (s.length + 1)) ?_
  refine Eq.trans (appendBoundary_length_succ s (monomialBlowupStep s h)) ?_
  exact congrArg
    (List.map (fun D : (Blowup.blowup (centerAtLast s)).IdealSheafData => D.comap (eqToHom e)))
    (monomialBlowupStep_boundary_one s h)

theorem blowupAtCenter_boundary_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).boundary (s.length + 1) =
      List.map (fun D => D.comap (eqToHom (blowupAtCenter_schemeAt_succ hinv s h)))
        (List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)]) :=
  boundary_succ_of_eq_append hinv s h (blowupAtCenter hinv s)
    (blowupAtCenter_eq_append hinv s h) (blowupAtCenter_schemeAt_succ hinv s h)

private theorem appendProjectionToBase_of_lt (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (i j : ℕ) (hi : s.length < i) (hj : i - s.length = j)
    (hobj : (s.appendToBlowupSequenceData t).obj i = t.obj j) :
    s.appendProjectionToBase t i = eqToHom hobj ≫ t.proj j ≫ s.proj s.length := by
  subst hj
  exact appendProjectionToBase_of_length_lt s t hi

theorem blowupAtCenter_projectionToBase_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).proj (s.length + 1) =
      eqToHom (blowupAtCenter_schemeAt_succ hinv s h) ≫ Blowup.blowup.proj (centerAtLast s) ≫ s.proj s.length := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = s.append (monomialBlowupStep s h) hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.proj (s.length + 1) =
          eqToHom hobj ≫ Blowup.blowup.proj (centerAtLast s) ≫ s.proj s.length := by
    rintro d rfl hobj
    rewrite [append_projectionToBase,
      appendProjectionToBase_of_lt s (monomialBlowupStep s h) (s.length + 1) 1 (by omega) (by omega)
        (appendToBlowupSequenceData_schemeAt_length_succ s (monomialBlowupStep s h)),
      monomialBlowupStep_projectionToBase_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

def monomialStallIndex (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) : ℕ :=
  sInf {n : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n}

theorem isStationaryAt_monomialStallIndex (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData)
    (hex : ∃ n : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n) :
    MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) (monomialStallIndex hinv p I m E) := by
  exact Nat.sInf_mem hex

theorem isAdmissibleCenter_of_lt_monomialStallIndex (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (n : ℕ) (hn : n < monomialStallIndex hinv p I m E) :
    MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) := by
  have hn' : n < sInf {j : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j} := hn
  have hstall : ¬ MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n := by
    intro hmem
    have hle : sInf {j : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j} ≤ n :=
      Nat.sInf_le hmem
    exact absurd hle (not_le.mpr hn')
  by_contra hstep
  exact hstall
    ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv (emptyMarkedBlowupSequenceData p I m E) n).mpr hstep)

theorem monomialStallIndex_eq_of_isStationaryAt (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (n : ℕ)
    (hstall : MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (hstep : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j)) :
    monomialStallIndex hinv p I m E = n := by
  have hne : ∃ j : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j := ⟨n, hstall⟩
  have h1 : monomialStallIndex hinv p I m E ≤ n := Nat.sInf_le hstall
  refine le_antisymm h1 ?_
  by_contra hlt
  have hlt' : monomialStallIndex hinv p I m E < n := lt_of_not_ge hlt
  have hmem : MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E)
      (monomialStallIndex hinv p I m E) := Nat.sInf_mem hne
  exact ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv _ _).mp hmem) (hstep _ hlt')

theorem monomialBlowupSeq_eq_monomialBlowupIterate (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) :
    monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (monomialStallIndex hinv p I m E) :=
  rfl

private theorem monomialBlowupIterate_length {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (n : ℕ) :
    (∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)) →
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length = s.length + n := by
  induction n with
  | zero =>
      intro _
      rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero, Nat.add_zero]
  | succ n ih =>
      intro hstep
      have h2 : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n) :=
        hstep n (Nat.lt_succ_self n)
      have h1 := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have e1 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s (n + 1)).length
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length + 1 := by
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
          MarkedBlowupSequenceData.blowupAtCenter_length hinv _ h2]
      omega

theorem monomialBlowupSeq_length (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) :
    (monomialBlowupSeq hinv p I m E).length = monomialStallIndex hinv p I m E := by
  have h := monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E)
    (monomialStallIndex hinv p I m E)
    (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j hj)
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, h, emptyMarkedBlowupSequenceData_length, Nat.zero_add]

private theorem blowupAtCenter_schemeAt_of_le {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ d.length) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj i := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h]
    exact MarkedBlowupSequenceData.append_schemeAt_of_le_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv hi
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    rw [hs]

private theorem length_le_blowupAtCenter_length {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) :
    d.length ≤ (MarkedBlowupSequenceData.blowupAtCenter hinv d).length := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv d h]
    omega
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    exact le_of_eq (by rw [hs])

private theorem monomialBlowupIterate_length_le_and_schemeAt_eq {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (j : ℕ) :
    d.length ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).length ∧
      ∀ i ≤ d.length, (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i := by
  induction j with
  | zero =>
      refine ⟨?_, ?_⟩
      · exact le_of_eq (by rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero])
      · intro i _
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero]
  | succ j ih =>
      refine ⟨?_, ?_⟩
      · refine le_trans ih.1 ?_
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ]
        exact length_le_blowupAtCenter_length hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j)
      · intro i hi
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
          blowupAtCenter_schemeAt_of_le hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i
            (le_trans hi ih.1)]
        exact ih.2 i hi

private theorem monomialBlowupIterate_add {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (a b : ℕ) :
    MarkedBlowupSequenceData.monomialBlowupIterate hinv d (a + b) =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d a) b := by
  induction b with
  | zero => rw [Nat.add_zero, MarkedBlowupSequenceData.monomialBlowupIterate_zero]
  | succ b ih =>
      rw [← Nat.add_assoc, MarkedBlowupSequenceData.monomialBlowupIterate_succ,
        MarkedBlowupSequenceData.monomialBlowupIterate_succ, ih]

theorem monomialBlowupSeq_schemeAt (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).obj n =
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).obj
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length := by
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    have h := monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn))
    rw [emptyMarkedBlowupSequenceData_length, Nat.zero_add] at h
    exact h
  rw [hlen]
  have hsplit : monomialStallIndex hinv p I m E = n + (monomialStallIndex hinv p I m E - n) := by
    omega
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, hsplit, monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) n
    (monomialStallIndex hinv p I m E - n)]
  exact (monomialBlowupIterate_length_le_and_schemeAt_eq hinv
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (monomialStallIndex hinv p I m E - n)).2 n (le_of_eq hlen.symm)

private theorem comap_eqToHom_comap_eqToHom_symm {V W : Scheme.{u}} (h : V = W)
    (J : W.IdealSheafData) :
    (J.comap (eqToHom h)).comap (eqToHom h.symm) = J := by
  subst h
  simp

private theorem isPrefix_monomialBlowupIterate_succ {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) (j : ℕ) :
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j).IsPrefix
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s (j + 1)) := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)
  · rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
      MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv _ h]
    exact MarkedBlowupSequenceData.isPrefix_append _ _ hinv
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv s j := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ, hs]
    exact MarkedBlowupSequenceData.IsPrefix.refl _

private theorem isPrefix_monomialBlowupIterate_of_le {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) {i j : ℕ} (hij : i ≤ j) :
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv s i).IsPrefix
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j) := by
  induction j with
  | zero =>
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      exact MarkedBlowupSequenceData.IsPrefix.refl _
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact MarkedBlowupSequenceData.IsPrefix.refl _
      · exact (ih (Nat.lt_succ_iff.mp h)).trans (isPrefix_monomialBlowupIterate_succ hinv s n)

private theorem ideal_eq_comap_of_isPrefix {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (A B : MarkedBlowupSequenceData p I m E) (n : ℕ) (hlen : A.length = n)
    (hpre : A.IsPrefix B) (hobj : B.obj n = A.obj A.length) :
    B.ideal n = (A.ideal A.length).comap (eqToHom hobj) := by
  subst hlen
  rw [hpre.ideal_eq A.length le_rfl]
  exact (comap_eqToHom_comap_eqToHom_symm (hpre.obj_eq A.length le_rfl) (B.ideal A.length)).symm

theorem monomialBlowupSeq_ideal (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).ideal n =
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).ideal
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length).comap
        (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n hn)) := by
  have hstep : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j) :=
    fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn)
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    rw [monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n hstep,
      emptyMarkedBlowupSequenceData_length, Nat.zero_add]
  have hpre : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).IsPrefix
      (monomialBlowupSeq hinv p I m E) := by
    rw [monomialBlowupSeq_eq_monomialBlowupIterate]
    exact isPrefix_monomialBlowupIterate_of_le hinv (emptyMarkedBlowupSequenceData p I m E) hn
  exact ideal_eq_comap_of_isPrefix
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (monomialBlowupSeq hinv p I m E) n hlen hpre (monomialBlowupSeq_schemeAt hinv p I m E n hn)

private theorem comap_eqToHom_self {Y : Scheme.{u}} (q : Y = Y) (Z : Y.IdealSheafData) :
    Z.comap (eqToHom q) = Z := by
  simp

private theorem map_comap_eqToHom_self {Y : Scheme.{u}} (q : Y = Y) (L : List Y.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom q)) L = L := by
  induction L with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ih, comap_eqToHom_self]

private theorem comap_eqToHom_comp {A B C : Scheme.{u}} (hAB : A = B) (hBC : B = C) (hAC : A = C)
    (D : C.IdealSheafData) :
    (D.comap (eqToHom hBC)).comap (eqToHom hAB) = D.comap (eqToHom hAC) := by
  cases hAB
  cases hBC
  simp only [comap_eqToHom_self]

private theorem map_comap_eqToHom_comp {A B C : Scheme.{u}} (hAB : A = B) (hBC : B = C)
    (hAC : A = C) (L : List C.IdealSheafData) :
    List.map (fun D : B.IdealSheafData => D.comap (eqToHom hAB))
        (List.map (fun D : C.IdealSheafData => D.comap (eqToHom hBC)) L)
      = List.map (fun D : C.IdealSheafData => D.comap (eqToHom hAC)) L := by
  induction L with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih, comap_eqToHom_comp hAB hBC hAC]

private theorem blowupAtCenter_boundary_of_le (hinv : ComapIsoInvariance.{u})
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) (i : ℕ) (hi : i ≤ s.length)
    (ho : (MarkedBlowupSequenceData.blowupAtCenter hinv s).obj i = s.obj i) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv s).boundary i =
      List.map (fun D => D.comap (eqToHom ho)) (s.boundary i) := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E,
      d = s.append (MarkedBlowupSequenceData.monomialBlowupStep s h) hinv →
      ∀ ho' : d.obj i = s.obj i,
        d.boundary i = List.map (fun D => D.comap (eqToHom ho')) (s.boundary i) := by
    rintro d rfl ho'
    refine Eq.trans
      (MarkedBlowupSequenceData.append_boundary s (MarkedBlowupSequenceData.monomialBlowupStep s h) hinv i) ?_
    exact MarkedBlowupSequenceData.appendBoundary_of_le_length s (MarkedBlowupSequenceData.monomialBlowupStep s h) hi
  exact key (MarkedBlowupSequenceData.blowupAtCenter hinv s)
    (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv s h) ho

private theorem monomialBlowupIterate_boundary_of_le (hinv : ComapIsoInvariance.{u})
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ s.length) (d : ℕ) :
    (∀ j < d, MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)) →
      ∀ ho : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i = s.obj i,
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).boundary i =
          List.map (fun D => D.comap (eqToHom ho)) (s.boundary i) := by
  induction d with
  | zero =>
      intro _ ho
      exact (map_comap_eqToHom_self ho (s.boundary i)).symm
  | succ d ih =>
      intro hstep ho
      have h2 : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) :=
        hstep d (Nat.lt_succ_self d)
      have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).length = s.length + d :=
        monomialBlowupIterate_length hinv s d (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have hi' : i ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).length := by omega
      have hobj1 : (MarkedBlowupSequenceData.blowupAtCenter hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d)).obj i
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i :=
        blowupAtCenter_schemeAt_of_le hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) i hi'
      have hobj2 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i = s.obj i :=
        Eq.trans hobj1.symm ho
      have hstep1 := blowupAtCenter_boundary_of_le hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) h2 i hi' hobj1
      have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj)) hobj2
      exact Eq.trans hstep1
        (Eq.trans (congrArg (List.map (fun D => D.comap (eqToHom hobj1))) hprev)
          (map_comap_eqToHom_comp hobj1 hobj2 ho (s.boundary i)))

private theorem boundary_eq_map_comap_of_index_eq
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (d t : MarkedBlowupSequenceData p I m E) (n L : ℕ) (hL : L = n)
    (hb : ∀ ho : d.obj n = t.obj n,
      d.boundary n = List.map (fun D => D.comap (eqToHom ho)) (t.boundary n))
    (H : d.obj n = t.obj L) :
    d.boundary n = List.map (fun D => D.comap (eqToHom H)) (t.boundary L) := by
  subst hL
  exact hb H

theorem monomialBlowupSeq_boundary (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).boundary n =
      List.map (fun D => D.comap (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n hn)))
        ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).boundary
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length) := by
  have hsteps0 : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j) :=
    fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn)
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    rw [monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n hsteps0,
      emptyMarkedBlowupSequenceData_length, Nat.zero_add]
  have h1 : n + (monomialStallIndex hinv p I m E - n) = monomialStallIndex hinv p I m E := by omega
  have hseq : monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
        (monomialStallIndex hinv p I m E - n) := by
    have h2 : MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (n + (monomialStallIndex hinv p I m E - n))
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
            (monomialStallIndex hinv p I m E - n) :=
      monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) n (monomialStallIndex hinv p I m E - n)
    rw [h1] at h2
    exact Eq.trans (monomialBlowupSeq_eq_monomialBlowupIterate hinv p I m E) h2
  have hstepsn : ∀ j < monomialStallIndex hinv p I m E - n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) j) := by
    intro j hj
    have h3 : MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) j
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) (n + j) :=
      (monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) n j).symm
    rw [h3]
    exact isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E (n + j) (by omega)
  have key : ∀ d : MarkedBlowupSequenceData p I m E,
      d = MarkedBlowupSequenceData.monomialBlowupIterate hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
            (monomialStallIndex hinv p I m E - n) →
      ∀ ho : d.obj n = (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).obj n,
        d.boundary n = List.map (fun D => D.comap (eqToHom ho))
          ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).boundary n) := by
    rintro d rfl ho
    exact monomialBlowupIterate_boundary_of_le hinv
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n (by omega)
      (monomialStallIndex hinv p I m E - n) hstepsn ho
  exact boundary_eq_map_comap_of_index_eq (monomialBlowupSeq hinv p I m E)
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length hlen
    (key (monomialBlowupSeq hinv p I m E) hseq) (monomialBlowupSeq_schemeAt hinv p I m E n hn)

private theorem append_center_eq_appendToBlowupSequenceData_center {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (i : ℕ) :
    (s.append t hinv).center i = (s.appendToBlowupSequenceData t).center i :=
  rfl

private theorem blowupAtCenter_center_of_lt {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i < d.length)
    (e : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj i) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).center i = (d.center i).comap (eqToHom e) := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · have key : ∀ D : MarkedBlowupSequenceData p I m E,
        D = d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv →
        ∀ eD : D.obj i = d.obj i, D.center i = (d.center i).comap (eqToHom eD) := by
      rintro D rfl eD
      refine Eq.trans
        (append_center_eq_appendToBlowupSequenceData_center d (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv i) ?_
      exact MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_lt_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) hi
    exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d)
      (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h) e
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    have key : ∀ D : MarkedBlowupSequenceData p I m E, D = d →
        ∀ eD : D.obj i = d.obj i, D.center i = (d.center i).comap (eqToHom eD) := by
      rintro D rfl eD
      exact (comap_eqToHom_self eD _).symm
    exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d) hs e

private theorem monomialBlowupIterate_center_of_lt {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i < d.length) (j : ℕ) :
    ∀ e : (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i,
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).center i = (d.center i).comap (eqToHom e) := by
  induction j with
  | zero =>
      intro e
      exact (comap_eqToHom_self e (d.center i)).symm
  | succ j ih =>
      intro e
      have e2 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i :=
        (monomialBlowupIterate_length_le_and_schemeAt_eq hinv d j).2 i (le_of_lt hi)
      have hij : i < (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).length :=
        lt_of_lt_of_le hi (monomialBlowupIterate_length_le_and_schemeAt_eq hinv d j).1
      have e1 : (MarkedBlowupSequenceData.blowupAtCenter hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j)).obj i
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i :=
        blowupAtCenter_schemeAt_of_le hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i (le_of_lt hij)
      refine Eq.trans
        (blowupAtCenter_center_of_lt hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i hij e1) ?_
      rw [ih e2]
      exact comap_eqToHom_comp e1 e2 e (d.center i)

private theorem blowupAtCenter_center_of_eq_length {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) (i : ℕ) (hi : i = d.length)
    (e : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj d.length) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).center i =
      (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom e) := by
  subst hi
  have key : ∀ D : MarkedBlowupSequenceData p I m E,
      D = d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv →
      ∀ eD : D.obj d.length = d.obj d.length,
        D.center d.length = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
    rintro D rfl eD
    have hc : (d.appendToBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep d h)).obj d.length
        = d.obj d.length :=
      MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) (le_refl d.length)
    have e3 : (d.appendToBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep d h)).obj d.length
        = (MarkedBlowupSequenceData.monomialBlowupStep d h).obj 0 :=
      hc.trans (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm
    have s1 : (d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv).center d.length
        = (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (MarkedBlowupSequenceData.monomialBlowupStep d h).isoZero.inv).comap (eqToHom hc) :=
      MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length d (MarkedBlowupSequenceData.monomialBlowupStep d h)
    have s2 : (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (MarkedBlowupSequenceData.monomialBlowupStep d h).isoZero.inv).comap (eqToHom hc)
        = (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (eqToHom (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm)).comap (eqToHom hc) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_isoObjZero_inv]
    have s3 : (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (eqToHom (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm)).comap (eqToHom hc)
        = ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap (eqToHom e3) :=
      comap_eqToHom_comp hc (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm e3
        ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0)
    have s4 : ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap (eqToHom e3)
        = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_center_zero]
      rfl
    exact s1.trans (s2.trans (s3.trans s4))
  exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d)
    (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h) e

private theorem center_monomialBlowupIterate_blowupAtCenter_eq {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (n : ℕ) (hlen : d.length = n)
    (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) (r : ℕ) (D : MarkedBlowupSequenceData p I m E)
    (hD : D = MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) r)
    (eD : D.obj n = d.obj d.length) :
    D.center n = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
  subst hD
  have hl1 : (MarkedBlowupSequenceData.blowupAtCenter hinv d).length = n + 1 := by
    rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv d h, hlen]
  have hn1 : n < (MarkedBlowupSequenceData.blowupAtCenter hinv d).length := by omega
  have e1 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.blowupAtCenter hinv d) r).obj n
      = (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj n :=
    (monomialBlowupIterate_length_le_and_schemeAt_eq hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) r).2 n
      (le_of_lt hn1)
  have ejunc : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj n = d.obj d.length :=
    (blowupAtCenter_schemeAt_of_le hinv d n (le_of_eq hlen.symm)).trans (congrArg d.obj hlen.symm)
  rw [monomialBlowupIterate_center_of_lt hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) n hn1 r e1,
    blowupAtCenter_center_of_eq_length hinv d h n hlen.symm ejunc]
  exact comap_eqToHom_comp e1 ejunc eD (MarkedBlowupSequenceData.centerAtLast d)

theorem monomialBlowupSeq_center (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n < monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).center n =
      (MarkedBlowupSequenceData.centerAtLast
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)).comap
        (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n (Nat.le_of_lt hn))) := by
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    have h := monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_trans hj hn))
    rw [emptyMarkedBlowupSequenceData_length, Nat.zero_add] at h
    exact h
  have hstep : MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) :=
    isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E n hn
  have hsplit : monomialStallIndex hinv p I m E
      = (n + 1) + (monomialStallIndex hinv p I m E - (n + 1)) := by
    omega
  have h1 : MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (monomialStallIndex hinv p I m E)
      = MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
          ((n + 1) + (monomialStallIndex hinv p I m E - (n + 1))) := by
    rw [← hsplit]
  have hseq : monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.blowupAtCenter hinv
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n))
        (monomialStallIndex hinv p I m E - (n + 1)) := by
    rw [monomialBlowupSeq_eq_monomialBlowupIterate, h1,
      monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) (n + 1)
        (monomialStallIndex hinv p I m E - (n + 1)),
      MarkedBlowupSequenceData.monomialBlowupIterate_succ]
  exact center_monomialBlowupIterate_blowupAtCenter_eq hinv
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n
    hlen hstep (monomialStallIndex hinv p I m E - (n + 1)) (monomialBlowupSeq hinv p I m E) hseq
    (monomialBlowupSeq_schemeAt hinv p I m E n (Nat.le_of_lt hn))

end

namespace MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def monomialStallIndex (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) : ℕ :=
  sInf {n : ℕ | IsStationaryAt hinv s n}

theorem monomialStallIndex_eq_sInf (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) :
    monomialStallIndex hinv s = sInf {n : ℕ | IsStationaryAt hinv s n} :=
  rfl

def monomialIterateUntilStall (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) :
    MarkedBlowupSequenceData p I m E :=
  monomialBlowupIterate hinv s (monomialStallIndex hinv s)

theorem monomialIterateUntilStall_eq_monomialBlowupIterate (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) :
    monomialIterateUntilStall hinv s = monomialBlowupIterate hinv s (monomialStallIndex hinv s) :=
  rfl

theorem monomialStallIndex_eq_zero_of_not_isAdmissibleCenter (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (h : ¬ IsAdmissibleCenter s) : monomialStallIndex hinv s = 0 := by
  have h0 : IsStationaryAt hinv s 0 := (isStationaryAt_iff_not_isAdmissibleCenter hinv s 0).mpr h
  show sInf {n : ℕ | IsStationaryAt hinv s n} = 0
  exact Nat.le_zero.mp (Nat.sInf_le h0)

end

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem monomialStallIndex_eq_monomialStallIndex_empty (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    monomialStallIndex hinv p I m E =
      MarkedBlowupSequenceData.monomialStallIndex hinv (emptyMarkedBlowupSequenceData p I m E) :=
  rfl

theorem monomialBlowupSeq_eq_monomialIterateUntilStall (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialIterateUntilStall hinv (emptyMarkedBlowupSequenceData p I m E) :=
  rfl

end

end FunctorialResolution.EmbeddedResolution

end
