import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private def natSuccAbove (j i : ℕ) : ℕ := if i < j then i else i + 1

private theorem natSuccAbove_ne (j i : ℕ) : natSuccAbove j i ≠ j := by
  unfold natSuccAbove
  split_ifs with h <;> omega

private theorem natSuccAbove_inj (j i i' : ℕ) (h : natSuccAbove j i = natSuccAbove j i') : i = i' := by
  unfold natSuccAbove at h
  split_ifs at h <;> omega

private theorem getElem_eraseIdx_natSuccAbove {α : Type u} (l : List α) (j i : ℕ)
    (hi : i < (l.eraseIdx j).length) (hs : natSuccAbove j i < l.length) :
    (l.eraseIdx j)[i]'hi = l[natSuccAbove j i]'hs := by
  unfold natSuccAbove at hs ⊢
  rw [List.getElem_eraseIdx]
  split <;> simp [*]

private def complOrderEmbPreimage (m : ℕ) (S : Finset (Fin m)) (s : Fin m) : Option (Fin (m - S.card)) :=
  if hs : s ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S hs))

private theorem mem_of_complOrderEmbPreimage_eq_none (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (h : complOrderEmbPreimage m S s = none) : s ∈ S := by
  by_contra hs
  unfold complOrderEmbPreimage at h
  rw [dif_neg hs] at h
  simp at h

private theorem complOrderEmb_of_complOrderEmbPreimage_eq_some (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (u : Fin (m - S.card)) (h : complOrderEmbPreimage m S s = some u) : complOrderEmb m S u = s := by
  by_cases hs : s ∈ S
  · exfalso
    unfold complOrderEmbPreimage at h
    rw [dif_pos hs] at h
    simp at h
  · unfold complOrderEmbPreimage at h
    rw [dif_neg hs] at h
    have hu : Classical.choose (exists_complOrderEmb_eq m S hs) = u := Option.some.inj h
    rw [← hu]
    exact Classical.choose_spec (exists_complOrderEmb_eq m S hs)

private def transportSuccAboveToCompl {m : ℕ} (S : Finset (Fin m)) (j : ℕ) (a : ℕ → Option (Fin m))
    (i : ℕ) : Option (Fin (m - S.card)) :=
  (a (natSuccAbove j i)).bind (complOrderEmbPreimage m S)

private theorem transportSuccAboveToCompl_eq_some {m : ℕ} (S : Finset (Fin m)) (j : ℕ)
    (a : ℕ → Option (Fin m)) (i : ℕ) (u : Fin (m - S.card))
    (h : transportSuccAboveToCompl S j a i = some u) : a (natSuccAbove j i) = some (complOrderEmb m S u) := by
  rcases hs : a (natSuccAbove j i) with _ | s
  · exfalso
    unfold transportSuccAboveToCompl at h
    rw [hs] at h
    simp at h
  · have h' : complOrderEmbPreimage m S s = some u := by
      unfold transportSuccAboveToCompl at h
      rw [hs] at h
      exact h
    rw [complOrderEmb_of_complOrderEmbPreimage_eq_some m S s u h']

private theorem transportSuccAboveToCompl_eq_none {m : ℕ} (S : Finset (Fin m)) (j : ℕ)
    (a : ℕ → Option (Fin m)) (i : ℕ) (h : transportSuccAboveToCompl S j a i = none) :
    a (natSuccAbove j i) = none ∨ ∃ s, a (natSuccAbove j i) = some s ∧ s ∈ S := by
  rcases hs : a (natSuccAbove j i) with _ | s
  · exact Or.inl rfl
  · refine Or.inr ⟨s, rfl, ?_⟩
    have h' : complOrderEmbPreimage m S s = none := by
      unfold transportSuccAboveToCompl at h
      rw [hs] at h
      exact h
    exact mem_of_complOrderEmbPreimage_eq_none m S s h'

theorem inStrictNormalCrossingPosition_of_forall_etaleChart {Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (L : List Y.IdealSheafData)
    (h : ∀ x : ↥Y, ∃ (U : Y.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart q U m)
      (a : ℕ → Option (Fin m)),
      (∀ i < L.length, ∀ i' < L.length, ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < L.length), a i = none → restrictIdeal L[i] U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < L.length) (t : Fin m),
        a i = some t → restrictIdeal L[i] U = c.coordIdeal {t})) :
    InStrictNormalCrossingPosition q L := by
  refine (inStrictNormalCrossingPosition_iff q L).mpr ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_exists_etaleChart (h x)⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
  refine isSmoothDivisor_of_locally_coordIdeal _ ?_
  intro x
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := h x
  refine ⟨U, hxU, m, c, ?_⟩
  rcases hai : a i with _ | t
  · exact Or.inl (h2 i hi hai)
  · exact Or.inr ⟨t, h3 i hi t hai⟩

theorem exists_etaleChart_comap_subschemeι_eraseIdx {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (z : ↥((E[j]'hj).subscheme)) :
    ∃ (U : ((E[j]'hj).subscheme).Opens) (_ : z ∈ U) (m : ℕ)
      (c : EtaleChart ((E[j]'hj).subschemeι ≫ p) U m) (a : ℕ → Option (Fin m)),
      (∀ i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ i' < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        a i = none →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length)
        (t : Fin m), a i = some t →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U =
            c.coordIdeal {t}) := by
  classical
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  have hx : (E[j]'hj).subschemeι.base z ∈ (E[j]'hj).support := by
    have hmem : (E[j]'hj).subschemeι.base z ∈ Set.range (E[j]'hj).subschemeι.base :=
      Set.mem_range_self z
    simpa using hmem
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := (hpos ((E[j]'hj).subschemeι.base z)).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  rcases haj : a j with _ | t
  · refine absurd hx ?_
    refine AlgebraicGeometry.Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ ?_ hxU
    rw [← restrictIdeal_eq_comap_ι]
    exact h2 j hj haj
  · have hzmem : z ∈ (E[j]'hj).subschemeι ⁻¹ᵁ V := hxV
    have h2V : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal (E[i]'hi) V = ⊤ :=
      fun i hi hn => restrictIdeal_eq_top_of_le _ hVU (h2 i hi hn)
    have h3V : ∀ (i : ℕ) (hi : i < E.length) (s : Fin m), a i = some s →
        restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {s} :=
      fun i hi s hsm => restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {s} (h3 i hi s hsm)
    have hZV : restrictIdeal (E[j]'hj) V = (c.restrict hVU).coordIdeal {t} := h3V j hj t haj
    have hlen : ∀ i, i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length →
        natSuccAbove j i < E.length := by
      intro i hi
      rw [List.length_map] at hi
      have h0 := List.length_eraseIdx_add_one hj
      unfold natSuccAbove
      split_ifs with hc <;> omega
    have helem : ∀ (i : ℕ)
        (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]'hi =
          (E[natSuccAbove j i]'(hlen i hi)).comap (E[j]'hj).subschemeι := by
      intro i hi
      have hi' : i < (E.eraseIdx j).length := by
        rw [List.length_map] at hi
        exact hi
      have he : (E.eraseIdx j)[i]'hi' = E[natSuccAbove j i]'(hlen i hi) :=
        getElem_eraseIdx_natSuccAbove E j i hi' (hlen i hi)
      rw [List.getElem_map]
      exact congrArg (fun D => D.comap (E[j]'hj).subschemeι) he
    refine ⟨(E[j]'hj).subschemeι ⁻¹ᵁ V, hzmem, m - ({t} : Finset (Fin m)).card,
      (c.restrict hVU).restrictToSubscheme hV (E[j]'hj) {t} hZV,
      transportSuccAboveToCompl {t} j a, ?_, ?_, ?_⟩
    · intro i hi i' hi' u hu hu'
      exact natSuccAbove_inj j i i'
        (h1 (natSuccAbove j i) (hlen i hi) (natSuccAbove j i') (hlen i' hi')
          (complOrderEmb m {t} u) (transportSuccAboveToCompl_eq_some {t} j a i u hu)
          (transportSuccAboveToCompl_eq_some {t} j a i' u hu'))
    · intro i hi hn
      rw [helem i hi]
      rcases transportSuccAboveToCompl_eq_none {t} j a i hn with hnone | ⟨s, hsome, hsmem⟩
      · exact restrictIdeal_comap_subschemeι_eq_top (E[j]'hj) V _
          (h2V (natSuccAbove j i) (hlen i hi) hnone)
      · exfalso
        have h0 : a (natSuccAbove j i) = some t := by
          rw [hsome, Finset.mem_singleton.mp hsmem]
        exact natSuccAbove_ne j i (h1 (natSuccAbove j i) (hlen i hi) j hj t h0 haj)
    · intro i hi u hu
      rw [helem i hi]
      exact (c.restrict hVU).restrictToSubscheme_coordIdeal_singleton hV (E[j]'hj) {t} hZV u
        (E[natSuccAbove j i]'(hlen i hi))
        (h3V (natSuccAbove j i) (hlen i hi) (complOrderEmb m {t} u)
          (transportSuccAboveToCompl_eq_some {t} j a i u hu))

theorem inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) :
    InStrictNormalCrossingPosition ((E[j]'hj).subschemeι ≫ p)
      ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι) :=
  inStrictNormalCrossingPosition_of_forall_etaleChart ((E[j]'hj).subschemeι ≫ p)
    ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)
    (exists_etaleChart_comap_subschemeι_eraseIdx p E hE j hj)

theorem inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (D : X.IdealSheafData) (hD : E[j]'hj = D) :
    InStrictNormalCrossingPosition (D.subschemeι ≫ p)
      ((E.eraseIdx j).map fun F => F.comap D.subschemeι) := by
  subst hD
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx p E hE j hj

end FunctorialResolution.EmbeddedResolution

end
