import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem support_comap_subset_preimage {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (D : X.IdealSheafData) :
    ((D.comap π).support : Set ↥X₁) ⊆ ⇑π ⁻¹' (D.support : Set ↥X) := by
  simp

theorem support_strictTransform_subset_preimage {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    ((Blowup.strictTransform π Z D).support : Set ↥X₁) ⊆ ⇑π ⁻¹' (D.support : Set ↥X) := by
  refine subset_trans ?_ (support_comap_subset_preimage π D)
  intro x hx
  have h1 : stalkIdeal (Blowup.strictTransform π Z D) x ≠ ⊤ :=
    (mem_support_iff_stalkIdeal_ne_top (Blowup.strictTransform π Z D) x).mp hx
  have h2 : stalkIdeal (D.comap π) x ≤ stalkIdeal (Blowup.strictTransform π Z D) x :=
    stalkIdeal_mono (comap_le_strictTransform π Z D) x
  have h3 : stalkIdeal (D.comap π) x ≠ ⊤ := by
    intro htop
    rw [htop, top_le_iff] at h2
    exact h1 h2
  exact (mem_support_iff_stalkIdeal_ne_top (D.comap π) x).mpr h3

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}

@[simp]
theorem EtaleChart.map_restrict {U : X.Opens} {n : ℕ} (c : EtaleChart p U n)
    {V : X.Opens} (hVU : V ≤ U) :
    (c.restrict hVU).map = X.homOfLE hVU ≫ c.map :=
  c.restrict_map hVU

theorem EtaleChart.coordIdeal_restrict {U : X.Opens} {n : ℕ} (c : EtaleChart p U n)
    {V : X.Opens} (hVU : V ≤ U) (S : Finset (Fin n)) :
    (c.restrict hVU).coordIdeal S = (c.coordIdeal S).comap (X.homOfLE hVU) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, c.restrict_map hVU]
  simp only [Scheme.IdealSheafData.comap_comp]

private theorem getElemOpt_append_length_add.{v} {α : Type v} (L₂ : List α) :
    ∀ (L₁ : List α) (i : ℕ), (L₁ ++ L₂)[L₁.length + i]? = L₂[i]? := by
  intro L₁
  induction L₁ with
  | nil => intro i; simp
  | cons b L ih =>
      intro i
      have hlen : (b :: L).length + i = (L.length + i) + 1 := by
        simp only [List.length_cons]; omega
      rw [List.cons_append, hlen, List.getElem?_cons_succ]
      exact ih i

private theorem getElem_append_length_add.{v} {α : Type v} (L₁ L₂ : List α) (i : ℕ)
    (hi : i < L₂.length) (hi' : L₁.length + i < (L₁ ++ L₂).length) :
    (L₁ ++ L₂)[L₁.length + i]'hi' = L₂[i]'hi := by
  have h1 := getElemOpt_append_length_add L₂ L₁ i
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h1
  exact Option.some.inj h1

theorem HasStrictNormalCrossingsWith.of_append {Z : X.IdealSheafData} {L₁ L₂ : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z (L₁ ++ L₂)) : HasStrictNormalCrossingsWith p Z L₂ := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩ := h.exists_etaleChart hx
  refine ⟨U, hxU, m, c, fun i => a (L₁.length + i), S, ?_, ?_, ?_, hZ⟩
  · intro i hi j hj t hti htj
    have hi' : L₁.length + i < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have hj' : L₁.length + j < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have heq := hinj _ hi' _ hj' t hti htj
    omega
  · intro i hi hni
    have hi' : L₁.length + i < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have h2 := hnone _ hi' hni
    rwa [getElem_append_length_add L₁ L₂ i hi hi'] at h2
  · intro i hi t hti
    have hi' : L₁.length + i < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have h2 := hsome _ hi' t hti
    rwa [getElem_append_length_add L₁ L₂ i hi hi'] at h2

private theorem hasStrictNormalCrossingsWith_cons_of_disjoint_support {Z : X.IdealSheafData}
    {M : List X.IdealSheafData} (h : HasStrictNormalCrossingsWith p Z M) {D : X.IdealSheafData}
    (hD : (D.support : Set ↥X) ∩ (Z.support : Set ↥X) = ∅) :
    HasStrictNormalCrossingsWith p Z (D :: M) := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZU⟩ := h.exists_etaleChart hx
  have hxD : x ∉ (D.support : Set ↥X) := by
    intro hxD
    have hmem : x ∈ (D.support : Set ↥X) ∩ (Z.support : Set ↥X) := ⟨hxD, hx⟩
    rw [hD] at hmem
    exact hmem
  obtain ⟨V, hVU, hxV, hVD⟩ :
      ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧ ∀ y : ↥X, y ∈ V → y ∉ D.support := by
    refine ⟨⟨(U : Set ↥X) ∩ ((D.support : Set ↥X))ᶜ,
        U.2.inter D.support.2.isOpen_compl⟩, ?_, ⟨hxU, hxD⟩, ?_⟩
    · intro y hy
      exact hy.1
    · intro y hy
      exact hy.2
  refine ⟨V, hxV, m, c.restrict hVU, fun i => if i = 0 then none else a (i - 1), S,
    ?_, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    cases i with
    | zero => simp at hti
    | succ i' =>
      cases j with
      | zero => simp at htj
      | succ j' =>
        have hi' : i' < M.length := by
          simp only [List.length_cons] at hi
          omega
        have hj' : j' < M.length := by
          simp only [List.length_cons] at hj
          omega
        have hti' : a i' = some t := by simpa using hti
        have htj' : a j' = some t := by simpa using htj
        have heq := hinj i' hi' j' hj' t hti' htj'
        omega
  · intro i hi hni
    cases i with
    | zero =>
      refine (restrictIdeal_eq_top_iff_forall_notMem_support _ V).mpr ?_
      intro y hy
      exact hVD y hy
    | succ i' =>
      have hi' : i' < M.length := by
        simp only [List.length_cons] at hi
        omega
      have ha : a i' = none := by simpa using hni
      have key : restrictIdeal (M[i']'hi') U = ⊤ := hnone i' hi' ha
      show restrictIdeal (M[i']'hi') V = ⊤
      rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, key]
      simp
  · intro i hi t hti
    cases i with
    | zero => simp at hti
    | succ i' =>
      have hi' : i' < M.length := by
        simp only [List.length_cons] at hi
        omega
      have ha : a i' = some t := by simpa using hti
      have key : restrictIdeal (M[i']'hi') U = c.coordIdeal {t} := hsome i' hi' t ha
      show restrictIdeal (M[i']'hi') V = (c.restrict hVU).coordIdeal {t}
      rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, key, EtaleChart.coordIdeal_restrict]
  · rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, hZU, EtaleChart.coordIdeal_restrict]

theorem HasStrictNormalCrossingsWith.append_of_support_disjoint {Z : X.IdealSheafData} {N : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z N) {L : List X.IdealSheafData}
    (hL : ∀ D ∈ L, (D.support : Set ↥X) ∩ (Z.support : Set ↥X) = ∅) :
    HasStrictNormalCrossingsWith p Z (L ++ N) := by
  revert hL
  induction L with
  | nil =>
      intro _
      exact h
  | cons D L ih =>
      intro hL
      exact hasStrictNormalCrossingsWith_cons_of_disjoint_support
        (ih fun E hE => hL E (List.mem_cons.mpr (Or.inr hE)))
        (hL D (List.mem_cons.mpr (Or.inl rfl)))

end

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem boundary_length (u : MarkedBlowupSequenceData p I m E) (t : ℕ) (ht : t ≤ u.length) :
    (u.boundary t).length = E.length + t := by
  revert ht
  induction t with
  | zero =>
      intro _
      simp [u.boundary_zero]
  | succ j ih =>
      intro ht
      have hj : j < u.length := ht
      rw [u.boundary_succ j hj, List.length_append, List.length_map, ih (le_of_lt hj)]
      simp only [List.length_cons, List.length_nil]
      omega

theorem index_lt_boundary_length (u : MarkedBlowupSequenceData p I m E) {t : ℕ} (ht : t ≤ u.length)
    {i : ℕ} (hi : i < E.length) : i < (u.boundary t).length := by
  rw [u.boundary_length t ht]
  omega

theorem boundary_succ_drop (u : MarkedBlowupSequenceData p I m E) {t : ℕ} (ht : t < u.length)
    (n : ℕ) (hn : n ≤ (u.boundary t).length) :
    (u.boundary (t + 1)).drop n =
      ((u.boundary t).drop n).map (Blowup.strictTransform (u.map t) (u.center t)) ++
        [Blowup.exceptionalIdeal (u.map t) (u.center t)] := by
  have hlen : n ≤ ((u.boundary t).map (Blowup.strictTransform (u.map t) (u.center t))).length := by
    rw [List.length_map]
    exact hn
  rw [u.boundary_succ t ht, List.drop_append_of_le_length hlen, ← List.map_drop]

theorem preimage_iUnion_support_boundary_subset (u : MarkedBlowupSequenceData p I m E)
    (hN : ∀ i ≤ u.length, IsLocallyNoetherian (u.obj i)) {t : ℕ} (ht : t < u.length) :
    ⇑(u.map t) ⁻¹' (⋃ D ∈ u.boundary t, (D.support : Set ↥(u.obj t))) ⊆
      ⋃ D ∈ u.boundary (t + 1), (D.support : Set ↥(u.obj (t + 1))) := by
  have hlocNoeth : IsLocallyNoetherian (u.obj (t + 1)) := hN (t + 1) ht
  intro x hx
  obtain ⟨D, hD, hxD0⟩ := Set.mem_iUnion₂.mp (Set.mem_preimage.mp hx)
  have hxD : ⇑(u.map t) x ∈ ((D.support : Set ↥(u.obj t))) := hxD0
  by_cases hc : ⇑(u.map t) x ∈ ((u.center t).support : Set ↥(u.obj t))
  · have hmem : Blowup.exceptionalIdeal (u.map t) (u.center t) ∈ u.boundary (t + 1) := by
      rw [u.boundary_succ t ht, List.mem_append]
      exact Or.inr (List.mem_singleton_self _)
    have h2 : x ∈ ((Blowup.exceptionalIdeal (u.map t) (u.center t)).support : Set ↥(u.obj (t + 1))) := by
      rw [Blowup.exceptionalIdeal_eq_comap]
      have hEq : ((((u.center t).comap (u.map t)).support) : Set ↥(u.obj (t + 1)))
          = ⇑(u.map t) ⁻¹' ((u.center t).support : Set ↥(u.obj t)) := by
        simp
      rw [hEq]
      exact hc
    exact Set.mem_iUnion₂.mpr ⟨_, hmem, h2⟩
  · have hmem : Blowup.strictTransform (u.map t) (u.center t) D ∈ u.boundary (t + 1) := by
      rw [u.boundary_succ t ht, List.mem_append]
      refine Or.inl ?_
      rw [List.mem_map]
      exact ⟨D, hD, rfl⟩
    have h2 : x ∈ ((Blowup.strictTransform (u.map t) (u.center t) D).support : Set ↥(u.obj (t + 1))) := by
      rw [support_strictTransform_eq_closure_preimage (u.map t) (u.center t) D]
      exact subset_closure (Set.mem_preimage.mpr (Set.mem_sdiff_of_mem hxD hc))
    exact Set.mem_iUnion₂.mpr ⟨_, hmem, h2⟩

private theorem eq_of_exceptionalIdeal_pow_mul_eq_mul {Y Y' : Scheme.{u}} {π : Y' ⟶ Y}
    {Z : Y.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π Z) (n : ℕ) {A B : Y'.IdealSheafData}
    (e : Blowup.exceptionalIdeal π Z ^ n * A = Blowup.exceptionalIdeal π Z ^ n * B) : A = B := by
  rw [Blowup.exceptionalIdeal_eq_comap] at e
  exact eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul h.1 n e

private theorem projectionToBase_eq_projectionToBase_toBlowupSequenceData (u : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    u.proj i = u.toBlowupSequenceData.projectionToBase i := by
  induction i with
  | zero => rw [u.proj_zero, BlowupSequenceData.projectionToBase_zero]
  | succ j ih => rw [u.proj_succ j, BlowupSequenceData.projectionToBase_succ, ih]

private theorem toBlowupSequenceData_boundary_eq_boundary (u : MarkedBlowupSequenceData p I m E) :
    ∀ i, i ≤ u.length → u.toBlowupSequenceData.boundaryFrom E i = u.boundary i := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.boundary_zero, u.boundary_zero]
  | succ j ih =>
      intro hj
      have hjlt : j < u.length := hj
      rw [BlowupSequenceData.boundary_succ, ih (le_of_lt hjlt), u.boundary_succ j hjlt]

private theorem toBlowupSequenceData_controlledTransform_eq_ideal (u : MarkedBlowupSequenceData p I m E) :
    ∀ i, i ≤ u.length → u.toBlowupSequenceData.controlledTransform I m i = u.ideal i := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.controlledTransform_zero, u.ideal_zero]
  | succ j ih =>
      intro hj
      have hjlt : j < u.length := hj
      have hIH : u.toBlowupSequenceData.controlledTransform I m j = u.ideal j := ih (le_of_lt hjlt)
      have hex : ∃ B : (u.obj (j + 1)).IdealSheafData,
          Blowup.exceptionalIdeal (u.map j) (u.center j) ^ m * B =
            (u.toBlowupSequenceData.controlledTransform I m j).comap (u.map j) := by
        refine ⟨u.ideal (j + 1), ?_⟩
        rw [hIH]
        exact u.ideal_succ j hjlt
      have key := u.toBlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ I m j hex
      refine eq_of_exceptionalIdeal_pow_mul_eq_mul (u.isBlowup j hjlt) m ?_
      rw [key, hIH]
      exact (u.ideal_succ j hjlt).symm

theorem isMarked (u : MarkedBlowupSequenceData p I m E) : u.toBlowupSequenceData.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨u.ideal (i + 1), ?_⟩
    rw [toBlowupSequenceData_controlledTransform_eq_ideal u i (le_of_lt hi)]
    exact u.ideal_succ i hi
  · intro i hi
    rw [toBlowupSequenceData_controlledTransform_eq_ideal u i (le_of_lt hi)]
    exact u.center_order i hi
  · intro i hi
    have h := u.center_smooth i hi
    rwa [projectionToBase_eq_projectionToBase_toBlowupSequenceData u i] at h
  · intro i hi
    have h := u.center_snc i hi
    rwa [projectionToBase_eq_projectionToBase_toBlowupSequenceData u i, ← toBlowupSequenceData_boundary_eq_boundary u i (le_of_lt hi)] at h

private theorem getElemOpt_map_append.{v, w} {α : Type v} {β : Type w} (f : α → β) (T : List β) :
    ∀ (L : List α) (i : ℕ), i < L.length → (List.map f L ++ T)[i]? = Option.map f (L[i]?) := by
  intro L
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons a L ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ j =>
          have hj : j < L.length := by
            simp only [List.length_cons] at hi
            omega
          simp only [List.map_cons, List.cons_append, List.getElem?_cons_succ]
          exact ih j hj

private theorem getElem_map_append.{v, w} {α : Type v} {β : Type w} (f : α → β)
    (L : List α) (T : List β) (i : ℕ) (hi : i < L.length)
    (hi' : i < (List.map f L ++ T).length) :
    (List.map f L ++ T)[i]'hi' = f (L[i]'hi) := by
  have h := getElemOpt_map_append f T L i hi
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h
  simpa using h

theorem orderAtLeastLocus_disjoint_boundary_of_le (u : MarkedBlowupSequenceData p I m E)
    (hdesc : ∀ t < u.length,
      orderAtLeastLocus (u.ideal (t + 1)) m ⊆ ⇑(u.map t) ⁻¹' orderAtLeastLocus (u.ideal t) m)
    {i : ℕ} (hi : i < E.length) {r : ℕ} (hr : r ≤ u.length)
    (hsep : orderAtLeastLocus (u.ideal r) m ∩
        ((((u.boundary r)[i]'(u.index_lt_boundary_length hr hi)).support :
          Set ↥(u.obj r))) = ∅) :
    ∀ t, r ≤ t → ∀ ht : t ≤ u.length,
      orderAtLeastLocus (u.ideal t) m ∩
        ((((u.boundary t)[i]'(u.index_lt_boundary_length ht hi)).support :
          Set ↥(u.obj t))) = ∅ := by
  intro t hrt
  induction t, hrt using Nat.le_induction with
  | base =>
      intro ht
      exact hsep
  | succ t hrt ih =>
      intro ht
      have htlt : t < u.length := ht
      have ihy := ih (le_of_lt htlt)
      have hxl : i < (u.boundary t).length :=
        u.index_lt_boundary_length (le_of_lt htlt) hi
      have hlen2 : i < (List.map (Blowup.strictTransform (u.map t) (u.center t)) (u.boundary t)
          ++ [Blowup.exceptionalIdeal (u.map t) (u.center t)]).length := by
        rw [List.length_append, List.length_map]
        omega
      have hbeq : (u.boundary (t + 1))[i]'(u.index_lt_boundary_length ht hi)
          = Blowup.strictTransform (u.map t) (u.center t) ((u.boundary t)[i]'hxl) := by
        refine Eq.trans (List.getElem_of_eq (u.boundary_succ t htlt)
          (u.index_lt_boundary_length ht hi)) ?_
        exact getElem_map_append (Blowup.strictTransform (u.map t) (u.center t))
          (u.boundary t) [Blowup.exceptionalIdeal (u.map t) (u.center t)] i hxl hlen2
      refine Set.eq_empty_of_subset_empty ?_
      rintro x ⟨hx1, hx2⟩
      rw [hbeq] at hx2
      have hx1' : ⇑(u.map t) x ∈ orderAtLeastLocus (u.ideal t) m :=
        Set.mem_preimage.mp (hdesc t htlt hx1)
      have hx2' : ⇑(u.map t) x ∈ ((((u.boundary t)[i]'hxl).support : Set ↥(u.obj t))) :=
        Set.mem_preimage.mp
          (support_strictTransform_subset_preimage (u.map t) (u.center t)
            ((u.boundary t)[i]'hxl) hx2)
      have hfalse : (⇑(u.map t) x) ∈ (∅ : Set ↥(u.obj t)) := by
        rw [← ihy]
        exact Set.mem_inter hx1' hx2'
      simp at hfalse

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
