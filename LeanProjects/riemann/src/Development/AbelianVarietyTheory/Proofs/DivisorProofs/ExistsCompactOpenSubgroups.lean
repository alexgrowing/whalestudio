import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.FinAdeleNbhd

theorem exists_prod_openCompact_subset :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (V : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    V ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (N v : Set (v.adicCompletion F))) ∧ (∀ v, IsCompact (N v : Set (v.adicCompletion F))) ∧
      (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ⊆ V := by
  intro F _ _ κ _ V hV
  classical

  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨J, s, hs, hJs⟩ := hV
  set W : Set (FiniteAdeleRing (𝓞 F) F) := ⋂ i, s i with hWdef
  have hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 hs
  have hWV : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, y i ∈ W) → y ∈ V := fun y hy =>
    hJs fun i _ => Set.mem_iInter.1 (hy i) i

  let R : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Type := fun v => v.adicCompletion F
  let A : ∀ v, Set (R v) := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let e := RestrictedProduct.structureMap R A Filter.cofinite
  have he : Continuous e := (RestrictedProduct.isEmbedding_structureMap).continuous
  let p : ∀ v, A v := fun v => ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hep : (e p : FiniteAdeleRing (𝓞 F) F) = 0 := rfl
  have hpre : e ⁻¹' W ∈ 𝓝 p := he.continuousAt.preimage_mem_nhds (by rw [hep]; exact hW)
  rw [nhds_pi, Filter.mem_pi'] at hpre
  obtain ⟨I, t, ht, hIt⟩ := hpre
  have hu : ∀ v, ∃ u ∈ 𝓝 (0 : R v), Subtype.val ⁻¹' u ⊆ t v := fun v =>
    (mem_nhds_subtype (A v) (p v) (t v)).1 (ht v)
  choose u hu0 hut using hu

  have hG : ∀ v, ∃ G : OpenAddSubgroup (R v), (G : Set (R v)) ⊆ u v := fun v =>
    NonarchimedeanAddGroup.is_nonarchimedean _ (hu0 v)
  choose G hGu using hG
  let O : ∀ v, AddSubgroup (R v) := fun v => (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  have hOset : ∀ v, ((O v : AddSubgroup (R v)) : Set (R v)) = A v := fun v => rfl
  have hOopen : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hOcpt : ∀ v, IsCompact (A v) := fun v =>
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let N : ∀ v, AddSubgroup (R v) := fun v => if v ∈ I then (G v).toAddSubgroup ⊓ O v else O v
  have hNO : ∀ v, ∀ x ∈ N v, x ∈ A v := by
    intro v x hx
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true] at hx; exact hx.2
    · simp only [N, hv, if_false] at hx; exact hx
  have hNG : ∀ v ∈ I, ∀ x ∈ N v, x ∈ (G v : Set (R v)) := by
    intro v hv x hx
    simp only [N, hv, if_true] at hx; exact hx.1
  have hNopen : ∀ v, IsOpen (N v : Set (R v)) := by
    intro v
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true, AddSubgroup.coe_inf]
      exact (G v).isOpen.inter (hOopen v)
    · simp only [N, hv, if_false]; exact hOopen v
  have hNcpt : ∀ v, IsCompact (N v : Set (R v)) := by
    intro v
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true, AddSubgroup.coe_inf]
      exact (hOcpt v).inter_left (G v).isClosed
    · simp only [N, hv, if_false]; exact hOcpt v
  refine ⟨N, hNopen, hNcpt, ?_, ?_, ?_⟩
  · filter_upwards [I.eventually_cofinite_notMem] with v hv
    simp only [N, hv, if_false]; rfl
  ·
    let P : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ N v}
    have hPeq : P = {a : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ I → a v ∈ A v} ∩ ⋂ v ∈ I, (fun a : FiniteAdeleRing (𝓞 F) F => a v) ⁻¹' (N v : Set (R v)) := by
      ext a
      simp only [P, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h; exact ⟨fun v _ => hNO v _ (h v), fun v _ => h v⟩
      · rintro ⟨h1, h2⟩ v
        by_cases hv : v ∈ I
        · exact h2 v hv
        · have := h1 v hv
          simp only [N, hv, if_false]; exact this
    have hPopen : IsOpen P := by
      rw [hPeq]
      refine IsOpen.inter (RestrictedProduct.isOpen_forall_imp_mem hOopen) ?_
      exact isOpen_biInter_finset fun v _ => (hNopen v).preimage (RestrictedProduct.continuous_eval v)
    have hP0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ P := fun v => (N v).zero_mem
    have : (Set.univ : Set κ).pi (fun _ => P) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
      set_pi_mem_nhds Set.finite_univ fun i _ => hPopen.mem_nhds hP0
    refine Filter.mem_of_superset this ?_
    intro y hy i v
    exact hy i (Set.mem_univ i) v
  ·
    intro y hy
    apply hWV
    intro i
    have hyi : ∀ v, (y i) v ∈ N v := fun v => hy i v
    let x : ∀ v, A v := fun v => ⟨(y i) v, hNO v _ (hyi v)⟩
    have hex : (e x : FiniteAdeleRing (𝓞 F) F) = y i := rfl
    have hxI : x ∈ (I : Set _).pi t := by
      intro v hv
      apply hut v
      show (y i) v ∈ u v
      exact hGu v (hNG v hv _ (hyi v))
    have h := hIt hxI
    have h' : (e x : FiniteAdeleRing (𝓞 F) F) ∈ W := h
    rw [hex] at h'
    exact h'

end GlobalTheory.FinAdeleNbhd
