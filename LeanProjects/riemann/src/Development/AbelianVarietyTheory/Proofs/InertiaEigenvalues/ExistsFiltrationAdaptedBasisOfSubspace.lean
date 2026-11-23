import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AdaptedBasis

variable {k M : Type} [Field k] [AddCommGroup M] [Module k M]

theorem exists_adapted_family (F : ℤ → Submodule k M) (hF : Antitone F) :
    ∀ (n : ℕ) (D : Submodule k M) [FiniteDimensional k D], Module.finrank k D = n →
    (∀ x ∈ D, ∃ a, x ∈ F a) → (∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) →
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M) (h : ι → ℤ), LinearIndependent k v ∧
      Submodule.span k (Set.range v) = D ∧ (∀ j, v j ∈ F (h j) ∧ v j ∉ F (h j + 1)) ∧
      ∀ a, D ⊓ F a ≤ Submodule.span k (v '' {j | a ≤ h j}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ hn hex hsep
  by_cases hD : D = ⊥
  · subst hD
    refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, linearIndependent_empty_type, ?_,
      fun j => j.elim, fun a => by simp⟩
    simp
  have hne : ∃ a, D ≤ F a := by
    let b := Module.finBasis k D
    have hb : ∀ i, ∃ a, (b i : M) ∈ F a := fun i => hex _ (b i).2
    choose c hc using hb
    obtain ⟨m, hm⟩ := Finite.exists_le (fun i => OrderDual.toDual (c i))
    refine ⟨OrderDual.ofDual m, ?_⟩
    intro x hx
    have hx' : (⟨x, hx⟩ : D) ∈ Submodule.span k (Set.range b) := by
      rw [b.span_eq]; trivial
    have : (Submodule.span k (Set.range b)).map D.subtype ≤ F (OrderDual.ofDual m) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hF (hm i) (hc i)
    exact this ⟨_, hx', rfl⟩
  have hbdd : ∃ b, ∀ z, D ≤ F z → z ≤ b := by
    obtain ⟨x, hxD, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    have : ¬ ∀ a, x ∈ F a := fun h => hx0 (hsep x hxD h)
    push_neg at this
    obtain ⟨a, ha⟩ := this
    refine ⟨a, fun z hz => ?_⟩
    by_contra hlt
    exact ha (hF (le_of_not_ge hlt) (hz hxD))
  obtain ⟨a₀, ha₀, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  set D' := D ⊓ F (a₀ + 1) with hD'
  have hD'D : D' ≤ D := inf_le_left
  have hlt : D' < D := by
    refine lt_of_le_of_ne hD'D fun heq => ?_
    have : D ≤ F (a₀ + 1) := heq ▸ inf_le_right
    have := hmax _ this
    omega
  haveI : FiniteDimensional k D' := Submodule.finiteDimensional_of_le hD'D
  obtain ⟨ι, _, v, h, hli, hspan, hdeg, hfil⟩ :=
    ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) D' rfl
      (fun x hx => hex x (hD'D hx)) (fun x hx => hsep x (hD'D hx))
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl D'
  set C := C' ⊓ D with hC
  have hCD : C ≤ D := inf_le_right
  have hdisj : Disjoint D' C := hC'.disjoint.mono_right inf_le_left
  have hsup : D' ⊔ C = D := by
    rw [hC, ← sup_inf_assoc_of_le _ hD'D, hC'.sup_eq_top, top_inf_eq]
  haveI : FiniteDimensional k C := Submodule.finiteDimensional_of_le hCD
  let bC := Module.finBasis k C
  let c : Fin (Module.finrank k C) → M := fun i => (bC i : M)
  have hcli : LinearIndependent k c := bC.linearIndependent.map' C.subtype C.ker_subtype
  have hcspan : Submodule.span k (Set.range c) = C := by
    have : Set.range c = C.subtype '' Set.range bC := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, bC.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hdeg' : ∀ j, a₀ + 1 ≤ h j := by
    intro j
    by_contra hj
    push_neg at hj
    have hvj : v j ∈ D' := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact (hdeg j).2 (hF (show h j + 1 ≤ a₀ + 1 by omega) (Submodule.mem_inf.mp hvj).2)
  refine ⟨ι ⊕ Fin (Module.finrank k C), inferInstance, Sum.elim v c,
    Sum.elim h (fun _ => a₀), ?_, ?_, ?_, ?_⟩
  · exact hli.sum_type hcli (by rw [hspan, hcspan]; exact hdisj)
  · rw [Set.Sum.elim_range, Submodule.span_union, hspan, hcspan, hsup]
  · rintro (j | i)
    · exact hdeg j
    · refine ⟨ha₀ (hCD (bC i).2), fun hmem => ?_⟩
      have h1 : c i ∈ D' := ⟨hCD (bC i).2, hmem⟩
      have h2 : c i = 0 := (Submodule.disjoint_def.mp hdisj) _ h1 (bC i).2
      exact hcli.ne_zero i h2
  · intro a x hx
    by_cases ha : a ≤ a₀
    · have hall : {j : ι ⊕ Fin (Module.finrank k C) | a ≤ Sum.elim h (fun _ => a₀) j} = Set.univ := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rcases j with j | i
        · have := hdeg' j; simp only [Sum.elim_inl]; omega
        · simpa using ha
      rw [hall, Set.image_univ, Set.Sum.elim_range, Submodule.span_union, hspan, hcspan, hsup]
      exact hx.1
    · push_neg at ha
      have hx' : x ∈ D' ⊓ F a := ⟨⟨hx.1, hF (by omega) hx.2⟩, hx.2⟩
      refine Submodule.span_mono ?_ (hfil a hx')
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨Sum.inl j, hj, rfl⟩

end GlobalTheory.AdaptedBasis

namespace GlobalTheory.AdaptedBasis

theorem exists_adapted_basis {k M : Type} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hex : ∀ x ∈ D, ∃ a, x ∈ F a) (hsep : ∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) :
    ∃ (b : Module.Basis (Fin (Module.finrank k D)) k D) (h : Fin (Module.finrank k D) → ℤ),
      (∀ j, (b j : M) ∈ F (h j) ∧ (b j : M) ∉ F (h j + 1)) ∧
      ∀ (a : ℤ) (x : D), (x : M) ∈ F a → ∀ j, b.repr x j ≠ 0 → a ≤ h j := by
  classical
  obtain ⟨ι, _, v, h, hli, hspan, hdeg, hfil⟩ :=
    exists_adapted_family F hF _ D rfl hex hsep
  let b0 : Module.Basis ι k D := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hb0 : ∀ i, (b0 i : M) = v i := fun i => by
    simp [b0, Module.Basis.span_apply]
  let e : ι ≃ Fin (Module.finrank k D) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b0).symm
  refine ⟨b0.reindex e, fun j => h (e.symm j), fun j => ?_, fun a x hx j hj => ?_⟩
  · rw [Module.Basis.reindex_apply, hb0]
    exact hdeg _
  · rw [Module.Basis.repr_reindex_apply] at hj
    have hxs : (x : M) ∈ Submodule.span k (v '' {i | a ≤ h i}) := hfil a ⟨x.2, hx⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination k).mp hxs
    have hrepr : b0.repr x = l := by
      have : x = Finsupp.linearCombination k b0 l := by
        apply Subtype.ext
        have h1 := Finsupp.apply_linearCombination k D.subtype b0 l
        simp only [Submodule.subtype_apply] at h1
        have hv : (⇑D.subtype ∘ ⇑b0) = v := funext hb0
        rw [h1, hv, hlx]
      rw [this, b0.repr_linearCombination]
    rw [hrepr] at hj
    exact hl (Finsupp.mem_support_iff.mpr hj)

end GlobalTheory.AdaptedBasis
