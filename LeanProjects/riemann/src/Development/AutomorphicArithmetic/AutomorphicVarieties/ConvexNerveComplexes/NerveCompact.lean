import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveCut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycUnion
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycCone

open Set UpperTheory.V.ConeExtensionAcyclic

private theorem faces_finite {I F : Type} (X : Set F) (A : I → Set F)
    (hfin : {i | (X ∩ A i).Nonempty}.Finite) :
    {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j}.Finite := by
  apply ((hfin.toFinset.powerset : Finset (Finset I)).finite_toSet).subset
  rintro σ ⟨x, hxX, hx⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro j hj
  rw [Set.Finite.mem_toFinset]
  exact ⟨x, hxX, hx j hj⟩

private theorem faces_lt {I F : Type} (X Y : Set F) (A : I → Set F)
    (hfin : {i | (X ∩ A i).Nonempty}.Finite) (hYX : Y ⊆ X) (σ : Finset I)
    (h1 : ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j) (h2 : ¬ ∃ x ∈ Y, ∀ j ∈ σ, x ∈ A j) :
    {σ : Finset I | ∃ x ∈ Y, ∀ j ∈ σ, x ∈ A j}.ncard <
      {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j}.ncard := by
  have hsub : {σ : Finset I | ∃ x ∈ Y, ∀ j ∈ σ, x ∈ A j} ⊆ {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j} := by
    rintro τ ⟨x, hx, hxt⟩
    exact ⟨x, hYX hx, hxt⟩
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2 ⟨σ, h1, h2⟩) (faces_finite X A hfin)

theorem UpperTheory.V.ConeExtensionAcyclic.nerve_compact :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F), IsCompact X → Convex ℝ X → X.Nonempty → (∀ i, IsClosed (A i)) → (∀ i, Convex ℝ (A i)) → {i | (X ∩ A i).Nonempty}.Finite → (∀ x ∈ X, ∃ i, x ∈ A i) → Acyc (nerve X A) := by
  intro I F _ _ X A hc hcv hne hcl hca hfin hcov
  suffices key : ∀ n : ℕ, ∀ X : Set F, {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j}.ncard = n →
      IsCompact X → Convex ℝ X → X.Nonempty → {i | (X ∩ A i).Nonempty}.Finite →
      (∀ x ∈ X, ∃ i, x ∈ A i) → Acyc (nerve X A) by
    exact key _ X rfl hc hcv hne hfin hcov
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hc hcv hne hfin hcov
  by_cases hcone : ∃ x ∈ X, ∀ i, (X ∩ A i).Nonempty → x ∈ A i
  · obtain ⟨x, hxX, hx⟩ := hcone
    obtain ⟨a, ha⟩ := hcov x hxX
    apply acyc_cone _ a
    intro m t ht
    simp only [nerve, Set.mem_setOf_eq] at ht ⊢
    obtain ⟨y, hyX, hy⟩ := ht
    refine ⟨x, hxX, ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa using ha
    | succ k => simpa using hx (t k) ⟨y, hyX, hy k⟩
  · obtain ⟨f, u, i, σ, hi, hiu, hσ, hσu⟩ := nerve_sep X A hc hcv hne hcl hca hfin hcone
    have hcut := nerve_cut X A f u hcv hca
    have step : ∀ (Y : Set F) (τ : Finset I), Y ⊆ X → IsCompact Y → Convex ℝ Y → Y.Nonempty →
        (∃ x ∈ X, ∀ j ∈ τ, x ∈ A j) → (¬ ∃ x ∈ Y, ∀ j ∈ τ, x ∈ A j) → Acyc (nerve Y A) := by
      intro Y τ hYX hYc hYv hYn h1 h2
      have hfinY : {i | (Y ∩ A i).Nonempty}.Finite :=
        hfin.subset (fun k hk => Set.Nonempty.mono (Set.inter_subset_inter hYX subset_rfl) hk)
      exact ih _ ((faces_lt X Y A hfin hYX τ h1 h2).trans_eq hn) Y rfl hYc hYv hYn hfinY
        (fun x hx => hcov x (hYX hx))
    have hfc : Continuous f := f.continuous
    obtain ⟨p, hp⟩ := hi
    obtain ⟨q, hqX, hq⟩ := hσ
    have hpu : f p < u := hiu p hp
    have hqu : u < f q := hσu q hqX hq
    obtain ⟨r, hr, hfr⟩ : u ∈ f '' X :=
      hcv.isPreconnected.intermediate_value hp.1 hqX hfc.continuousOn ⟨hpu.le, hqu.le⟩
    have A1 : Acyc (nerve (X ∩ {x | f x ≤ u}) A) :=
      step _ σ Set.inter_subset_left (hc.inter_right (isClosed_le hfc continuous_const))
        (hcv.inter ((convex_Iic u).linear_preimage f.toLinearMap)) ⟨p, hp.1, hpu.le⟩ ⟨q, hqX, hq⟩
        (fun ⟨x, hx, hxs⟩ => absurd hx.2 (not_le.mpr (hσu x hx.1 hxs)))
    have A2 : Acyc (nerve (X ∩ {x | u ≤ f x}) A) :=
      step _ {i} Set.inter_subset_left (hc.inter_right (isClosed_le continuous_const hfc))
        (hcv.inter ((convex_Ici u).linear_preimage f.toLinearMap)) ⟨q, hqX, hqu.le⟩
        ⟨p, hp.1, fun j hj => (Finset.mem_singleton.mp hj) ▸ hp.2⟩
        (fun ⟨x, hx, hxs⟩ => absurd hx.2 (not_le.mpr (hiu x ⟨hx.1, hxs i (Finset.mem_singleton_self i)⟩)))
    have A0 : Acyc (nerve (X ∩ {x | f x = u}) A) :=
      step _ σ Set.inter_subset_left (hc.inter_right (isClosed_eq hfc continuous_const))
        (hcv.inter ((convex_singleton u).linear_preimage f.toLinearMap)) ⟨r, hr, hfr⟩ ⟨q, hqX, hq⟩
        (fun ⟨x, hx, hxs⟩ => (hσu x hx.1 hxs).ne' hx.2)
    rw [hcut.1]
    exact acyc_union (nerve (X ∩ {x | f x ≤ u}) A) (nerve (X ∩ {x | u ≤ f x}) A)
      (nerve_faceClosed _ _) (nerve_faceClosed _ _) A1 A2 (hcut.2 ▸ A0)
