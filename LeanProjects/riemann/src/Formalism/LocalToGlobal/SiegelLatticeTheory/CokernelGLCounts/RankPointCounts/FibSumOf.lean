import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOrbTTermOf

noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fibSum_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.FCount.FibSum M δ u u' F0 what₂ := by
  intro hA hT hP hN hR hE w hG Z hZ hfin
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, hE⟩
  let S : Set (TermDef.Term D u u' F0 what₂) := {γ | EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z}
  have hrep : ∀ γ ∈ S, RepIn u u' F0 what₂ γ Z := fun γ hγ => hC hpre γ w hG Z hZ hγ.1 hγ.2
  have hclsFin : ∀ Λ ∈ what₂, (clsSet F0 u' Λ Z).Finite := fun Λ hΛ =>
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin Λ hΛ)
  have hsub : ∀ γ : TermDef.Term D u u' F0 what₂,
      PairVal.orbT D u u' F0 what₂ γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro γ O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  have horbFin : ∀ γ : TermDef.Term D u u' F0 what₂, (PairVal.orbT D u u' F0 what₂ γ Z).Finite := fun γ =>
    (hclsFin γ.lam γ.mem).subset (hsub γ)
  have hne : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ Z).Nonempty := by
    intro γ hγ
    obtain ⟨F', hF', hr⟩ := hrep γ hγ
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard = (PairVal.orbT D u u' F0 what₂ γ Z).ncard := by
    intro γ hγ
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ w Z hγ.1 hZ (hrep γ hγ)]

  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ Λ ∈ (what₂ : Set (Submodule (𝓞 D.host.E) (VS D).V)), ⋃ O ∈ clsSet F0 u' Λ Z,
        {γ : TermDef.Term D u u' F0 what₂ | γ.lam = Λ ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ Z} := by
      intro γ hγ
      obtain ⟨O, hO⟩ := hne γ hγ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨γ.lam, γ.mem, O, hsub γ hO, rfl, hO⟩
    refine Set.Finite.subset ?_ hU
    refine Set.Finite.biUnion what₂.finite_toSet (fun Λ hΛ => Set.Finite.biUnion (hclsFin Λ hΛ) (fun O _ => ?_))
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hrow : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
      ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) = ((clsSet F0 u' Λ Z).ncard : ℝ) := by
    intro Λ hΛ
    have hbU : (hclsFin Λ hΛ).toFinset =
        (hSfin.toFinset.filter (fun γ => γ.lam = Λ)).biUnion (fun γ => (horbFin γ).toFinset) := by
      ext O
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨F', hF', rfl⟩
        refine ⟨termOf Λ hΛ F' (pd_of_ez hF'), ⟨⟨eligAt_termOf Λ hΛ hZ hF', ?_⟩, rfl⟩,
          mem_orbT_termOf Λ hΛ hF'⟩
        exact hD hpre _ w Z (eligAt_termOf Λ hΛ hZ hF') hZ (repIn_termOf Λ hΛ hF')
      · rintro ⟨γ, ⟨-, hγΛ⟩, hO⟩
        have := hsub γ hO
        rw [hγΛ] at this
        exact this
    have hdisj : ∀ γ₁ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ), ∀ γ₂ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        γ₁ ≠ γ₂ → Disjoint (horbFin γ₁).toFinset (horbFin γ₂).toFinset := by
      intro γ₁ h₁ γ₂ h₂ hne12
      rw [Finset.disjoint_left]
      intro O hO₁ hO₂
      rw [Set.Finite.mem_toFinset] at hO₁ hO₂
      exact hne12 (orbT_disj ((Finset.mem_filter.1 h₁).2.trans (Finset.mem_filter.1 h₂).2.symm) hO₁ hO₂)
    rw [Set.ncard_eq_toFinset_card _ (hclsFin Λ hΛ), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Set.ncard_eq_toFinset_card _ (horbFin γ)]

  have hreal : ∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
      CntLocal.nu (CntLocal.Tn u') F0 what₂ Z := by
    have e1 : ∀ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) := by
      intro γ hγ
      rw [hnc γ ((Set.Finite.mem_toFinset hSfin).1 hγ)]
      rfl
    rw [Finset.sum_congr rfl e1]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun γ : TermDef.Term D u u' F0 what₂ => γ.lam) (t := what₂)
      (fun γ _ => γ.mem)]
    have e2 : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) =
        PairVal.massRow D F0 what₂ Λ * ((clsSet F0 u' Λ Z).ncard : ℝ) := by
      intro Λ hΛ
      rw [← hrow Λ hΛ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun γ hγ => ?_)
      rw [(Finset.mem_filter.1 hγ).2]
    rw [Finset.sum_congr rfl e2]
    unfold CntLocal.nu PairVal.massRow
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun Λ _ => ?_)
    rw [Set.ncard_def, ← cntE_eq]
    unfold Formalism.MainNotions.S.Cnt.massRows
    ring
  haveI : Fintype {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} =>
    (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
  have h1 : ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) =
      ∑ γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z},
        (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ => Set.Finite.mem_toFinset hSfin) _
  have h2 : ((∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) : ℝ) : ℂ) =
      ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) := by
    push_cast
    rfl
  have key := h1.symm.trans (h2.symm.trans (congrArg (fun x : ℝ => (x : ℂ)) hreal))
  exact Eq.mpr (congrArg (HasSum _) key.symm) hs

end Count

end Formalism.L2.SG.Pf.FibPart
