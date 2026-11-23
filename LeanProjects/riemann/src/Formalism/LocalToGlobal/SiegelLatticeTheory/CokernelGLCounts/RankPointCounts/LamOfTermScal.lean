import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FibSumOf

noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SumFr

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lam_of_termScal {γ γ' : TermDef.Term D u u' F0 what₂} (h : Corank.TermScal D γ γ') : γ'.lam = γ.lam := by
  obtain ⟨p, h1, h2, -⟩ := h
  rw [← h1, ← h2]
  rfl

theorem sumFr_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂)
    (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hP : PrimeHyp D u (Tu D u'))
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hR : IsRowReps D F0 what₂)
    (hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤) :
    SumFr M δ u u' F0 what₂ := by
  intro γ w _ w' hG' _ Z hZ
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, eligRel_holds⟩
  have hclsFin : (clsSet F0 u' γ.lam Z).Finite :=
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin γ.lam γ.mem Z)
  have hfrSub : frPart γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  let S : Set (TermDef.Term D u u' F0 what₂) :=
    {γ' | (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z}
  have hlam : ∀ γ' ∈ S, γ'.lam = γ.lam := fun γ' h => lam_of_termScal h.1.1
  have hrep : ∀ γ' ∈ S, RepIn u u' F0 what₂ γ' Z := fun γ' h => hC hpre γ' w' hG' Z hZ h.1.2 h.2
  have hsub : ∀ γ' ∈ S, PairVal.orbT D u u' F0 what₂ γ' Z ⊆ frPart γ Z := by
    rintro γ' h O ⟨F', hF', hr, rfl⟩
    refine ⟨F', ?_, ⟨γ', h.1.1, hr⟩, ?_⟩
    · have e := hlam γ' h
      rw [e] at hF'
      exact hF'
    · have e := hlam γ' h
      ext F''
      simp only [Set.mem_setOf_eq]
      rw [e]
      exact Iff.rfl
  have horbFin : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Finite := fun γ' h =>
    (hclsFin.subset hfrSub).subset (hsub γ' h)
  have hne : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Nonempty := by
    intro γ' h
    obtain ⟨F', hF', hr⟩ := hrep γ' h
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard = (PairVal.orbT D u u' F0 what₂ γ' Z).ncard := by
    intro γ' h
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ' w' Z h.1.2 hZ (hrep γ' h)]
  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ O ∈ frPart γ Z,
        {γ' : TermDef.Term D u u' F0 what₂ | γ'.lam = γ.lam ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ' Z} := by
      intro γ' h
      obtain ⟨O, hO⟩ := hne γ' h
      simp only [Set.mem_iUnion]
      exact ⟨O, hsub γ' h hO, hlam γ' h, hO⟩
    refine Set.Finite.subset (Set.Finite.biUnion (hclsFin.subset hfrSub) (fun O _ => ?_)) hU
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hbU : (hclsFin.subset hfrSub).toFinset =
      hSfin.toFinset.biUnion (fun γ' => if h : γ' ∈ S then (horbFin γ' h).toFinset else ∅) := by
    ext O
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    constructor
    · rintro ⟨F', hF', ⟨γ', hsc, hr⟩, rfl⟩
      have e := lam_of_termScal hsc
      obtain ⟨Λ, m, c⟩ := γ
      obtain ⟨Λ', m', c'⟩ := γ'
      simp only at e
      subst e
      obtain ⟨hpd, hc⟩ := hr
      have hγ' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) = termOf Λ' m' F' (pd_of_ez hF') := by
        simp only [termOf] at hc ⊢
        rw [← hc]
      have hS' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) ∈ S := by
        refine ⟨⟨hsc, ?_⟩, ?_⟩
        · rw [hγ']
          exact eligAt_termOf Λ' m' hZ hF'
        · rw [hγ']
          exact hD hpre _ w' Z (eligAt_termOf Λ' m' hZ hF') hZ (repIn_termOf Λ' m' hF')
      refine ⟨⟨Λ', m', c'⟩, hS', ?_⟩
      simp only [dif_pos hS', Set.Finite.mem_toFinset]
      exact ⟨F', hF', ⟨hpd, hc⟩, rfl⟩
    · rintro ⟨γ', hγ'S, hO⟩
      have hO' : O ∈ (horbFin γ' hγ'S).toFinset := by simpa only [dif_pos hγ'S] using hO
      exact hsub γ' hγ'S ((Set.Finite.mem_toFinset _).1 hO')
  have hdisj : ∀ γ₁ ∈ hSfin.toFinset, ∀ γ₂ ∈ hSfin.toFinset, γ₁ ≠ γ₂ →
      Disjoint (if h : γ₁ ∈ S then (horbFin γ₁ h).toFinset else ∅)
        (if h : γ₂ ∈ S then (horbFin γ₂ h).toFinset else ∅) := by
    intro γ₁ h₁ γ₂ h₂ hne12
    rw [Set.Finite.mem_toFinset] at h₁ h₂
    rw [dif_pos h₁, dif_pos h₂, Finset.disjoint_left]
    intro O hO₁ hO₂
    rw [Set.Finite.mem_toFinset] at hO₁ hO₂
    exact hne12 (orbT_disj ((hlam γ₁ h₁).trans (hlam γ₂ h₂).symm) hO₁ hO₂)
  have hcount : ((frPart γ Z).ncard : ℝ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ (hclsFin.subset hfrSub), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ' hγ' => ?_)
    have h := (Set.Finite.mem_toFinset hSfin).1 hγ'
    rw [dif_pos h, hnc γ' h, Set.ncard_eq_toFinset_card _ (horbFin γ' h)]
  refine ⟨hclsFin.subset hfrSub, ?_⟩
  haveI : Fintype {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} =>
    ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
  have h1 : ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) =
      ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ' => Set.Finite.mem_toFinset hSfin) _
  have h2 : (((frPart γ Z).ncard : ℝ) : ℂ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) := by
    rw [hcount]
    push_cast
    rfl
  have key := h1.symm.trans h2.symm
  have key' : ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) = ((frPart γ Z).ncard : ℂ) := by
    rw [key]
    push_cast
    rfl
  exact Eq.mpr (congrArg (HasSum _) key'.symm) hs

end SumFr

end Formalism.L2.SG.Pf.FibPart
