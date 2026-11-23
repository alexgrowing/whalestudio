import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVb
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.MultiplicityBound

theorem finrank_biSup_indep {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] {t : ι → Submodule K V} (ht : iSupIndep t) (A : Finset ι) :
    Module.finrank K ↥(⨆ σ ∈ A, t σ) = ∑ σ ∈ A, Module.finrank K ↥(t σ) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have hs : (⨆ σ ∈ insert a A, t σ) = t a ⊔ ⨆ σ ∈ A, t σ := by
      rw [Finset.iSup_insert]
    have hd : Disjoint (t a) (⨆ σ ∈ A, t σ) := ht.disjoint_biSup (by simpa using ha)
    rw [hs, ← Submodule.finrank_sup_add_finrank_inf_eq, hd.eq_bot, finrank_bot, add_zero]

open Classical in

noncomputable def goodRows (D : D7) (i : D.nd.Loc) : Finset D.what₂.FT :=
  Finset.univ.filter (fun σ => D.nd.goodRow σ ∧ AtM D.nd D.naut i σ)

theorem dM_eq_sum (D : D7) (hI : Rows.IsotInternal D.what₂) (i : D.nd.Loc) (j : ℕ) (h : D.nd.j i = j) :
    dM D.nd D.naut i = ∑ σ ∈ goodRows D i, Module.finrank ℂ ↥(D.what₂.isot j σ) := by
  classical
  subst h
  have hr := D.nd.j_range i
  have hind : iSupIndep (D.what₂.isot (D.nd.j i)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have hsup : goodPartM D.nd D.naut i = ⨆ σ ∈ goodRows D i, D.what₂.isot (D.nd.j i) σ := by
    unfold goodPartM goodRows
    apply iSup_congr
    intro σ
    simp
  unfold dM
  rw [hsup]
  exact finrank_biSup_indep hind _

theorem sum_mult_le (D : D7) (hZ : SumRepresentations.ConclusionZ D) (i : D.nd.Loc) :
    (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤ (dM D.nd D.naut i : ℝ) := by
  classical
  rcases (D.nd.Zgood i).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  · have hG : HG D.nd D.naut i := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, (D.Zgood_tie i x).1 hx⟩
    have h3 := (hZ i hG).2.2
    rw [← h3, ← Nat.cast_sum]
    apply le_of_eq
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (D.nd.Zgood i))]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos ((D.Zgood_tie i x).1 hx)]
    · intro x _ hx
      rw [if_neg (fun h => hx ((D.Zgood_tie i x).2 h))]

end GlobalTheory.MultiplicityBound

open GlobalTheory.MultiplicityBound in

theorem GlobalTheory.NLink.multLe_of_rank : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ →
    KillingConditions.LocalisationUniqueness D → MultLe L := by
  intro D L h42 hZ hI h2 j hj w hw
  classical
  rcases (D.nd.locs j w).eq_empty_or_nonempty with he | ⟨i0, hi0⟩
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  obtain ⟨hj0, hw0⟩ := (D.nd.locs_mem j w i0).1 hi0
  subst hj0 hw0
  have hr := D.nd.j_range i0
  have hind : iSupIndep (D.what₂.isot (D.nd.j i0)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have h1 : (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤
      ((∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => sum_mult_le D hZ i)
  refine h1.trans ?_
  apply Nat.cast_le.2
  have hdisj : (↑(D.nd.locs (D.nd.j i0) (D.nd.w i0)) : Set D.nd.Loc).PairwiseDisjoint (goodRows D) := by
    intro i hi i' hi' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hσ hσ'
    have hi := (D.nd.locs_mem _ _ i).1 hi
    have hi' := (D.nd.locs_mem _ _ i').1 hi'
    simp only [goodRows, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hσ'
    have htw : TwistedPlaces.TwLoc D i := by
      unfold TwistedPlaces.TwLoc
      rw [hi.2]
      exact hw
    exact hne (h2 i i' htw (hi.1.trans hi'.1.symm) (hi.2.trans hi'.2.symm) σ hσ.1 hσ.2 hσ'.2)
  calc (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i)
      = ∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ σ ∈ goodRows D i,
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        Finset.sum_congr rfl (fun i hi => dM_eq_sum D hI i _ ((D.nd.locs_mem _ _ i).1 hi).1)
    _ = ∑ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        (Finset.sum_biUnion hdisj).symm
    _ = Module.finrank ℂ ↥(⨆ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          D.what₂.isot (D.nd.j i0) σ) :=
        (finrank_biSup_indep hind _).symm
    _ ≤ Module.finrank ℂ (D.what₂.Mj (D.nd.j i0)) := Submodule.finrank_le _
    _ = L.zeroSpaceRankAtPlace (D.nd.j i0) (D.nd.w i0) := by
        unfold SizeData₂.zeroSpaceRankAtPlace Rows.Data.Zj
        rw [← D.nd.mu_w i0,
          LinearMap.finrank_range_of_inj (Formalism.MainNotions.J.theta_injective_of_scalars D h42 hI i0 hj)]
