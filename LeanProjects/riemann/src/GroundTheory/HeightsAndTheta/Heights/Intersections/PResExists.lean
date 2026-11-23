import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StResExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.SchemeRes
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjLogResCOfCR
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IfaceInh
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_forms_span {P : Ideal (MRing ι ℂ)} (hP : NumbersDVR.IsMultiHomogIdeal P) :
    ∃ (t : ℕ) (G : Fin t → MRing ι ℂ), (∀ i, ∃ a, ReciprocityTheory.AnForm.R.IsMultiHomog (G i) a) ∧
      Ideal.span (Set.range G) = P := by
  classical
  obtain ⟨S, hS, hPS⟩ := (Bridge.isMultiHomogIdeal_iff P).mp hP
  obtain ⟨T, hTS, hT⟩ : ∃ T : Finset (MRing ι ℂ), (T : Set (MRing ι ℂ)) ⊆ S ∧
      Ideal.span S = Ideal.span (T : Set (MRing ι ℂ)) := by
    have hfg : (Ideal.span S).FG := by
      rw [← hPS]
      exact IsNoetherian.noetherian P
    exact (Submodule.fg_span_iff_fg_span_finset_subset S).mp hfg
  refine ⟨T.card, fun i => (T.equivFin.symm i).1, fun i => hS _ (hTS (T.equivFin.symm i).2), ?_⟩
  have hrange : Set.range (fun i => (T.equivFin.symm i).1) = (T : Set (MRing ι ℂ)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).2
    · intro hf
      exact ⟨T.equivFin ⟨f, hf⟩, by simp⟩
  rw [hrange, ← hT, hPS]

theorem isEmpty_sigma [IsEmpty K] : IsEmpty (Σ k, ι k) := ⟨fun q => isEmptyElim q.1⟩

attribute [local instance] isEmpty_sigma

theorem eq_bot_of_isEmpty [IsEmpty K] {P : Ideal (MRing ι ℂ)} (hP : P.IsPrime) : P = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot, eq_C_of_isEmpty f]
  by_contra h
  have hc : coeff 0 f ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  refine hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hf ?_)
  rw [eq_C_of_isEmpty f]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem ringKrullDim_bot_of_isEmpty [IsEmpty K] :
    ringKrullDim (MRing ι ℂ ⧸ (⊥ : Ideal (MRing ι ℂ))) = 0 := by
  rw [ringKrullDim_eq_of_ringEquiv
    ((RingEquiv.quotientBot (MRing ι ℂ)).trans (isEmptyRingEquiv ℂ (Σ k, ι k)))]
  exact ringKrullDim_eq_zero_of_field ℂ

def emptyAlgRes [IsEmpty K] : ReciprocityTheory.AnForm.R.AlgRes ι (⊥ : Ideal (MRing ι ℂ)) ⊤ 0 where
  M := Unit
  n := 1
  amb _ := 0
  ideal _ := ⊥
  src _ := Set.univ
  isOpen_alt_bis _ := isOpen_univ
  cover _ := ⟨0, Set.mem_univ _⟩
  coord _ _ := 0
  isEmbedding _ := Topology.IsEmbedding.of_subsingleton _
  image _ := by
    ext y
    constructor
    · rintro - h hh
      rw [Ideal.mem_bot] at hh
      simp [hh]
    · intro _
      exact ⟨(), Set.mem_univ _, Subsingleton.elim _ _⟩
  trans _ _ _ _ := ⟨1, fun l => l.elim0, by simp, fun _ _ _ l => l.elim0⟩
  regular _ _ _ := ReciprocityTheory.AnForm.R.locRing_bot_regular _
  dim _ _ _ := by
    rw [ReciprocityTheory.AnForm.R.locRing_bot_dim]
    rfl
  lift _ q := isEmptyElim q.1
  lift_one _ := ⟨fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  lift_mem _ _ _ := ⟨fun k => isEmptyElim k, fun f hf => by rw [Ideal.mem_bot.mp hf, map_zero]⟩
  compat _ _ _ _ := ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, funext fun q => isEmptyElim q.1⟩
  surj _ _ _ := ⟨0, (), Set.mem_univ _, fun k => isEmptyElim k, fun k => isEmptyElim k,
    funext fun q => isEmptyElim q.1⟩
  inj _ _ x _ x' _ _ _ := Subsingleton.elim x x'
  inv _ _ _ _ _ hp := ⟨Set.univ, isOpen_univ, Set.mem_univ _, subset_rfl, 1, fun l => l.elim0,
    fun _ _ => ⟨hp, by simp, fun l => l.elim0⟩⟩
  bd _ := ⊤
  le_bd _ := le_top
  zero_bd _ _ _ := ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp),
    fun h => absurd (h.2 1 Submodule.mem_top) (by simp)⟩
  rc := 0
  comp k := k.elim0
  sncAt _ _ _ := ptSnc _
  comp_eq _ _ _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, subset_rfl, fun k => k.elim0⟩
  mult f _ _ hfP _ := by
    have hc : coeff 0 f ≠ 0 := fun h0 => hfP (by rw [Ideal.mem_bot, eq_C_of_isEmpty f, h0, map_zero])
    refine ⟨fun k => k.elim0, fun i x hx => ⟨algebraMap _ _ (bind₁ (fun q : Σ k, ι k =>
      (isEmptyElim q.1 : MvPolynomial (Fin 0) ℂ)) f), ?_, ?_⟩⟩
    · rw [eq_C_of_isEmpty f, bind₁_C_right]
      exact ((isUnit_iff_ne_zero.mpr hc).map C).map _
    · simp only [ptSnc, Finset.prod_empty, mul_one]

end

theorem ResExists.proof (h : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC ∧ ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE) :
    ResExists.Statement := by
  intro K _ _ ι _ P e hP
  obtain ⟨⟨hprime, hhom, -⟩, hdimP⟩ := hP
  rcases isEmpty_or_nonempty K with hK | hK
  ·
    have hP0 : P = ⊥ := eq_bot_of_isEmpty hprime
    subst hP0
    have he : e = 0 := by
      rw [ringKrullDim_bot_of_isEmpty, Fintype.card_eq_zero, add_zero] at hdimP
      exact_mod_cast hdimP.symm
    subst he
    exact ⟨⟨⊤, fun _ _ _ => Submodule.mem_top, fun h' => hprime.ne_top (top_le_iff.mp h'),
      emptyAlgRes⟩⟩
  · haveI := hprime
    obtain ⟨t, G, hG, hspan⟩ := exists_forms_span hhom
    have hdimQ : ∀ Q ∈ P.minimalPrimes,
        ringKrullDim (MRing ι ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      intro Q hQ
      rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hQ
      rw [hQ]
      exact hdimP

    obtain ⟨a, b, hab⟩ := exists_jacobian_minor_not_mem_charZero P G hspan (e + Fintype.card K) hdimP
    obtain ⟨δ, hδ⟩ := isMultiHomog_det_pderiv_over (R := ℂ) G hG a b
    set d := Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) with hd
    have hPR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P :=
      ⟨Set.range G, by rintro _ ⟨i, rfl⟩; exact hG i, hspan.symm⟩
    have hDR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (Ideal.span {d}) :=
      ⟨{d}, by rintro _ rfl; exact ⟨δ, hδ⟩, rfl⟩
    have hDN : NumbersDVR.IsMultiHomogIdeal (Ideal.span {d}) :=
      (Bridge.isMultiHomogIdeal_iff _).mpr ⟨{d}, by rintro _ rfl; exact ⟨δ, hδ⟩, rfl⟩
    have hnot : ¬ Ideal.span {d} ≤ P := fun hle => hab (hle (Ideal.subset_span rfl))
    have hcomp : ∀ Q ∈ P.minimalPrimes, ReciprocityTheory.AnForm.R.IsRelevant Q → ¬ Ideal.span {d} ≤ Q := by
      intro Q hQ _
      rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hQ
      rw [hQ]
      exact hnot

    have hsing : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ),
        (∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal P p, eval z h = 0) →
        ¬ IsRegularLocalRing (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal P p) z) →
        ∀ f ∈ Ideal.span {d}, eval z f = 0 := by
      intro p z hz hnreg f hf
      have hdz : eval z d = 0 := by
        by_contra hne
        exact hnreg (ReciprocityTheory.AnForm.R.isRegularLocalRing_locAt_chart P e hdimQ G hG hspan p z hz a b hne)
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [map_mul, hdz, mul_zero]
    have hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ),
        (∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal P p, eval z h = 0) →
        ringKrullDim (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal P p) z) = e :=
      fun p z hz => ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart P hPR e hdimQ p z hz
    obtain ⟨R⟩ := ReciprocityTheory.AnForm.R.algRes_of_logResStC h.2 P (Ideal.span {d}) e hPR
      hprime.isRadical hDR hcomp hsing hdim
      (ReciprocityTheory.AnForm.R.projLogResC_of_C h.1 h.2 K ι P (Ideal.span {d}) hPR hDR hprime.isRadical
        hsing hcomp)
    exact ⟨⟨Ideal.span {d}, hDN, hnot, R⟩⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
