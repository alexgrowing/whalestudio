import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.JumpWin

theorem finset_of_rat (F : Finset ℚ) (n N : ℕ) (P : ℤ → Prop) (hF : F.card ≤ n)
    (hP : ∀ a, P a → (a : ℚ) ∈ F ∧ -(N : ℤ) ≤ a ∧ a ≤ N) :
    ∃ U : Finset ℤ, U.card ≤ n ∧ (∀ u ∈ U, -(N : ℤ) ≤ u ∧ u ≤ N) ∧ ∀ a, P a → a ∈ U := by
  classical
  refine ⟨(F.image fun q => ⌊q⌋).filter (fun u => -(N : ℤ) ≤ u ∧ u ≤ N), ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hF)
  · intro u hu
    exact (Finset.mem_filter.1 hu).2
  · intro a ha
    obtain ⟨h1, h2⟩ := hP a ha
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a : ℚ), h1, Int.floor_intCast a⟩, h2⟩

variable {D : D7}

open AdmissibleParameterJ

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up <;> simp only [JW, cloudT, lowT, JJ, Jp, Jm, reflS, Bool.false_eq_true, if_true, if_false,
    Set.mem_union, Set.mem_setOf_eq] at hq ⊢ <;> tauto

theorem exists_finset_JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) :
    ∃ F : Finset ℚ, F.card ≤ D.R.r ∧ ∀ q ∈ JW D up j ρ, q ∈ F := by
  classical
  let cl : Finset ℚ := Finset.univ.image (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D)
  let lw : Finset ℚ := Finset.univ.image (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)
  have hcard : (cl ∪ lw).card ≤ D.R.r := by
    have h1 : cl.card ≤ D.R.k - 1 := Finset.card_image_le.trans (by simp)
    have h2 : lw.card ≤ D.R.m := Finset.card_image_le.trans (by simp)
    have hk := D.R.m_add_three_le_k
    have : (cl ∪ lw).card ≤ cl.card + lw.card := Finset.card_union_le _ _
    simp only [Ranks.r]
    omega
  have hmem : ∀ q, q ∈ cloudJ D j ρ ∪ lowJ D j ρ → q ∈ cl ∪ lw := by
    intro q hq
    rcases hq with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  cases up
  · refine ⟨(cl ∪ lw).image (AdmissibleParameterJ.refl D), Finset.card_image_le.trans hcard, ?_⟩
    intro q hq
    have hq' : AdmissibleParameterJ.refl D q ∈ cloudJ D j ρ ∪ lowJ D j ρ := by
      simpa only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
        Set.mem_setOf_eq] using hq
    refine Finset.mem_image.2 ⟨AdmissibleParameterJ.refl D q, hmem _ hq', ?_⟩
    simp only [AdmissibleParameterJ.refl]; ring
  · refine ⟨cl ∪ lw, hcard, ?_⟩
    intro q hq
    exact hmem q (by simpa only [JW, cloudT, lowT, if_true] using hq)

theorem zero_not_mem_JW (L : SizeData₂ D) (hc : jcCondition L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hj2 ρ
  cases up
  · intro h
    simp only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
      Set.mem_setOf_eq] at h
    have ht : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
    rcases h with h | h
    · have := hcl _ h
      simp only [AdmissibleParameterJ.refl] at this
      linarith
    · rcases hlow _ h with ⟨-, h'⟩ | ⟨h', -⟩
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
  · simpa only [JW, cloudT, lowT, if_true] using h0

theorem natAbs_le_of_mem_JJ (L : SizeData₂ D) (he : JumpAbsoluteBound L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    a.natAbs ≤ ⌊2 * L.sc.b⌋₊ := by
  have h1 := he.1 j hj1 hj2 ρ up _ ha
  have h2 : |((a : ℚ) : ℝ)| ≤ 2 * L.sc.b := by
    have := he.2.1; have := he.2.2.2; linarith
  apply Nat.le_floor
  have : ((a.natAbs : ℕ) : ℝ) = |((a : ℚ) : ℝ)| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]; exact h2

end GlobalTheory.JumpWin

open GlobalTheory.JumpWin AdmissibleParameterJ in

theorem GlobalTheory.jumps_WpO_T2O_window : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → AdmissibleParameterJ.DualCloudSizes L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1), ∀ M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i), (M = WpO D.nd i ρ π ∨ M = T2O D.nd i ρ π) → (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -((⌊2 * L.sc.b⌋₊ + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (⌊2 * L.sc.b⌋₊ + 1 : ℕ)) ∧ ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧ ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0 := by
  intro D L ep hA _hb hc he hf i r ρ π hr hπ hdec w hw C τ M hM
  classical
  obtain ⟨g, ρ', -, -, hT⟩ := hA i r hr w hw C τ
  have hj := D.nd.j_range i
  have hW := hT ρ π hπ hdec
  generalize decide (TypeU D ep g) = up at hW
  obtain ⟨F, hFc, hFm⟩ := exists_finset_JW up (D.nd.j i) ρ'
  rcases hM with rfl | rfl
  · refine ⟨finset_of_rat F D.R.r (⌊2 * L.sc.b⌋₊ + 1) _ hFc ?_, ?_⟩
    · intro a ha
      have hq := ((hW a).1).1 ha
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' a (JW_sub_JJ up _ ρ' hq)
      refine ⟨hFm _ hq, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).1).1 h0
      exact zero_not_mem_JW L hc up _ hj.1 hj.2 ρ' (by simpa using this)
  · refine ⟨finset_of_rat (F.image fun q => -q - 1) D.R.r (⌊2 * L.sc.b⌋₊ + 1) _
      (Finset.card_image_le.trans hFc) ?_, ?_⟩
    · intro a ha
      have hq : -(a : ℚ) - 1 ∈ JW D up (D.nd.j i) ρ' := ((hW a).2.2.1).1 ha
      have hq' : (((-a - 1 : ℤ)) : ℚ) ∈ JW D up (D.nd.j i) ρ' := by push_cast; exact hq
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' _ (JW_sub_JJ up _ ρ' hq')
      refine ⟨Finset.mem_image.2 ⟨_, hFm _ hq, by ring⟩, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).2.2.1).1 h0
      exact (hf _ hj.1 hj.2 ρ').2.2.1 up (by simpa using this)

end
