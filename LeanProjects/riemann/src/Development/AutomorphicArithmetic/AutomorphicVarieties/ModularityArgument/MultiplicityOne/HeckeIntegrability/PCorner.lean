import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUnique

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi.Cn

variable {R : Type} [Ring R] [Algebra ℂ R]

private def Good (s : Set R) (e : R) : Prop :=
  e ∈ Algebra.adjoin ℂ s ∧ e * e = e ∧ ∀ x ∈ Algebra.adjoin ℂ s, ∃ c : ℂ, e * x * e = c • e

private lemma adj_comm {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {x y : R}
    (hx : x ∈ Algebra.adjoin ℂ s) (hy : y ∈ Algebra.adjoin ℂ t) : Commute x y :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun _ hb =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => (h a ha _ hb).symm).symm

private lemma mem_span {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {z : R}
    (hz : z ∈ Algebra.adjoin ℂ (s ∪ t)) :
    z ∈ Submodule.span ℂ {w : R | ∃ x ∈ Algebra.adjoin ℂ s, ∃ y ∈ Algebra.adjoin ℂ t, w = x * y} := by
  induction hz using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · exact Submodule.subset_span ⟨g, Algebra.subset_adjoin hg, 1, one_mem _, (mul_one _).symm⟩
    · exact Submodule.subset_span ⟨1, one_mem _, g, Algebra.subset_adjoin hg, (one_mul _).symm⟩
  | algebraMap r =>
    exact Submodule.subset_span ⟨_, Subalgebra.algebraMap_mem _ r, 1, one_mem _, (mul_one _).symm⟩
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv =>
    have hm := Submodule.mul_mem_mul hu hv
    rw [Submodule.span_mul_span] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, _, ⟨x', hx', y', hy', rfl⟩, rfl⟩
    refine ⟨x * x', mul_mem hx hx', y * y', mul_mem hy hy', ?_⟩
    exact ((adj_comm h hx' hy).mul_mul_mul_comm x y').symm

private lemma good_two {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {e e' : R}
    (he : Good s e) (he' : Good t e') : Good (s ∪ t) (e * e') := by
  obtain ⟨m, i, c⟩ := he
  obtain ⟨m', i', c'⟩ := he'
  refine ⟨mul_mem (Algebra.adjoin_mono Set.subset_union_left m)
    (Algebra.adjoin_mono Set.subset_union_right m'), ?_, fun z hz => ?_⟩
  · rw [(adj_comm h m m').symm.mul_mul_mul_comm, i, i']
  · have hz' := mem_span h hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      obtain ⟨p, hp⟩ := c x hx
      obtain ⟨q, hq⟩ := c' y hy
      refine ⟨p * q, ?_⟩
      rw [(adj_comm h hx m').symm.mul_mul_mul_comm,
        (adj_comm h m (mul_mem m' hy)).symm.mul_mul_mul_comm, hp, hq, smul_mul_smul_comm]
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨p, hp⟩ := hu
      obtain ⟨q, hq⟩ := hv
      exact ⟨p + q, by rw [mul_add, add_mul, hp, hq, add_smul]⟩
    | smul r u _ hu =>
      obtain ⟨p, hp⟩ := hu
      exact ⟨r * p, by rw [mul_smul_comm, smul_mul_assoc, hp, smul_smul]⟩

private lemma good_list {I : Type} (s : I → Set R) (e : I → R)
    (h : ∀ i k, i ≠ k → ∀ x ∈ s i, ∀ y ∈ s k, Commute x y) (he : ∀ i, Good (s i) (e i))
    (l : List I) (hl : l.Nodup) : Good {x | ∃ i ∈ l, x ∈ s i} (l.map e).prod := by
  induction l with
  | nil =>
    refine ⟨by simpa using one_mem _, by simp, fun x hx => ?_⟩
    have h0 : {x | ∃ i ∈ ([] : List I), x ∈ s i} = ∅ := by simp
    rw [h0, Algebra.adjoin_empty, Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    exact ⟨r, by simp [Algebra.algebraMap_eq_smul_one]⟩
  | cons i l ih =>
    have hn := List.nodup_cons.1 hl
    have h0 : {x | ∃ k ∈ i :: l, x ∈ s k} = s i ∪ {x | ∃ k ∈ l, x ∈ s k} := by
      ext x; simp
    rw [h0, List.map_cons, List.prod_cons]
    refine good_two ?_ (he i) (ih hn.2)
    rintro x hx y ⟨k, hk, hy⟩
    exact h i k (fun e => hn.1 (e ▸ hk)) x hx y hy

end UpperTheory.V.Z.Mult.Pi.Cn

open UpperTheory.V.Z.Mult.Pi.Cn in
theorem UpperTheory.V.Z.Mult.Pi.corner_pf :
    Corner := by
  intro I _ J Y _ _ _ _ a b e e' haa hab hbb hY he he' f hf
  have hg := good_list (fun i => Set.range (a i) ∪ Set.range (b i)) (fun i => e i * e' i)
    (by
      rintro i k hik x (⟨p, rfl⟩ | ⟨p, rfl⟩) y (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · exact haa i k hik p q
      · exact hab i k p q
      · exact (hab k i q p).symm
      · exact hbb i k hik p q)
    (fun i => good_two (by
      rintro x ⟨p, rfl⟩ y ⟨q, rfl⟩
      exact hab i i p q) (he i) (he' i))
    (Finset.univ : Finset I).toList (Finset.nodup_toList _)
  rw [← hf] at hg
  obtain ⟨-, h1, h2⟩ := hg
  refine ⟨h1, fun x => ?_⟩
  have hsurj := DiscreteGroups.T1.Desc.Swap3.burnside (Algebra.adjoin ℂ
    {x | ∃ i ∈ (Finset.univ : Finset I).toList, x ∈ Set.range (a i) ∪ Set.range (b i)}).val (by
    intro W hW
    refine hY W fun i p x hx => ⟨?_, ?_⟩
    · exact hW ⟨a i p, Algebra.subset_adjoin ⟨i, by simp, Or.inl ⟨p, rfl⟩⟩⟩ x hx
    · exact hW ⟨b i p, Algebra.subset_adjoin ⟨i, by simp, Or.inr ⟨p, rfl⟩⟩⟩ x hx)
  obtain ⟨⟨z, hz⟩, rfl⟩ := hsurj x
  exact h2 z hz
