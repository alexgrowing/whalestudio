import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem conjP_ne {R : Ranks} (H : Formalism.BasicNotions.Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : conjPrime₂ P ≠ P := by
  intro e
  obtain ⟨x, hx, hy⟩ := h
  have hc : IsConjPl H P P := (isConjPl_iff H P P).2 e.symm
  have e1 : ((cO H.E x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := bridge_star_holds R H x
  exact hy _ e1 ((hc x _ e1).1 hx)

variable {B : Base} {X : PreX B.toPre} {I : ColIn B X}

theorem under_sel (h : I.Ok) (v : HeightOneSpectrum (𝓞 B.host.F)) : (I.sel v).under (𝓞 B.host.F) = v :=
  HeightOneSpectrum.ext (h.sel_ok v)

theorem good_of_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ I.SQ) :
    I.sel (P.under (𝓞 B.host.F)) = P ∧ GoodPl B.host.E I.S (P.under (𝓞 B.host.F)) := by
  obtain ⟨a, ha⟩ := I.mem_SQ.1 hP
  obtain ⟨v, -, rfl, hg⟩ := I.exists_of_mem_Q ha
  rw [under_sel h]
  exact ⟨rfl, hg⟩

theorem plc_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ (B.primes X).vGs) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 B.host.F)) ∈ I.S := by
  classical
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ P.asIdeal := by
    unfold Primes.vGs Primes.vG at hP
    simpa only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two] using hP
  obtain ⟨i, hi⟩ := hm
  have h1 : ((B.primes X).g i : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi
  rw [(ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.g_prime i)).2 h1]
  exact h.g_mem i

theorem levOk_twists : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → LevOk B.host (B.primes X).vGs I.SQ ∧ Disjoint (B.primes X).vGs I.SQ ∧ ∀ a, KDq B.host (I.Q a) ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker ∧ (I.xi a).IsUnitary := by
  classical
  intro B X I h
  have hb := levOk_base B X
  have hu : ∀ P : HeightOneSpectrum (𝓞 B.host.E), (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := fun P =>
    (under_eq_iff B.host P _).2 (Or.inr rfl)
  refine ⟨⟨hb.cover, fun P hP hP' => ?_⟩, Finset.disjoint_left.2 fun P h1 h2 => (good_of_mem h h2).2.2.2 (plc_mem h h1),
    fun a => ?_⟩
  · simp only [Finset.mem_union] at hP hP'
    rcases hP with hP | hP <;> rcases hP' with hP' | hP'
    · exact hb.split P (by simpa using hP) (by simpa using hP')
    · refine (good_of_mem h hP').2.2.2 ?_
      rw [hu]
      exact plc_mem h hP
    · refine (good_of_mem h hP).2.2.2 ?_
      rw [← hu]
      exact plc_mem h hP'
    · have e := (good_of_mem h hP').1
      rw [hu, (good_of_mem h hP).1] at e
      exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 (good_of_mem h hP).2).1 e.symm
  · obtain ⟨⟨⟨n, hn, ho⟩, hT, hta, -⟩, hq, -⟩ :=
      ReadTwist.isTwist_of_reads B.R B.host B.LL B.embLL I.S (I.tup a) (I.xi a) (h.xi_reads a)
    refine ⟨KDq_le_ker_of_tame _ hT hta fun w hw => by_contra fun hr => hw (Or.inr ?_), fun x => ?_⟩
    · have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
        ((UnrAe.finite_ramified (I.xi a)).image (·.under (𝓞 B.host.F))).subset fun v hv => by
          obtain ⟨P, e, hP⟩ := (hq v).1 hv
          exact ⟨P, hP, e⟩
      have hmem : I.sel (w.under (𝓞 B.host.F)) ∈ I.Q a := by
        unfold ColIn.Q QE
        rw [dif_pos hfin]
        convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 ((hq _).2 ⟨w, rfl, hr⟩))
      rcases (under_eq_iff B.host _ w).1 (under_sel h _).symm with e | e
      · exact Or.inl (e ▸ hmem)
      · exact Or.inr ⟨_, hmem, (isConjPl_iff B.host _ _).2 e⟩
    · have h1 : (I.xi a).1 x ^ n = 1 := congrArg (fun χ : HChar B.host.E => χ.1 x) ho
      have h2 : ‖(((I.xi a).1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

end GlobalTheory.Mem.LevTwist
