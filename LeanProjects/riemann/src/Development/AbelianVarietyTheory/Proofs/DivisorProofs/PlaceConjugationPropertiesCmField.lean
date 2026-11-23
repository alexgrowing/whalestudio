import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.ConjAtPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_of_lt_one {w : HeightOneSpectrum (𝓞 E)} (x : w.adicCompletion E) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (nhds 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_of_lt_one z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  rw [map_pow] at hN
  exact absurd hN (not_lt.2 (one_le_pow₀ hc))

theorem conjSrc_eq_of_cont (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s)
    (he : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hmem : ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ Valued.v (algebraMap E (w.adicCompletion E) (a : E)) < 1 := by
    intro a
    rw [hval, HeightOneSpectrum.valuation_lt_one_iff_mem]
  have hdir : ∀ x y : 𝓞 E, (y : E) = IsCMField.complexConj E (x : E) → x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    rw [hmem] at hx ⊢
    rw [hxy, ← he]
    exact lt_one_of_continuous s hs hx
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.SplitPts.conjE E) w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    refine ⟨hdir x y hxy, hdir y x ?_⟩
    rw [show (GlobalTheory.SplitPts.conjE E) (x : E) = IsCMField.complexConj E (x : E) from rfl] at hxy
    rw [hxy, IsCMField.complexConj_apply_apply]
  exact (eq_conjSrc hc).symm

theorem conjSrc_eq_iff (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w ↔ ¬ IsSplitAt w := by
  refine ⟨fun h hs => (GlobalTheory.SplitPts.over_split hs).1 h, fun h => ?_⟩
  by_contra hne
  apply h
  exact ⟨conjSrc (GlobalTheory.SplitPts.conjE E) w, hne,
    (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))⟩

theorem ext_of_cont {v w : HeightOneSpectrum (𝓞 E)} (s t : v.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) (ht : Continuous t)
    (hse : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hte : ∀ x : E, t (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) : s = t :=
  RingHom.ext fun y => congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hs ht
    (funext fun k => (hse k).trans (hte k).symm)) y

theorem cont_of_val {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s :=
  GlobalTheory.Mem.Chr.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective E w) s hv

theorem cj_spec (w : Pl E)
    (h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    Continuous (cj w) ∧ ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  unfold cj
  rw [dif_pos h]
  exact h.choose_spec

theorem cj_of_not (w : Pl E)
    (h : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    cj w = RingHom.id _ := by
  unfold cj
  rw [dif_neg h]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  intro E _ _ _ hU w
  by_cases hsp : IsSplitAt w
  · have hno : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
      rintro ⟨s, hs, he⟩
      exact (GlobalTheory.SplitPts.over_split hsp).1 (conjSrc_eq_of_cont w s hs he)
    have hid := cj_of_not w hno
    refine ⟨by rw [hid]; exact continuous_id, fun x => by rw [hid]; rfl, fun x => by rw [hid]; rfl,
      fun h => absurd hsp h, fun s hv he _ => hno ⟨s, cont_of_val s hv, he⟩⟩
  · obtain ⟨s0, ϖ, q, he0, hU0⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hU w) hsp
    have hc0 : Continuous s0 := cont_of_val s0 hU0.2.1
    obtain ⟨hcj, hecj⟩ := cj_spec w ⟨s0, hc0, he0⟩
    have heq : cj w = s0 := ext_of_cont _ _ hcj hc0 hecj he0
    have hsrc : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := (conjSrc_eq_iff w).2 hsp
    refine ⟨hcj, fun x => by rw [heq]; exact hU0.1 x, fun x => by rw [heq]; exact hU0.2.1 x,
      fun _ => ⟨hecj, ⟨ϖ, q, by rw [heq]; exact hU0, ?_⟩, fun x => ?_,
        fun s hv he => ext_of_cont _ _ (cont_of_val s hv) hcj he hecj⟩, fun _ _ _ => hsp⟩
    · exact (Formalism.UG.P.tjcosets_card_residue w).symm.trans hU0.2.2.2.2.2.2
    · rw [pLoc_conjFin]
      have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
          Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
          f (pLoc E v x) = cj w (pLoc E w x) := by
        rintro v rfl f hf hfe
        rw [ext_of_cont f (cj v) hf hcj hfe hecj]
      exact key _ hsrc _ (conjLoc_spec _ w).1 (conjLoc_spec _ w).2.1

end GlobalTheory.ConjAtPlace
