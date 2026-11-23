import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

open MeasureTheory NumberField Matrix Finset in
private theorem card_infinitePlace_E_eq_F (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.E) = Fintype.card (InfinitePlace I.F) := by
  have hsurj : Function.Surjective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) :=
    fun v => InfinitePlace.comap_surjective v
  have hinj : Function.Injective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
    intro w₁ w₂ h
    have key : ∀ w : InfinitePlace I.E,
        w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases _root_.GlobalTheory.Count.Test.embedding_cases I w with hw | hw
      · rw [← hw, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← hw, InfinitePlace.mk_embedding]
    rw [key w₁, key w₂]
    simp only at h
    rw [h]
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩

open MeasureTheory NumberField Matrix Finset in
private theorem card_infinitePlace_F_eq_finrank (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.F) = Module.finrank ℚ I.F := by
  haveI := I.cm.totReal
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero] at *
  omega

open MeasureTheory NumberField Matrix Finset in
private theorem one_le_abs_discr_E (I : _root_.Formalism.MainNotions.S.AutInst) : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
  have h := discr_ne_zero I.E
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.FlagMeas.instance_numbers : ∀ I : _root_.Formalism.MainNotions.S.AutInst, _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * _root_.Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, _root_.GlobalTheory.FlagMeas.HasSig I p q → p + q = I.n := by
  intro I
  have hdeg : _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [card_infinitePlace_E_eq_F, card_infinitePlace_F_eq_finrank]
  have hcardF : Fintype.card (InfinitePlace I.F) = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact card_infinitePlace_F_eq_finrank I
  have hfpos : 1 ≤ I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact Module.finrank_pos
  refine ⟨hdeg, ?_, ?_, hfpos, hcardF, ?_⟩
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd _root_.Formalism.HermitianLatticesTheory.vInv
    rw [hdeg]
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    ring
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd
    apply Real.one_le_rpow (one_le_abs_discr_E I)
    positivity
  · intro p q h
    unfold _root_.GlobalTheory.FlagMeas.HasSig at h
    have hne : Nonempty (InfinitePlace I.F) := by
      apply Fintype.card_pos_iff.mp
      omega
    obtain ⟨v⟩ := hne
    obtain ⟨hp, hq⟩ := h v
    rw [← hp, ← hq]
    unfold _root_.Formalism.MainNotions.S.AutInst.pAt _root_.Formalism.MainNotions.S.AutInst.qAt
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin I.n))) (fun a => I.ε v a = true)
    simpa using this

end GlobalTheory.FlagMeas
