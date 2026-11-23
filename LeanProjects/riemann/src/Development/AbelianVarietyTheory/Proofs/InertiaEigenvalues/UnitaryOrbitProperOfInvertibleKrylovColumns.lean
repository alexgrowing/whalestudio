import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OrbProper

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem continuous_bm : Continuous (fun X : Hn r F E => Bm X.toGl) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((((continuous_subtype_val.comp continuous_fst).pow (j : ℕ))).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem continuous_actU :
    Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU q.1 q.2) := by
  haveI := ImgSec.continuousStar (E := E) F
  have hg : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact ((hg.mul hA).mul hg.star).subtype_mk _
  · exact hg.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))
  · exact continuous_snd.comp (continuous_snd.comp continuous_snd)

theorem continuousOn_inv {X : Type} [TopologicalSpace X] {Ω : Set X} {h : X → Matrix (Fin r) (Fin r) E}
    (hh : ContinuousOn h Ω) (hu : ∀ a ∈ Ω, IsUnit (h a).det) : ContinuousOn (fun a => (h a)⁻¹) Ω := by
  have : (fun a => (h a)⁻¹) = fun a => ((h a).det)⁻¹ • (h a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  refine ContinuousOn.smul (f := fun a => ((h a).det)⁻¹) (g := fun a => (h a).adjugate) ?_ ?_
  · exact (continuous_id.matrix_det.comp_continuousOn hh).inv₀ fun a ha => (hu a ha).ne_zero
  · exact continuous_id.matrix_adjugate.comp_continuousOn hh

theorem isCompact_orbit (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E)
    (h : Inv r F → Matrix (Fin r) (Fin r) E) (hΩ : IsCompact Ω) (hs : ContinuousOn s Ω) (hhc : ContinuousOn h Ω)
    (hb : ∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) (C : Set (Hn r F E)) (hC : IsCompact C) :
    IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
  haveI := ImgSec.continuousStar (E := E) F
  set Φ : Hn r F E × Inv r F → Matrix (Fin r) (Fin r) E := fun q => Bm q.1.toGl * (h q.2)⁻¹ with hΦ
  have hΦc : ContinuousOn Φ (C ×ˢ Ω) := by
    refine (continuous_bm.comp continuous_fst).continuousOn.mul ?_
    exact (continuousOn_inv hhc fun a ha => (hb a ha).1).comp continuous_snd.continuousOn
      (fun q hq => hq.2)
  have hM : IsCompact (Φ '' (C ×ˢ Ω)) := (hC.prod hΩ).image_of_continuousOn hΦc
  have hU : IsClosed ((Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E))) := isClosed_unitary
  have hK : IsCompact (((↑) : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    (hU.isClosedEmbedding_subtypeVal).isCompact_preimage hM
  have hcl : IsClosed {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
    have hf : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2))
        (Set.univ ×ˢ Ω) := by
      have h1 : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => (p.1, s p.2)) (Set.univ ×ˢ Ω) :=
        continuous_fst.continuousOn.prodMk (hs.comp continuous_snd.continuousOn (fun q hq => hq.2))
      have h2 := (continuous_actU (F := F) (E := E) (r := r)).comp_continuousOn h1
      exact h2
    have hC2 : IsClosed C := hC.isClosed
    have hO2 : IsClosed (Set.univ ×ˢ Ω : Set (Matrix.unitaryGroup (Fin r) E × Inv r F)) := isClosed_univ.prod hΩ.isClosed
    have h3 := hf.preimage_isClosed_of_isClosed hO2 hC2
    have heq : {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} =
        (Set.univ ×ˢ Ω) ∩ (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2)) ⁻¹' C := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage]
    rw [heq]; exact h3
  refine (hK.prod hΩ).of_isClosed_subset hcl ?_
  rintro ⟨g, a⟩ ⟨ha, hC'⟩
  refine ⟨⟨(actU g (s a), a), ⟨hC', ha⟩, ?_⟩, ha⟩
  simp only [hΦ]
  rw [ImgSec.bm_actU, (hb a ha).2, Matrix.mul_nonsing_inv_cancel_right _ _ (hb a ha).1]

end GlobalTheory.JR.OrbProper

theorem GlobalTheory.JR.orbit_proper_of_columns : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} :=
  fun _ _ _ _ _ _ _ r Ω s h hΩ hs hh hb C hC => GlobalTheory.JR.OrbProper.isCompact_orbit r Ω s h hΩ hs hh hb C hC
