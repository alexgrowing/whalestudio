import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CellSmoothness

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma contDiffOn_gq (D : RealPlaceData k r Wp Wq) : ContDiffOn ℝ ∞ (fun q => gq D q) (QDom k r D.z D.z') := by
  refine Formalism.FourierDecayAlt.P.Ux10.cdm_iff.2 fun i j => ?_
  simp only [gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) (⟨j.val, h1⟩ : Fin r)).comp
      (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff.contDiffOn
  · exact contDiffOn_const
  · exact (D.sec.1 _ _).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  · exact contDiffOn_const
  · refine ContDiffOn.inv ?_ ?_
    · exact (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        (⟨2 * r + k - j.val, by omega⟩ : Fin r)).comp (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff).contDiffOn
    · intro q hq
      simpa using hq.1 _
  · exact contDiffOn_const

lemma glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Formalism.FourierDecayAlt.Q.Glev k r 0 := by simpa [Formalism.FourierDecayAlt.Q.Glev] using hg

theorem jqSmooth_of_words (hW : JWords) : JqSmooth := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  have hck := (hW k r Wp Wq D A m F hThr hCC).1
  have hg := contDiffOn_gq D
  have hQo : IsOpen (QDom k r D.z D.z') := Formalism.FourierDecayAlt.P.B7.isOpen_good_set D
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hqOm : gq D q ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := hck _ ⟨glev0 hqOm.1, hqOm.2⟩
  have hVo : IsOpen (QDom k r D.z D.z' ∩ (fun x => gq D x) ⁻¹' U) :=
    hg.continuousOn.isOpen_inter_preimage hQo hU
  refine ⟨QDom k r D.z D.z' ∩ (fun x => gq D x) ⁻¹' U, hVo, ⟨hq, hgU⟩, ?_⟩
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => F' (gq D x))
      (QDom k r D.z D.z' ∩ (QDom k r D.z D.z' ∩ (fun x => gq D x) ⁻¹' U)) :=
    hF'.comp ((hg.of_le (by exact_mod_cast le_top)).mono Set.inter_subset_left) (fun x hx => hx.2.2)
  refine h1.congr fun x hx => ?_
  have hxOm : gq D x ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hx.1
  exact hUF _ hx.2.2 (glev0 hxOm.1)

theorem jqSmooth_of_jDom (hD : JDom) : JqSmooth := jqSmooth_of_words (bessel_words_of_domain hD)

end Formalism.FourierDecayAlt.P.CellSmoothness
