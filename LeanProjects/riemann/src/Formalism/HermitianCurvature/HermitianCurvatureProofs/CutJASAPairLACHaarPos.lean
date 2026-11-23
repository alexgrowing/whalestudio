import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair

open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

variable {k r : ℕ}

theorem haar_pos_nhds_one {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ)
    (hinv : ∀ u ∈ U, u⁻¹ ∈ U) (hunit : ∀ u ∈ U, IsUnit u.det) {V : Set (Mt k r)} (hV : IsOpen V)
    (h1 : ((1 : B.Mat k r) : Mt k r) ∈ V) : 0 < μ V := by
  rw [pos_iff_ne_zero]
  intro h0
  let W : B.Mat k r → Set (Mt k r) := fun u => lmulM u⁻¹ ⁻¹' V
  have hWo : ∀ u ∈ U, IsOpen (W u) := fun u _ => hV.preimage (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont _)
  have hW0 : ∀ u ∈ U, μ (W u) = 0 := by
    intro u hu
    have e := h.left u⁻¹ (hinv u hu)
    have := Measure.map_apply (μ := μ) (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) u⁻¹).measurable hV.measurableSet
    rw [e] at this
    show μ (lmulM u⁻¹ ⁻¹' V) = 0
    rw [← this]; exact h0
  have hcov : (U : Set (Mt k r)) ⊆ ⋃ u ∈ U, W u := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    have e : (lmulM x⁻¹ x : Mt k r) = ((1 : B.Mat k r) : Mt k r) := by
      show x⁻¹ * x = 1
      exact Matrix.nonsing_inv_mul x (hunit x hx)
    show lmulM x⁻¹ x ∈ V
    rw [e]; exact h1
  obtain ⟨T, hTU, hTc, hTeq⟩ := TopologicalSpace.isOpen_biUnion_countable U W hWo
  have hU0 : μ (U : Set (Mt k r)) = 0 := by
    refine measure_mono_null (hcov.trans hTeq.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun u hu => hW0 u (hTU hu)
  have huniv : μ Set.univ = 0 := by
    refine measure_mono_null ?_ (measure_union_null hU0 h.conc)
    intro x _
    by_cases hx : x ∈ (U : Set (Mt k r))
    · exact Or.inl hx
    · exact Or.inr hx
  exact h.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

theorem averaging_haar_positivity : ACHaarPos := by
  intro k r Wp Wq _ _ _ _ D O hO h1
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨A, B', hA, hB, hoA, hoB, hAB⟩ := isOpen_prod_iff.1 hO oneP.1 oneP.2 h1
  obtain ⟨V1, V2, hV1, hV2, ho1, ho2, h12⟩ := isOpen_prod_iff.1 hA oneP.1.1 oneP.1.2 hoA
  obtain ⟨V3, V4, hV3, hV4, ho3, ho4, h34⟩ := isOpen_prod_iff.1 hB oneP.2.1 oneP.2.2 hoB
  have hsub : (V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4) ⊆ O :=
    (Set.prod_mono h12 h34).trans hAB
  have uwI : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, u⁻¹ ∈ UWset k r w :=
    fun w u hu => Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hu
  have uwU : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, IsUnit u.det :=
    fun w u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have nI : ∀ u ∈ Nset k r, u⁻¹ ∈ Nset k r := fun u hu => WeylGroupFacts.mem_n_inv hu
  have nU : ∀ u ∈ Nset k r, IsUnit u.det := fun u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have p1 := haar_pos_nhds_one D.haarW (uwI _) (uwU _) hV1 ho1
  have p2 := haar_pos_nhds_one D.haarN nI nU hV2 ho2
  have p3 := haar_pos_nhds_one D.haarW' (uwI _) (uwU _) hV3 ho3
  have p4 := haar_pos_nhds_one D.haarN nI nU hV4 ho4
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  show 0 < ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) ((V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4))
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  rw [pos_iff_ne_zero] at p1 p2 p3 p4 ⊢
  exact mul_ne_zero (mul_ne_zero p1 p2) (mul_ne_zero p3 p4)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
