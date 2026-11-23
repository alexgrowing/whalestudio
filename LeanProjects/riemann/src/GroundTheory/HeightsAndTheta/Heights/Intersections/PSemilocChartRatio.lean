import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocChartRatio
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFibreOverFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocChartRatio.proof (hF : FibreOverFinite.Statement) : SemilocChartRatio.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s α W i' hv hP' hZ hs hsn hW hi' q
  have hSf : (insert P' (fibreOver v P' W)).Finite :=
    (hF K ι K' ι' κ v P' n s α W hv hP' hZ hs hsn hW).insert P'
  have hSp : ∀ V ∈ insert P' (fibreOver v P' W), IsMultiProjPrime V := by
    rintro V (rfl | hV)
    · exact hP'.2.1
    · exact hV.1
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid _ hSf hSp
  obtain ⟨w, hwd, hwS⟩ := hd₀ (Pi.single q.1 1 + d₀) le_add_self
  have hPp : P'.IsPrime := hP'.2.1.1
  have hwP' : w ∉ P' := hwS P' (Set.mem_insert _ _)
  have hwnz : Ideal.Quotient.mk P' w ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  set N : MRing ι' := ∏ k, (X ⟨k, i' k⟩ : MRing ι') ^ d₀ k with hN
  have hNd : IsMultiHomog N d₀ := AvoidRing.isMultiHomog_coordProd i' d₀
  have hNP : N ∉ P' := AvoidRing.coordProd_not_mem hPp i' hi' d₀
  have hwW : ∀ W' ∈ fibreOver v P' W, w ∉ W' := fun W' hW' => hwS W' (Set.mem_insert_of_mem _ hW')
  have gen : ∀ u : MRing ι', IsMultiHomog u (Pi.single q.1 1 + d₀) →
      IsLocalization.mk' (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' u) ⟨_, hwnz⟩ ∈
        semiLocRing P' (fibreOver v P' W) := fun u hu =>
    Subring.subset_closure ⟨u, w, _, hwnz, hwW, hu, hwd, rfl⟩
  have hq : IsMultiHomog (X q * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 q.2) hNd
  have hc : IsMultiHomog (X ⟨q.1, i' q.1⟩ * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 (i' q.1)) hNd
  refine ⟨⟨_, gen _ hq⟩, ⟨_, gen _ hc⟩, ?_, ?_⟩
  · show IsLocalization.mk' _ _ _ ≠ (0 : FractionRing (MRing ι' ⧸ P'))
    rw [Ne, IsFractionRing.mk'_eq_zero_iff_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    rcases hPp.mem_or_mem h with h | h
    · exact hi' q.1 h
    · exact hNP h
  · show IsLocalization.mk' _ _ _ * _ = IsLocalization.mk' _ _ _ * _
    rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm (IsLocalization.mk' _ _ _),
      IsLocalization.mul_mk'_eq_mk'_of_mul]
    congr 1
    simp only [map_mul]
    ring

end GroundTheory.Heights₂.Heights.Inter
