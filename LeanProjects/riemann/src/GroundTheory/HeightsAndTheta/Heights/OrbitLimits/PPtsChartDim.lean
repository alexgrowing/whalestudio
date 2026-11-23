import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar)

theorem PtsChartDim.proof : PtsChartDim.Statement := by
  classical
  intro K _ ι _ P e i hP J hJ

  set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
  have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  have : PQ.IsPrime := hvar.1.isPrime
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
    rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      congr 1
    · simp
  have hdim : ∀ Q ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hext] at hQ
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]
    exact hvar.2
  have hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩

  let g : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
    (rename (PtsSegreChart.coordEquiv (ι := ι))).toRingHom
  let f : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →+* MvPolynomial (Σ k, ι k) ℂ :=
    (rename (PtsSegreChart.coordEquiv (ι := ι)).symm).toRingHom
  have hfg : ∀ b, f (g b) = b := fun b => by simp [f, g, rename_rename]
  have hgf : ∀ a, g (f a) = a := fun a => by simp [f, g, rename_rename]
  have hI : PtsSegreChart.ideal P i = (ReciprocityTheory.AnForm.R.chartIdeal PC i).map g := by
    rw [PtsSegreChart.ideal, ReciprocityTheory.AnForm.R.chartIdeal, Ideal.map_sup, Ideal.map_span, hPC, Ideal.map_map,
      ← Set.range_comp]
    congr 3
    funext k
    simp [g]
  obtain ⟨hmin, hd⟩ := SegreChartDim.minimalPrimes_transfer f g (PtsSegreChart.ideal P i)
    (ReciprocityTheory.AnForm.R.chartIdeal PC i)
    (by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_comap, hfg]
      exact hb)
    (by rw [hI]; exact Ideal.le_comap_map)
    (fun a => by rw [hgf, sub_self]; exact Ideal.zero_mem _)
    (fun b => by rw [hfg, sub_self]; exact Ideal.zero_mem _) J hJ
  rw [hd]
  exact SegreChartDim.ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin

end GroundTheory.Heights₂.Heights
