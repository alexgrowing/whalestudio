import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem up_ne (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {π ρ : M.Ty P} (h : M.Up P l π ρ) :
    ρ ≠ π := by
  rintro rfl
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 : l - 1 + 1 = l := by omega
  simp [h2] at h1

theorem up_idx (P : M.Par) {j l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {π ρ : M.Ty P} (h : M.Up P l π ρ)
    (h' : M.Up P j π ρ) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h3 := h' ⟨l - 1, by omega⟩
  have h2 : l - 1 + 1 = l := by omega
  by_contra hne
  have hne' : ¬ l = j := fun e => hne e.symm
  simp only [h2, if_true, hne', if_false] at h1 h3
  omega

theorem up_det (P : M.Par) {j : ℕ} {σ σ' ρ : M.Ty P} (h : M.Up P j σ σ') (h' : M.Up P j σ ρ) : σ' = ρ := by
  funext i
  apply Fin.ext
  rw [h i, h' i]

theorem algebraic_shift_holds : AlgSS := by
  intro P 𝒜 _ _ _ d hR l hl π ρ hUp Y
  obtain ⟨-, hκ, -, hSS, -, -⟩ := hR
  have hne := up_ne P hl hUp
  have hmul : ∀ f : M.Ty P → ℂ, d.κ f * d.κ (Pi.single π 1) = f π • d.κ (Pi.single π 1) := by
    intro f
    rw [← map_mul, ← map_smul]
    congr 1
    funext σ
    by_cases h : σ = π
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h0 : d.κ (Pi.single ρ 1) * d.κ (Pi.single π 1) = 0 := by
    rw [hmul, Pi.single_eq_of_ne hne.symm, zero_smul]
  have cGG : Commute (d.κ (Pi.single ρ 1)) d.L.GG := hκ _ _ (by simp [R.LevelData.fns])
  have cl0 : Commute (d.κ (Pi.single π 1)) (d.L.l0 Y) := by
    unfold R.LevelData.l0
    refine Commute.sub_right (Commute.neg_right (hκ _ _ (by simp))) (Commute.mul_right
      (Algebra.commute_algebraMap_right _ _) (Commute.mul_right (hκ _ _ (by simp [R.LevelData.fns]))
        (hκ _ _ (by simp [R.LevelData.fns]))))
  have t1 : d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1) = 0 := by
    have e : d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1) =
        d.L.GG * (d.κ (Pi.single ρ 1) * (d.x Y * d.κ (Pi.single π 1))) * d.L.l0 Y := by
      calc d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1)
          = (d.κ (Pi.single ρ 1) * d.L.GG) * d.x Y * (d.L.l0 Y * d.κ (Pi.single π 1)) := by
            simp only [mul_assoc]
        _ = (d.L.GG * d.κ (Pi.single ρ 1)) * d.x Y * (d.κ (Pi.single π 1) * d.L.l0 Y) := by
            rw [cGG.eq, cl0.eq]
        _ = _ := by simp only [mul_assoc]
    rw [e, Q.NFData.x, hmul, mul_smul_comm, h0, smul_zero, mul_zero, zero_mul]
  have t2 : ∀ j ∈ Finset.Icc 1 (P.k - 1),
      d.κ (Pi.single ρ 1) * (d.SS j * d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1) =
        if j = l then M.xEx P {j} π Y • (d.SS j * d.κ (Pi.single π 1)) else 0 := by
    intro j _
    have hs := hSS j (fun σ => if M.Up P j σ ρ then 1 else 0) (Pi.single ρ 1) (by
      intro σ σ' h
      by_cases hσ : σ' = ρ
      · subst hσ; simp [h]
      · rw [Pi.single_eq_of_ne hσ, if_neg]
        intro h'
        exact hσ (up_det P h h'))
    calc d.κ (Pi.single ρ 1) * (d.SS j * d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1)
        = (d.κ (Pi.single ρ 1) * d.SS j) * ((d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1)) := by
          simp only [mul_assoc]
      _ = M.xEx P {j} π Y • (d.SS j * ((d.κ fun σ => if M.Up P j σ ρ then 1 else 0) * d.κ (Pi.single π 1))) := by
          rw [hs, hmul, mul_smul_comm, mul_assoc]
      _ = M.xEx P {j} π Y • (d.SS j * ((if M.Up P j π ρ then (1 : ℂ) else 0) • d.κ (Pi.single π 1))) := by
          rw [hmul]
      _ = _ := by
          by_cases hjl : j = l
          · subst hjl; simp [hUp]
          · have hn : ¬ M.Up P j π ρ := fun h => hjl (up_idx P hl hUp h)
            simp [hn, hjl]
  have hQ : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  rw [hQ, mul_add, add_mul, t1, zero_add, Q.NFData.weightedSumBis, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl t2, Finset.sum_ite_eq', if_pos hl]

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
