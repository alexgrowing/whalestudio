import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProductsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenUnitCCOf

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.Rg.Rs.C3.UC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

set_option maxHeartbeats 1000000 in

theorem spehCosocle_uc (hG : PositivityTheory.RgUd.Exp.GenUnitCC) (hSC : GlobalTheory.Published.StandardCosocleGL)
    [CharZero k] (x : GlobalTheory.LocGL.IrrGL k) (hg : GlobalTheory.LocGL.IsGeneric x.rep)
    (hu : GlobalTheory.SmGL.IsUnitarisable x.rep) (d : ℕ) (hd : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W),
      GlobalTheory.LocGL.IsCosocle τ (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd) := by
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, ⟨φ⟩⟩ := hG k _ _ x.rep x.2.rep.smooth x.2.rep.irr hu hg
  let y : Fin d → Fin m → IrrGL k := fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = (spehFactor x d i).1 := fun _ => hd0
  let Y : Fin (d * m) → IrrGL k := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = N := by
    rw [← hd, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (spehFactor x d i).rep.Equiv (prodIrr (y i) (hN i)) := fun i =>
    (x.twEquiv _ (isSmoothChar_absPow _)).symm.trans
      ((twistEquiv φ _).trans (prodIrrTwistEquiv _ hd0 _ (isSmoothChar_absPow _)))
  obtain ⟨e2⟩ := GlobalTheory.T.parabolicInduction_in_stages_product_of_products k d m y (fun i => (spehFactor x d i).1) N hN hd hM'
  let E := (multiProdEquiv _ e1).trans e2
  let Γs : Fin (d * m) → Segment k := fun p =>
    ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact GlobalTheory.isLSeg_nu (GlobalTheory.isLSeg_nu (hΔ _) _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply, GlobalTheory.segment_nu_nu] at hP
    have key := PositivityTheory.RgUd.UOrder.add_one_le_of_precedes_u k (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j')
      (hδu j') (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ)))
      (by push_cast at hP ⊢; exact hP)
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    have := abs_lt.1 (hs j)
    have := abs_lt.1 (hs j')
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨GlobalTheory.univ_map_speh_segments d m Δ s, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hSC k _ (d * m) N Y hM' hLF
  exact ⟨_, _, _, π.ρ, hπ.of_equiv (.refl _) E.symm⟩

end PositivityTheory.Rg.Rs.C3.UC

end
