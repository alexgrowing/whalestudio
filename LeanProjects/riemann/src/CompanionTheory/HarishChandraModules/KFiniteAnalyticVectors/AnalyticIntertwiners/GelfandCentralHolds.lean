import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.SobApproxHolds
import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CasScalar
import CompanionTheory.AutomorphicTheory.HarishChandraMultiplicity.HCMult

open Matrix Topology Filter
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_smD_A {v : H} (hv : v ∈ smD ε σ) :
    Formalism.L2.Theta.SmoothVec (Formalism.IndefR.Tow.SobPf.lieG (Formalism.REAL.Jm ε)) σ v := by
  rw [mem_smD_iff] at hv
  intro m Xs hX
  have hc := Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_contDiff m Xs
  have hmem : ∀ t : Fin m → ℝ, Formalism.QuantumDeterminants.inUH (Formalism.REAL.Jm ε)
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) :=
    fun t => Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_mem _ m Xs (fun i => hX i) t
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨U, F, hU, h0, hF, hEq⟩ := hv _ (hmem t0)
  have hev : (fun t : Fin m → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) v)
      =ᶠ[𝓝 t0] fun t => F ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) := by
    filter_upwards [hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hEq _ ht (hmem t)
  exact ((hF.contDiffAt (hU.mem_nhds h0)).comp t0 hc.contDiffAt).congr_of_eventuallyEq hev

theorem isGRep_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ :=
  ⟨hσ.1.1, hσ.1.2, hσ.2.1, hσ.2.2⟩

theorem cartan_A : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) := by
  have h2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> norm_num
  have hh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Jm_conjTranspose_self
  refine ⟨h2, ?_, ?_⟩
  · rw [hh, h2, Matrix.one_mul]
  · rw [h2]; exact Matrix.PosDef.one

theorem kfin_of_kfinG_A {a : H}
    (h : Formalism.IndefR.Tow.SobPf.KFinG (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ a) : Formalism.MainNotions.S.IsKFin ε σ a := by
  obtain ⟨W, hW, haW, hst⟩ := h
  refine ⟨W, hW, haW, fun g hg x hx => hst g ⟨mem_UJset_of_mem_kset hg, hg.2⟩ x hx⟩

theorem exists_kfin_near_A [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {w : H}
    (hw : w ∈ smD ε σ) {δ : ℝ} (hδ : 0 < δ) : ∃ a : H, Formalism.MainNotions.S.IsKFin ε σ a ∧ ‖a - w‖ < δ := by
  obtain ⟨a, -, haK, ha⟩ := CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ cartan_A
    (isGRep_A hσ) w (smoothVec_of_smD_A hw) [[]] (by simp) δ hδ
  exact ⟨a, kfin_of_kfinG_A haK, by simpa [Formalism.IndefR.Tow.SobPf.dL] using ha [] (by simp)⟩

theorem eq_zero_of_perp_A [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {w : H}
    (hw : w ∈ smD ε σ) (h : ∀ a : H, Formalism.MainNotions.S.IsKFin ε σ a → ⟪a, w⟫_ℂ = 0) : w = 0 := by
  refine norm_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (norm_nonneg _))
  rw [zero_add]
  obtain ⟨a, ha, hlt⟩ := exists_kfin_near_A hσ hw hδ
  have h1 : ‖w‖ ^ 2 = RCLike.re ⟪w - a, w⟫_ℂ := by
    rw [inner_sub_left, map_sub, h a ha, map_zero, sub_zero, inner_self_eq_norm_sq]
  have h2 : RCLike.re ⟪w - a, w⟫_ℂ ≤ ‖w - a‖ * ‖w‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [norm_sub_rev] at h2
  by_cases h0 : ‖w‖ = 0
  · rw [h0]; exact hδ.le
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem casimir_symm_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (x y : smD ε σ) :
    ⟪casimir (smE ε σ) x, y⟫_ℂ = ⟪x, casimir (smE ε σ) y⟫_ℂ := by
  have hU := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hU, hU, ← mul_assoc]
  have : adjSign ε a b * adjSign ε b a = 1 := by
    unfold adjSign
    by_cases h : ε a = ε b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, one_mul]

end CompanionTheory.D.gk.HC
