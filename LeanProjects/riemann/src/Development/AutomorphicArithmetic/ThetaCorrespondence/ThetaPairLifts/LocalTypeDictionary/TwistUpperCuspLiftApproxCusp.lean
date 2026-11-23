import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishingStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
namespace GlobalTheory.UpCuspApprox
end GlobalTheory.UpCuspApprox
namespace GlobalTheory.UpCuspApprox
theorem upperCusp_lift_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P i).Maps) (v : Fin n → SmT (G.P i).M), (∀ l, F l ∈ (G.P i).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g ∂(G.mP i).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hI0 C hC ε hε
  have hω := (hG.arrows.dn i hi).weil
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have e : ∀ h g, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) =
      starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) :=
    fun h g => by rw [GlobalTheory.UpArrowConv.thetaKO_toSgn]
  obtain ⟨C0, A0, hC0⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D R.ψ _ _ _ _ _ hω Φ hΦ
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact _ (hC.image (GlobalTheory.Grid.continuous_ofSgn_symm true _))
  have hK : ∀ h ∈ C, ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ ≤
      C0 * (max H 1) ^ A0 * 2 ^ A0 * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0 := by
    intro h hh g
    have hb : ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ ≤ C0 * (max H 1) ^ A0 * GlobalTheory.Grow.height (G.P i).V g ^ A0 := by
      intro g
      rw [e, RCLike.norm_conj]
      refine (hC0 _ g).trans ?_
      have h1 := hH _ ⟨h, hh, rfl⟩
      have h0 := GlobalTheory.Grow.height_pos (GlobalTheory.Grid.neg (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true _).symm h)
      have hC00 : 0 ≤ C0 := le_trans (norm_nonneg _) ((hC0 1 1).trans (by simp))
      rw [mul_pow, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC00) (pow_nonneg (GlobalTheory.Grow.height_pos _ _).le _)
      exact pow_le_pow_left₀ h0.le (h1.trans (le_max_left _ _)) _
    exact GlobalTheory.Grow.norm_le_quotHeight_pow
      (fun γ hγ g => by rw [e, e, GlobalTheory.UpArrowConv.thetaKO_left_snd hω hΦ _ γ hγ g]) hb g
  set B := C0 * (max H 1) ^ A0 * 2 ^ A0 with hBdef
  have hfin : (G.mP i).ν (G.mP i).fd < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hm.1.1 hm.2
  set Vol := (G.mP i).ν.real (G.mP i).fd with hVol
  have hV0 : 0 ≤ Vol := measureReal_nonneg
  have hB1 : 0 < |B| + 1 := by positivity
  set δ := ε / (2 * ((|B| + 1) * (Vol + 1))) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n, F, v, hF, happ⟩ := _root_.GlobalTheory.T.twist_cusp_form_approx_weighted D R.θ hR.inf hP (G.P i) φ hφ A0 δ hδ
  have hI : ∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν := by
    intro l h
    have hv := val_aut_cusp (hF l) (v l)
    have e' : (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) =
        fun g => starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) * F l (v l) g :=
      funext fun g => by rw [e]
    rw [e']
    exact GlobalTheory.UpArrowConv.conj_thetaKO_mul_integrableOn hP.cuspRapidDecay hR.inf hω hΦ hm.1.1 hm.2 hv.1 hv.2 _
  refine ⟨n, F, v, hF, hI, fun h hh => ?_⟩
  rw [← integral_finset_sum _ (fun l _ => hI l h), ← integral_sub (hI0 h) (integrable_finset_sum _ fun l _ => hI l h)]
  have hpt : ∀ g ∈ (G.mP i).fd, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g‖ ≤ |B| * δ := by
    intro g _
    rw [← Finset.mul_sum, ← mul_sub, norm_mul]
    have h1 := hK h hh g
    have h2 := happ g
    have hq := pow_nonneg (GlobalTheory.Grow.quotHeight_pos (G.P i).V g).le A0
    calc ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ * ‖φ g - ∑ l, F l (v l) g‖
        ≤ (|B| * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0) * ‖φ g - ∑ l, F l (v l) g‖ :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self B) hq)) (norm_nonneg _)
      _ = |B| * (‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0) := by ring
      _ ≤ |B| * δ := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans_lt ?_
  have hε2 : |B| * δ * Vol ≤ ε / 2 := by
    rw [hδdef]
    have : |B| * Vol ≤ (|B| + 1) * (Vol + 1) := by nlinarith [abs_nonneg B]
    calc |B| * (ε / (2 * ((|B| + 1) * (Vol + 1)))) * Vol = (|B| * Vol) * (ε / (2 * ((|B| + 1) * (Vol + 1)))) := by ring
      _ ≤ ((|B| + 1) * (Vol + 1)) * (ε / (2 * ((|B| + 1) * (Vol + 1)))) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ε / 2 := by field_simp
  linarith
end GlobalTheory.UpCuspApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_upperCusp_lift_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P i).Maps) (v : Fin n → SmT (G.P i).M), (∀ l, F l ∈ (G.P i).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g ∂(G.mP i).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.UpCuspApprox.upperCusp_lift_approx_cusp | exact _root_.GlobalTheory.UpCuspApprox.upperCusp_lift_approx_cusp | (intros; apply _root_.GlobalTheory.UpCuspApprox.upperCusp_lift_approx_cusp <;> assumption)
end
