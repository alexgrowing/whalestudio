import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingStepsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawPeriodsLinearRelationsDoubleStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSawStep

variable {D : D7}

theorem per_smul_right {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem per_smul_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (a : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (a • φ) f = a * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (b : ℂ) (f : GA D V → ℂ) : trc e (b • f) = b • trc e f := by
  funext g
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (b : ℂ) (G : GA D T → ℂ)
    (f : WO S T → ℂ) : liftS om ν 𝓕 (b • G) f = b • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem rapidDec_smul {V : HSp D} (b : ℂ) (F : GA D V → ℂ) (hF : RapidDec V F) : RapidDec V (b • F) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun γ hγ g => by simp only [Pi.smul_apply, h1 γ hγ g], h2.const_smul b, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  refine ⟨‖b‖ * C, fun g => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg b)

theorem contAut_zero (V : HSp D) : IsContAut V (fun _ => (0 : ℂ)) := ⟨fun _ _ _ => rfl, continuous_const⟩

theorem perF_smul {c : Comm D} (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (φ : tt.Ch n → GA D (c.X n) → ℂ) (b : ℂ)
    (f : GA D (c.V n) → ℂ) : tt.perF n ρ h φ (b • f) = b * tt.perF n ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => per_smul_right _ _ _ _ _

theorem perF_comb (hPS : PerSum D) {c : Comm D} (hc : c.Is) (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (k : ℂ)
    (co : c.Fr n →₀ ℂ) (φ : tt.Ch n → c.Fr n → GA D (c.X n) → ℂ) (hφ : ∀ β y, IsContAut (c.X n) (φ β y))
    (f : GA D (c.V n) → ℂ) (hf : IsContAut (c.V n) f) :
    tt.perF n ρ h (fun β => k • ∑ y' ∈ co.support, co y' • φ β y') f =
      k * ∑ y' ∈ co.support, co y' * tt.perF n ρ h (fun β => φ β y') f := by
  have e : ∀ β, (c.B n ρ h).per c.ψ (k • ∑ y' ∈ co.support, co y' • φ β y') (trc (tt.e n β) f) =
      k * ∑ y' ∈ co.support, co y' * (c.B n ρ h).per c.ψ (φ β y') (trc (tt.e n β) f) := by
    intro β
    have hT : IsContAut _ (trc (tt.e n β) f) :=
      (((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std ρ (c.B n ρ h) (fun _ => 0) (contAut_zero _)).2 (tt.e n β) f hf).1)
    rw [per_smul_left]
    congr 1
    exact hPS c.ψ hc.std ρ (c.B n ρ h) (trc (tt.e n β) f) hT (c.Fr n) co.support co (fun y' => φ β y') (fun y' _ => hφ β y')
  simp only [Tup.perF, e]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.mul_sum]

set_option maxHeartbeats 2000000 in

theorem stepX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D →
    RapidVal D → ValMove D → PerSum D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ValX t → TwoX t → RdX t → StepX t := by
  intro hHC D c 𝒯 t hDS hRV hVM hPS hc ht hloc hVal hTwo hRd
  intro j σ h I _ s α ψ G hψ hvan y v
  obtain ⟨χ0, hχ0⟩ := hRd j (by omega)
  have hφ : ∀ i a, IsContAut (c.X j) ((t (s i)).rd j a (ψ i) y) := fun i a => (hχ0 (s i) (ψ i) (hψ i) a y).1
  have hspan : GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) := hc.span (j + 1) (by omega)
  simp only [Tup.per]
  refine GlobalTheory.T.period_linear_relation_density_of_unfolding_steps hHC D c 𝒯 t hc j (σ + 1) h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).io (j + 1) (G i))) ht hφ
    (c.V (j + 1 + 1)) (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) hspan ?_ v
  intro P₁ P₂ v''
  have key : ∀ i, ((t (s i)).cI j * (t (s i)).cI (j + 1)) •
      ((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v'')) =
      liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
        ((t (s i)).pt j P₁) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'', liftS_smul, (ht (s i)).io j (by omega) _ P₁ _, smul_smul, mul_comm]
  have e : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
      (((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v''))) =
      α i * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
        (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
          (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
          ((t (s i)).pt j P₁)) := by
    intro i
    rw [← key i, perF_smul, mul_assoc]
  rw [Finset.sum_congr rfl fun i _ => e i]
  have hR0 : ∀ i, RapidDec _ ((G i).1 v'') := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    exact hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) v''
  have hR1 : ∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'')
      ((t (s i)).pt (j + 1) P₂)) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'']
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1) (by omega)
    exact rapidDec_smul _ _ (hRV c.θ hc.inf _ _ (c.M (j + 1)) J χ _ (hJ ((t (s i)).io (j + 1) (G i)).2) _)
  refine GlobalTheory.T.seeSaw_periods_linearRelations_doubleStep D c 𝒯 t hDS hc ht hloc j σ h P₁ P₂ I s α (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (G i).1 v'')
    hφ hR0 hR1 ?_
  intro a ha a' ha'
  obtain ⟨C, hC, hCe⟩ := hVal j σ h P₁ P₂ a ha a' ha'
  obtain ⟨co, hco⟩ := hTwo j (by omega) C hC y
  obtain ⟨sm, hsm⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D c.θ (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) hc.inf a' ha'
  refine ⟨fun i => (t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v'')),
    fun i => hCe (s i) (ψ i) (hψ i) y (G i) v'', ?_⟩
  obtain ⟨χ2, hχ2⟩ := hRd (j + 1 + 1) (by omega)
  have hψ'' : ∀ i, (t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i))) ∈ (t (s i)).Ram (j + 1 + 1) := fun i =>
    (ht (s i)).stabK (j + 1) (by omega) _ ((ht (s i)).stabK j (by omega) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
  have term : ∀ i, α i * ((t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v''))) =
      ∑ y' ∈ co.support, co y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1)) *
        (t (s i)).per (j + 1 + 1) σ (idx_step h) ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (G i) y' (sm v'')) := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    have hw : rTrans a' ((G i).1 v'') = (G i).1 (sm v'') := (hsm J χ (G i).1 (hJ (G i).2) v'').symm
    have htwo : (t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ co.support, co y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext (hco (s i) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
    have hGw : RapidDec _ ((G i).1 (sm v'')) := hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) _
    rw [hw, htwo, perF_comb hPS hc _ _ _ _ _ co _ (fun β y' => (hχ2 (s i) _ (hψ'' i) β y').1) _ ⟨hGw.1, hGw.2.1⟩]
    simp only [Tup.per, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => term i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hvan y' (sm v''), mul_zero]

end GlobalTheory.SeeSawStep

end
