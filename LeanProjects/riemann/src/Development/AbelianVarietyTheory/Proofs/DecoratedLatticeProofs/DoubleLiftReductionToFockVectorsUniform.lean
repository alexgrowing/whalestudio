import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlicesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProductsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniformIsotypicAverageRealCentreStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenAvg

theorem exists_central_average_uniform : ∀ (D : D7), BiAct D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A S A' : HSp D)
    (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y →
    k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
    (∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0) →
    ∃ (C₁ : WO A S → WO S A' → ℂ) (χ₁ : GA D A → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ ∧ IsBiSmooth C₁ ∧
      (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) ∧
      ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
        (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) →
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) := by
  intro D hB ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hv hs ⟨φ₀, hφ₀, hc₀, hne⟩
  obtain ⟨χA, χS, ha⟩ := hk₀.weil
  obtain ⟨χS', χA', hb⟩ := hk₀'.weil
  obtain ⟨i1, -, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A
  let Z : Subgroup (GA D A) := GinfC A ⊓ Subgroup.center (GA D A)
  have hcl : IsClosed (Subgroup.center (GA D A) : Set (GA D A)) := by
    have : (Subgroup.center (GA D A) : Set (GA D A)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp ((GlobalTheory.T.isCompact_realPoints_of_definiteHermitianSpaceData D A x hx).inter_right hcl)
  let ν : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hne
  have hh : φ₀ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hc₀ _ b.2.1 b.2.2, hc₀ _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ₀ (h₀ * a) / φ₀ h₀ := by
      funext a
      rw [hc₀ _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ₀.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D A) ∈ GinfC A := fun a => a.2.1
  have hC := GlobalTheory.FrComb.biTheta_of_vac hx.sd hy.sd hz.sd hv hs
  refine ⟨avg k₀.om ν Subtype.val (fun a => χ a) C, fun a => χ a⁻¹,
    isBiVac_avg ν ha hb hB continuous_subtype_val hj hcont hC hv,
    (isBiTheta_avg ν ha hb hB continuous_subtype_val hj hcont hC).smooth, fun a ha1 ha2 v => ?_, ?_⟩
  · funext u
    rw [om_avg ν ha hb hB continuous_subtype_val hj hcont hC]
    let a' : Z := ⟨a, ha1, ha2⟩
    simp only [Pi.smul_apply, smul_eq_mul, avg]
    rw [← integral_const_mul, ← integral_mul_left_eq_self (μ := ν)
      (fun b : Z => χ a⁻¹ * (χ b * k₀.om (b, 1) (fun u' => C u' v) u)) a']
    congr 1
    funext b
    have e : χ a⁻¹ * χ a = 1 := by
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel] at this
      exact this.symm.trans hone
    rw [hmul, ← mul_assoc, ← mul_assoc]
    change _ = χ a⁻¹ * χ a * χ b * k₀.om (a * b, 1) (fun u' => C u' v) u
    rw [e, one_mul]
  intro k k' hk hk' hag φ hφ hcφ
  obtain ⟨χA₁, χS₁, ha₁⟩ := hk.weil
  obtain ⟨χS₁', χA₁', hb₁⟩ := hk'.weil
  have eavg : avg k₀.om ν Subtype.val (fun a => χ a) C = avg k.om ν Subtype.val (fun a => χ a) C := by
    funext u v
    simp only [avg]
    congr 1
    funext a
    rw [hag a a.2.1 1 (GinfC S).one_mem _ (hv.left v).1]
  rw [eavg]
  have hG := GlobalTheory.FrComb.biTheta_combL ha₁.std (GlobalTheory.FrComb.biTheta_combR ha₁.std hC hk'.fin) hk.fin
  rw [biComb_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hC hk.fin hk'.fin]
  change IsBiTheta ψ A S A' (biComb ψ A S A' k.c k'.c C) at hG
  generalize biComb ψ A S A' k.c k'.c C = G at hG
  funext h₂
  unfold biLift
  congr 1
  funext h₁
  have hF : IsContAut A fun h => φ h * k'.om (h₁, h₂) (fun v => k.om (h, h₁) (fun u => G u v) 0) 0 := by
    refine ⟨fun γ hγ g => ?_, hφ.2.mul ?_⟩
    · have : ∀ v, k.om (γ * g, h₁) (fun u => G u v) 0 = k.om (g, h₁) (fun u => G u v) 0 := fun v => by
        rw [← ha₁.om_aut γ hγ 1 (one_mem _) _ (ha₁.om_pres (g, h₁) _ (GlobalTheory.FrComb.slice_left hG v)), ← Module.End.mul_apply,
          ← map_mul, Prod.mk_mul_mk, one_mul]
      simp only [this, hφ.1 γ hγ g]
    · exact (hB ψ A S A' _ _ _ _ _ _ ha₁ hb₁ G hG).2.2.2.comp
        (show Continuous fun h : GA D A => ((h, h₁), (h₁, h₂), (0 : WO A S), (0 : WO S A')) from
          (continuous_id.prodMk continuous_const).prodMk continuous_const)
  rw [← integral_mean ν hx.cpt x.vol continuous_subtype_val hF]
  congr 1
  funext h
  rw [ker_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hG, ← integral_const_mul]
  congr 1
  funext a
  rw [hcφ _ a.2.1 a.2.2]
  ring

end GlobalTheory.CenAvg

namespace GlobalTheory.SeeSaw

theorem fockRed_uniform : ∀ D : D7, BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → k.vac = k₀.vac → k'.vac = k₀'.vac → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → HasCen A χ φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm
  by_cases h0 : ∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0
  · obtain ⟨C₁, χ₁, hC₁, hs₁, he₁, heq₁⟩ :=
      GlobalTheory.CenAvg.exists_central_average_uniform D hBi ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm h0
    obtain ⟨χ₃, h₃⟩ := GlobalTheory.T.realCentre_acts_by_character_on_isotypic_slices D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ C₁ hC₁ he₁
    obtain ⟨C₂, χ₂, hC₂, he₂, hf₂, heq₂⟩ :=
      GlobalTheory.T.exists_uniform_isotypic_average_real_centre D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ hs₁ he₁ h₃
    obtain ⟨n, P, P', hp⟩ := GlobalTheory.T.centralEigen_realDatum_finite_sum_fockProducts D hCF ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₂ C₂ hC₂ he₂ hf₂
    refine ⟨n, P, P', fun k k' hk hk' hv hv' hag hag' φ hφ hcen => ?_⟩
    rw [heq₁ k k' hk hk' hag φ hφ hcen, heq₂ k k' hk hk' hag hag' φ hφ,
      GlobalTheory.T.doubleLift_fockSum_eq_sum_iteratedLifts D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C₂ (by rw [hv, hv']; exact hp) φ hφ]
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k k' _ _ _ _ _ _ φ hφ hcen => ?_⟩
    have e : φ = 0 := by
      by_contra hne
      exact h0 ⟨φ, hφ, hcen, hne⟩
    subst e
    funext h₂
    simp [biLift]

end GlobalTheory.SeeSaw

end
