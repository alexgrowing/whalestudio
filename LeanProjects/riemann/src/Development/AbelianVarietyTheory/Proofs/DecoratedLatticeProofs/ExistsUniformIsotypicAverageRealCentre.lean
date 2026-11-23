import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgMidUnif

open GlobalTheory.AvgMid

theorem exists_isotypic_uniform : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (χ₃ : GA D S → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → IsBiSmooth C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k₀.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v) → ∃ (C₂ : WO A S → WO S A' → ℂ) (χ₂ : GA D S → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₂ ∧ (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₂ u v) = χ₁ a • fun u => C₂ u v) ∧ (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k₀'.om (b, 1) (C₂ u) = χ₂ b • C₂ u) ∧ ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) = biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₂) := by
  intro D _ hF _ ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ _ h1 h3
  obtain ⟨χA, χS, hwa⟩ := hk₀.weil
  obtain ⟨χS', χA', hwb⟩ := hk₀'.weil
  by_cases h0 : ∀ u v, C₁ u v = 0
  · refine ⟨C₁, fun _ => 1, hC₁, h1, fun b _ _ u => ?_, fun _ _ _ _ _ _ _ _ => rfl⟩
    rw [show C₁ u = 0 from funext (h0 u), map_zero, smul_zero]
  push_neg at h0
  obtain ⟨u₀, v₀, h0⟩ := h0
  have hv : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ = χ₃ b.1 * C₁ u₀ v₀ :=
    fun b => congrFun (h3 b.1 b.2.1 b.2.2 v₀) u₀
  have hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1 := by
    have : (fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1) =
        fun b => k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ / C₁ u₀ v₀ := funext fun b => by rw [hv, mul_div_cancel_right₀ _ h0]
    rw [this]
    exact ((hwa.om_cont _ (hC₁.left v₀).1 u₀).comp (continuous_const.prodMk continuous_subtype_val)).div_const _
  have hm : ∀ b b' : ↥(GinfC S ⊓ Subgroup.center (GA D S)), χ₃ (b.1 * b'.1) = χ₃ b.1 * χ₃ b'.1 := fun b b' => by
    have e := hv (b * b')
    have e' : ((1, (b * b').1) : GA D A × GA D S) = (1, b.1) * (1, b'.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, h3 b'.1 b'.2.1 b'.2.2, map_smul, Pi.smul_apply, hv, smul_eq_mul] at e
    refine mul_right_cancel₀ h0 ?_
    rw [← Subgroup.coe_mul, ← e]
    ring
  obtain ⟨hcpt, ν, hν, hν'⟩ := exists_haar hy
  obtain ⟨W, hW, hWf⟩ := hF ψ θ hθ A S x y hx hy k₀ hk₀ χ₁
  let E : Submodule ℂ (WO A S → ℂ) := Submodule.span ℂ (Set.range fun v u => C₁ u v)
  haveI : FiniteDimensional ℂ E := by
    refine Submodule.finiteDimensional_of_le (S₂ := W.map (pureTensorO ψ θ A S x.s y.s x.B y.B k₀.vac))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨v, rfl⟩
    obtain ⟨P, hP, e⟩ := hWf _ (hC₁.left v).1 (hC₁.left v).2 (fun a ha hc => h1 a ha hc v)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  have hEv : E ≤ vacSub ψ A S (latO A S x.L y.L fun _ => True) := Submodule.span_le.2 (by
    rintro _ ⟨v, rfl⟩; exact hC₁.left v)
  have hEe : ∀ (p : GA D A × GA D S) (c : ℂ), (∀ v, k₀.om p (fun u => C₁ u v) = c • fun u => C₁ u v) →
      ∀ f ∈ E, k₀.om p f = c • f := fun p c h f hf => by
    have : E ≤ LinearMap.eqLocus (k₀.om p) (c • LinearMap.id) := Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact h v)
    exact this hf
  obtain ⟨n, e, g, he, hg, hs⟩ := GlobalTheory.SeeSaw.FinRank.sum_prod_of_slices C₁ E
    (vacSub ψ S A' (latO S A' y.L z.L fun _ => True)) (fun v => Submodule.subset_span ⟨v, rfl⟩) hC₁.right
  have hg' : ∀ i, mean k₀'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
    vac_mean hwb hθ hχ (hg i)
  have hl : ∀ v, (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) ∈ E := fun v => by
    have : (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, mean k₀'.om ν χ₃ (g i) v • e i := by
      funext u; simp [Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  have hr : ∀ u, (fun v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, e i u • mean k₀'.om ν χ₃ (g i) := fun u => by
    funext v; simp [Finset.sum_apply]
  refine ⟨fun u v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v, fun b => χ₃ b⁻¹, ⟨?_, fun v => hEv (hl v), fun u => ?_⟩,
    fun a ha hc v => hEe _ _ (h1 a ha hc) _ (hl v), fun b hb hc u => ?_, fun k k' hk hk' hag hag' φ hφ => ?_⟩
  · exact continuous_finset_sum _ fun i _ => ((hEv (he i)).1.cont.comp continuous_fst).mul
      ((hg' i).1.cont.comp continuous_snd)
  · rw [hr]
    exact (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg' i) :
      _ ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True))
  · simp only []
    rw [hr, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_comm]
    exact congrArg _ (eigen_mean hwb hθ hχ hm (hg i).1 ⟨b, hb, hc⟩)
  · obtain ⟨χA₁, χS₁, hwa₁⟩ := hk.weil
    obtain ⟨χS₁', χA₁', hwb₁⟩ := hk'.weil

    have hmean : ∀ i, mean k₀'.om ν χ₃ (g i) = mean k'.om ν χ₃ (g i) := fun i => by
      funext w
      simp only [mean]
      congr 1
      funext b
      rw [hag' b.1 b.2.1 1 (GinfC A').one_mem (g i) (hg i).1]
    have hEk : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), ∀ f ∈ E, k.om (1, b.1) f = χ₃ b.1 • f :=
      fun b f hf => by
        rw [hag 1 (GinfC A).one_mem b.1 b.2.1 f (hEv hf).1]
        exact hEe _ _ (h3 b.1 b.2.1 b.2.2) f hf
    have hg'' : ∀ i, mean k'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
      vac_mean hwb₁ hθ hχ (hg i)
    simp only [hmean]
    funext h₂
    have hX : ∀ i, IsThetaFunO ψ A S (comb ψ A S k.c (e i)) := fun i => theta_comb hwa₁.std hk.fin (hEv (he i)).1
    rw [show C₁ = fun u v => ∑ i, e i u * g i v from funext fun u => funext (hs u), biComb_sum, biComb_sum,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg i).1) hφ,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg'' i).1) hφ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [comb_mean hwb₁ hχ hk'.fin (hg i).1]
    refine (lift_mean hwb₁ hθ hy.cpt y.vol hχ (theta_comb hwb₁.std hk'.fin (hg i).1)
      (contAut_lift hwa₁ hx.cpt x.vol (hX i) hφ) (fun b h => ?_) h₂).symm
    rw [← integral_const_mul]
    congr 1
    funext a
    have e' : ((a, h * b.1) : GA D A × GA D S) = (a, h) * (1, b.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, GlobalTheory.FrComb.om_comb hwa₁ (GinfC A).one_mem b.2.1 hk.fin (hEv (he i)).1,
      hEk b _ (he i), comb_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.AvgMidUnif

end
