import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingClassOffOpenOrbitFixedByUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.DblOrbit

theorem integral_eq_zero_of_not_open : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, ∀ φ ∈ degPS V a μ s, ∀ γ ∈ GQ (dblSp V), (¬ ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∀ f₁ f₂ : GA D V → ℂ, Continuous f₁ → Continuous f₂ → GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f₁ → IsCuspFun V f₁ → ∀ (g₂ : GA D V) (Γ' : Subgroup (GA D V)), (∀ x, x ∈ Γ' ↔ x ∈ GQ V ∧ γ * io V (x, 1) * γ⁻¹ ∈ siegel V) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ 𝓖 : Set (GA D V), IsFundamentalDomain Γ' 𝓖 m → IntegrableOn (fun h => GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (γ * x)) f₁ f₂ (h, g₂)) 𝓖 m → ∫ h in 𝓖, GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (γ * x)) f₁ f₂ (h, g₂) ∂m = 0 := by
  intro D V a μ hμ s φ hφ γ hγ hnot f₁ f₂ hf₁ hf₂ hleft hcusp g₂ Γ' hΓ' m hm 𝓖 h𝓖 hint
  haveI := hm
  obtain ⟨r, C, hC, hN, hnorm⟩ := GlobalTheory.T.doublingClass_offOpenOrbit_fixedByUnipotentRadical D V γ hγ hnot
  set N := NA (frameFlag hC) with hNdef
  have hNI : ∀ n, n ∈ N ↔ n ∈ NI V C := fun n => by rw [hNdef, NA_frameFlag hC]
  have hφ' := (mem_degPS V a).1 hφ
  set K : GA D V → ℂ := fun h => φ (γ * io V (h, g₂)) * f₂ g₂ * ((μ (detA V g₂) : ℂ))⁻¹ with hK
  set F : GA D V → ℂ := fun h => conj (f₁ h) with hF
  have hEq : (fun h => GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (γ * x)) f₁ f₂ (h, g₂)) = fun h => K h * F h := by
    funext h; simp only [GlobalTheory.Eis.dblIntegrand, hK, hF]; ring
  rw [hEq] at hint ⊢
  have hΓ'le : ∀ x ∈ Γ', x ∈ GQ V := fun x hx => ((hΓ' x).1 hx).1
  have hΓc : Countable Γ' := by
    refine Function.Injective.countable (f := fun x : Γ' => (⟨x, hΓ'le x x.2⟩ : GQ V)) ?_
    intro x y hxy; exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have hNc : IsClosed (N : Set (GA D V)) := IsoFlag.isClosed_unip _ D.sp.cm _
  have hnormN : ∀ δ ∈ Γ', ∀ n ∈ N, δ * n * δ⁻¹ ∈ N := by
    intro δ hδ n hn
    obtain ⟨h1, h2⟩ := (hΓ' δ).1 hδ
    exact (hNI _).2 (hnorm δ h1 h2 n ((hNI n).1 hn))
  have hsub : Γ'.subgroupOf N = (GQ V).subgroupOf N := by
    ext n
    simp only [Subgroup.mem_subgroupOf]
    refine ⟨fun h => hΓ'le _ h, fun h => (hΓ' _).2 ⟨h, ?_⟩⟩
    obtain ⟨p, hp, -⟩ := hN n ((hNI n).1 n.2)
    rw [hp, mul_inv_cancel_right]; exact p.2
  let κ : Measure N := Measure.haar
  let 𝓝 : Set N := stdDom ((GQ V).subgroupOf N)
  have hcc : Cocompact (GQ V) N := cocompact_single _
  have h𝓝 : IsFundamentalDomain ((GQ V).subgroupOf N) 𝓝 κ := isFundamentalDomain_stdDom _ _
  have h𝓝' : IsFundamentalDomain (Γ'.subgroupOf N) 𝓝 κ := by rw [hsub]; exact h𝓝
  have h𝓝t : κ 𝓝 ≠ ⊤ := hcc.measure_ne_top h𝓝
  have hKc : Continuous K :=
    ((hφ'.2.1.comp (continuous_const.mul ((continuous_io V).comp (continuous_id.prodMk continuous_const)))).mul
      continuous_const).mul continuous_const
  have hFc : Continuous F := Complex.continuous_conj.comp hf₁
  have hKN : ∀ n ∈ N, ∀ h, K (n * h) = K h := by
    intro n hn h
    obtain ⟨p, hp, hp1⟩ := hN n ((hNI n).1 hn)
    have e : io V (n * h, g₂) = io V (n, 1) * io V (h, g₂) := by rw [← map_mul]; simp
    simp only [hK]
    rw [e, ← mul_assoc, hp, mul_assoc (p : GA D (dblSp V)) γ, hφ'.1, hp1]
    simp
  have hKΓ : ∀ δ ∈ Γ', ∀ h, K (δ * h) = K h := by
    intro δ hδ h
    obtain ⟨h1, h2⟩ := (hΓ' δ).1 hδ
    have hq : γ * io V (δ, 1) * γ⁻¹ ∈ siegelQ V :=
      Subgroup.mem_inf.2 ⟨h2, (GQ (dblSp V)).mul_mem ((GQ _).mul_mem hγ (io_mem_GQ V h1 (one_mem _)))
        ((GQ _).inv_mem hγ)⟩
    have e : γ * io V (δ * h, g₂) = (γ * io V (δ, 1) * γ⁻¹) * (γ * io V (h, g₂)) := by
      rw [show ((δ * h, g₂) : GA D V × GA D V) = (δ, 1) * (h, g₂) by simp, map_mul]; group
    simp only [hK]
    rw [e, apply_siegelQ_mul V a hμ hφ hq]
  have hFΓ : ∀ δ ∈ Γ', ∀ h, F (δ * h) = F h := by
    intro δ hδ h; simp only [hF]; rw [hleft δ (hΓ'le δ hδ) h]
  have h0 : ∀ h, ∫ n in 𝓝, F ((n : GA D V) * h) ∂κ = 0 := by
    intro h
    have hc : constTerm (frameFlag hC) f₁ = 0 := (isCuspFun_iff hleft).1 hcusp _ _
    have h1 : constTermOn (GQ V) N f₁ h = 0 := congrFun hc h
    have h2 := (hcc.constTermOn_eq_zero_iff h𝓝 hleft h).1 h1
    simp only [hF]; rw [integral_conj, h2, map_zero]
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D V) m Γ' N hΓc hNc hnormN κ 𝓝 inferInstance h𝓝' h𝓝t K F
    hKc.measurable hFc.measurable hKN hKΓ hFΓ h0 𝓖 h𝓖 hint

end GlobalTheory.DblOrbit
