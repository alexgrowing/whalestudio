import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

def contLeft (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨hF.add hG, fun γ hγ g => by simp [hF' γ hγ g, hG' γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    exact ⟨continuous_const.mul hF, fun γ hγ g => by simp [hF' γ hγ g]⟩

theorem rTrans_mem {V : HSp D} (t : GA D V) {F : GA D V → ℂ} (hF : F ∈ contLeft V) : rTrans t F ∈ contLeft V :=
  ⟨hF.1.comp (continuous_id.mul continuous_const), fun γ hγ g => by
    simp only [rTrans, mul_assoc]; exact hF.2 γ hγ (g * t)⟩

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  exact hψ.1.2.1 _

theorem per_add_bound {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) (Ω : Set (GA D B.V)) (hΩc : IsCompact Ω)
    (hΩ : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) :
    ∃ C : ℝ, (∀ f g, f ∈ contLeft B.V → g ∈ contLeft B.V → B.per ψ φ (f + g) = B.per ψ φ f + B.per ψ φ g) ∧
      ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) → ‖B.per ψ φ f‖ ≤ C * K := by
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut B.cpt hφ
  have hμ : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.Unf.vol_fund_lt_top B.cpt B.vA
  have hν1 : B.vN.ν B.vN.𝓝 = 1 := B.vN.unit.2.2
  have hν : B.vN.ν B.vN.𝓝 < ⊤ := by rw [hν1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  have hψc : Continuous ψ := hψ.1.1
  have hemb := GlobalTheory.Unf.BesSemi.continuous_embA B.d B.o
  have hpsi := GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψc 1 (vecB B.o B.ζ)

  have hsup : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ (h : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h)‖ ≤ K := by
    intro f hf K hK h n
    have hs : n.1 * embA B.d B.o h ∈ besGrp B.d B.o :=
      mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    obtain ⟨γ, hγ, hγs⟩ := hΩ _ hs
    rw [← hf.2 γ (Subgroup.mem_inf.1 hγ).1]
    exact hK _ hγs
  have hbd : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ h n, ‖GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n‖ ≤ Cφ * K := by
    intro f hf K hK h n
    simp only [GlobalTheory.MixPer.besFun, norm_mul, norm_star, norm_psiBes hψ, mul_one]
    exact mul_le_mul (hCφ h) (hsup f hf K hK h n) (norm_nonneg _) ((norm_nonneg _).trans (hCφ h))
  have hcont : ∀ f, f ∈ contLeft B.V → ∀ h, Continuous (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) := by
    intro f hf h
    change Continuous fun n : flagN B.d => φ h * f (n.1 * embA B.d B.o h) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)
    exact (continuous_const.mul (hf.1.comp (continuous_subtype_val.mul continuous_const))).mul
      (continuous_star.comp (hpsi.comp continuous_subtype_val))
  have hcontH : ∀ f, f ∈ contLeft B.V → ∀ n : flagN B.d,
      Continuous fun h => GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n := by
    intro f hf n
    simp only [GlobalTheory.MixPer.besFun]
    exact (hφ.2.mul (hf.1.comp (continuous_const.mul hemb))).mul continuous_const
  have hK : ∀ f, f ∈ contLeft B.V → ∃ K : ℝ, ∀ x ∈ Ω, ‖f x‖ ≤ K := by
    intro f hf
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hf.1.continuousOn
    exact ⟨K, hK⟩
  have hin : ∀ f, f ∈ contLeft B.V → ∀ h,
      IntegrableOn (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν := by
    intro f hf h
    obtain ⟨K, hK⟩ := hK f hf
    exact Measure.integrableOn_of_bounded hν.ne (hcont f hf h).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n => hbd f hf K hK h n)
  have houtC : ∀ f, f ∈ contLeft B.V →
      Continuous fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA B.A
    exact continuous_of_dominated (bound := fun _ => Cφ * K)
      (fun h => (hcont f hf h).aestronglyMeasurable)
      (fun h => Filter.Eventually.of_forall fun n => hbd f hf K hK h n) (integrable_const _)
      (Filter.Eventually.of_forall fun n => hcontH f hf n)
  have hout : ∀ f, f ∈ contLeft B.V →
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    refine Measure.integrableOn_of_bounded (M := Cφ * K * B.vN.ν.real B.vN.𝓝) hμ.ne (houtC f hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => ?_)
    exact norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK h n
  refine ⟨Cφ * B.vA.μ.real B.vA.𝓕, fun f g hf hg => ?_, fun f hf K hK' => ?_⟩
  · have e : ∀ h n, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ (f + g) h n =
        GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n + GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ g h n := by
      intro h n; simp only [GlobalTheory.MixPer.besFun, Pi.add_apply]; ring
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    simp_rw [e]
    rw [← integral_add (hout f hf) (hout g hg)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_add (hin f hf h) (hin g hg h))
  · have hνr : B.vN.ν.real B.vN.𝓝 = 1 := by simp [Measure.real, hν1]
    have h1 : ∀ h ∈ B.vA.𝓕, ‖∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν‖ ≤ Cφ * K := by
      intro h _
      have := norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK' h n
      rwa [hνr, mul_one] at this
    have h2 := norm_setIntegral_le_of_norm_le_const hμ h1
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    calc _ ≤ Cφ * K * B.vA.μ.real B.vA.𝓕 := h2
      _ = _ := by ring

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

theorem mult_mem_contLeft (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (u : M.Vec) : T u ∈ contLeft V := by
  let Q : Submodule ℂ (MMap M) :=
    { carrier := {T | ∀ u, T u ∈ contLeft V}
      add_mem' := fun ha hb u => by simpa using (contLeft V).add_mem (ha u) (hb u)
      zero_mem' := fun u => by simpa using (contLeft V).zero_mem
      smul_mem' := fun c T hT u => by simpa using (contLeft V).smul_mem c (hT u) }
  have : Mult θ M J χ ≤ Q := Submodule.span_le.2 fun T hT u => ⟨(hT.aut u).cont, (hT.aut u).left⟩
  exact this hT u

theorem mult_bound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (Ω : Set (GA D V)) (hΩ : IsCompact Ω)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g ∈ Ω, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact GlobalTheory.T.cuspFormMap_values_compact_sobolev_bound D θ V S M J χ hθ T hT Ω hΩ τ v
  | zero => exact ⟨[], 0, by simp, fun w g _ => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g hg => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g hg) (hb₂ w g hg)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g hg => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g hg) (norm_nonneg _)

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi

open SepPer in

theorem sepCont_per_rTrans : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S) (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (φ : GA D B.A → ℂ), IsInfFam θ → IsStdChar D ψ (-1) → IsContAut B.A φ → ∀ T ∈ MultT θ M J χ, ∃ Λ : SmT M →ₗ[ℂ] ℂ, SepCont M Λ ∧ ∀ x, Λ x = B.per ψ φ (rTrans t (T x)) := by
  intro D θ ψ ρ B S M J χ t φ hθ hψ hφ T hT
  obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D ρ B
  obtain ⟨Cp, hadd, hbd⟩ := per_add_bound B hψ hφ Ω hΩc hΩ
  set T' : MMap M := PiTensorProduct.lift.symm T with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  have hTt : ∀ u : M.Vec, T (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : T = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT M, T x ∈ contLeft B.V := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft B.V).smul_mem r (mult_mem_contLeft θ M J χ hT'm u)
    | add x y hx hy =>
      rw [map_add]
      exact (contLeft B.V).add_mem hx hy
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun x => B.per ψ φ (rTrans t (T x))
      map_add' := fun x y => by
        have e : rTrans t (T (x + y)) = rTrans t (T x) + rTrans t (T y) := by
          funext g; simp [rTrans]
        rw [e]
        exact hadd _ _ (rTrans_mem t (hmem x)) (rTrans_mem t (hmem y))
      map_smul' := fun c x => by
        have e : rTrans t (T (c • x)) = c • rTrans t (T x) := by
          funext g; simp [rTrans]
        have := GlobalTheory.HandHom.per_smul B ψ 1 c φ (rTrans t (T x))
        rw [one_smul, one_mul] at this
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [e, this] }
  refine ⟨Λ, fun τ v => ?_, fun x => rfl⟩
  have hΩt : IsCompact ((fun g => g * t) '' Ω) := hΩc.image (continuous_id.mul continuous_const)
  obtain ⟨L, Cu, hL, hb⟩ := mult_bound θ hθ M J χ hT'm _ hΩt τ v
  let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
    intro w
    have := congrArg (fun m => m w) hℓ
    simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
  refine ⟨ℓ, ⟨L, Cp * Cu, hL, fun w hw => ?_⟩, hℓw⟩
  have hw' : w ∈ M.sm τ := Submodule.subset_span hw
  have e := hℓw ⟨w, hw'⟩
  simp only at e
  rw [e]
  change ‖B.per ψ φ (rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))))‖ ≤ _
  have hK : ∀ x ∈ Ω, ‖rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))) x‖ ≤
      Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum := by
    intro x hx
    rw [rTrans, hTt]
    exact hb ⟨w, hw'⟩ (x * t) ⟨x, hx, rfl⟩
  calc _ ≤ Cp * (Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum) := hbd _ (rTrans_mem t (hmem _)) _ hK
    _ = _ := by ring

end GlobalTheory.Core.Mi
