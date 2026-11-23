import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitFrameReps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pre_mul_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    Formalism.IndefR.principalLevelFrame.pre Ψ (Ψ.ψ x) = x :=
  Ψ.inj (Formalism.IndefR.principalLevelFrame.pre_spec Ψ (Ψ.into x))

theorem frame_reps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := by
  intro D V n hF Ψ hΨ Pp hS d hd
  obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D Pp (GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS)
  have hv : Formalism.L2.NG.OverPl Pp s.v := by rw [← hs]; exact s.w_under
  have hrep : GlobalTheory.Hk3.rep V Pp d = hd.choose := by unfold GlobalTheory.Hk3.rep; rw [dif_pos hd]
  obtain ⟨e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hRs, hR⟩ := hd.choose_spec
  rw [hrep]
  have hK : ∀ k, k ∈ GlobalTheory.HeckeScalarSph.locK n s.v ↔
      Ψ.ψ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} :=
    fun k => and_congr (hΨ.2 k) (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv k).symm
  have h1 : (1 : Formalism.L2.Theta.GA D V) ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
    have := (hK 1).1 (one_mem _)
    rwa [map_one] at this
  have hαG : α ∈ Formalism.L2.Theta.GfC V := by
    obtain ⟨γ, ⟨hγ, hx⟩, -⟩ := hR.2 α ⟨1, h1, 1, h1, by rw [one_mul, mul_one]⟩
    have := mul_mem (hR.1 γ hγ).1 hx.1.1
    rwa [mul_inv_cancel_left] at this
  obtain ⟨a, rfl⟩ := Ψ.onto α hαG
  have hpull : ∀ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k},
      ∃ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Ψ.ψ κ = k := by
    intro k hk
    obtain ⟨κ, rfl⟩ := Ψ.onto k hk.1.1
    exact ⟨κ, (hK κ).2 hk, rfl⟩
  refine ⟨s, a, hv, (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨-, k₁, hk₁, k₂, hk₂, eγ⟩ := hR.1 γ hγ
    obtain ⟨κ₁, hκ₁, rfl⟩ := hpull k₁ hk₁
    obtain ⟨κ₂, hκ₂, rfl⟩ := hpull k₂ hk₂
    refine ⟨κ₁, hκ₁, κ₂, hκ₂, ?_⟩
    rw [eγ, ← map_mul, ← map_mul, pre_mul_eq]
  · rintro x ⟨κ₁, hκ₁, κ₂, hκ₂, rfl⟩
    obtain ⟨γ, ⟨hγ, hγx⟩, hu⟩ := hR.2 (Ψ.ψ (κ₁ * a * κ₂)) ⟨Ψ.ψ κ₁, (hK _).1 hκ₁, Ψ.ψ κ₂, (hK _).1 hκ₂, by rw [map_mul, map_mul]⟩
    have hγG : γ ∈ Formalism.L2.Theta.GfC V := (hR.1 γ hγ).1
    have eγ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ γ) = γ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hγG
    refine ⟨γ, ⟨hγ, ?_⟩, ?_⟩
    · have : Ψ.ψ ((Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * (κ₁ * a * κ₂)) ∈
          {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
        rw [map_mul, map_inv, eγ]; exact hγx
      exact ((hK _).2 this).1
    · rintro δ ⟨hδ, hδx⟩
      refine hu δ ⟨hδ, ?_⟩
      have hδG : δ ∈ Formalism.L2.Theta.GfC V := (hR.1 δ hδ).1
      have eδ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ δ) = δ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hδG
      have hδT : TrivOutside {s.v} (Formalism.IndefR.principalLevelFrame.pre Ψ δ) := by
        refine (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv _).1 ?_
        rw [eδ]; exact hRs δ hδ
      have hT : TrivOutside {s.v} ((Formalism.IndefR.principalLevelFrame.pre Ψ δ)⁻¹ * (κ₁ * a * κ₂)) :=
        GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hδT)
          (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul hκ₁.2
            ((GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα)) hκ₂.2)
      have := (hK _).1 ⟨hδx, hT⟩
      rwa [map_mul, map_inv, eδ] at this

end GlobalTheory.SplitFrameReps
