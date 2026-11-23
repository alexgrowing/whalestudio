import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsConvOfInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.Mi.Shift

variable {D : D7}

theorem inner_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (γ * h) n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨-, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  set δ : GA D B.V := embA B.d B.o γ with hδdef
  have hδ : δ ∈ GQ B.V := by
    have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    rwa [one_mul] at this
  have hmem : ∀ n : flagN B.d, δ⁻¹ * n.1 * δ ∈ flagN B.d := fun n => by
    have := hconj n.1 n.2 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have hmem' : ∀ n : flagN B.d, δ * n.1 * δ⁻¹ ∈ flagN B.d := fun n => hconj n.1 n.2 γ
  let c : flagN B.d ≃ₜ* flagN B.d :=
    { toFun := fun n => ⟨δ⁻¹ * n.1 * δ, hmem n⟩
      invFun := fun n => ⟨δ * n.1 * δ⁻¹, hmem' n⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ B.V B.d.e ↔ n ∈ NFlagQ B.V B.d.e := fun n => by
    change δ⁻¹ * (n : GA D B.V) * δ ∈ GQ B.V ↔ (n : GA D B.V) ∈ GQ B.V
    rw [Subgroup.mul_mem_cancel_right _ hδ, Subgroup.mul_mem_cancel_left _ (inv_mem hδ)]
  have hK : ∀ γ' ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ' * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  refine Eq.trans ?_ (GlobalTheory.Mem.TrueRecord.integral_aut _ u1 u2 u3 c hc _ hK)
  congr 1
  funext n
  change _ = besFun ψ 1 B.d B.o B.ζ φ f h ⟨δ⁻¹ * n.1 * δ, hmem n⟩
  simp only [besFun]
  have e1 : psiBes ψ B.d 1 (vecB B.o B.ζ) (δ⁻¹ * n.1 * δ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n.1 := by
    have := hψconj n.1 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have e2 : f (δ⁻¹ * n.1 * δ * embA B.d B.o h) = f (n.1 * embA B.d B.o (γ * h)) := by
    rw [map_mul, ← hδdef, mul_assoc, mul_assoc, hf _ (inv_mem hδ)]
  rw [e1, e2, hφ γ hγ h]

theorem map_mul_right {ρ : ℕ} (B : BesLev D ρ) (a : GA D B.A) : B.vA.μ.map (· * a) = B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  obtain ⟨K, hK, hcov⟩ := B.cpt
  exact Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vA.μ (GQ B.A) hK hcov a

theorem setIntegral_mul_right {ρ : ℕ} (B : BesLev D ρ) (G : GA D B.A → ℂ) (hG : ∀ γ ∈ GQ B.A, ∀ h, G (γ * h) = G h)
    (a : GA D B.A) : ∫ h in B.vA.𝓕, G (h * a) ∂B.vA.μ = ∫ h in B.vA.𝓕, G h ∂B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  have hmp : MeasurePreserving (· * a) B.vA.μ B.vA.μ := ⟨measurable_mul_const a, map_mul_right B a⟩
  have hmp' : MeasurePreserving (· * a⁻¹) B.vA.μ B.vA.μ := ⟨measurable_mul_const a⁻¹, map_mul_right B a⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a) G B.vA.𝓕, Set.image_mul_right]
  have hF : IsFundamentalDomain (GQ B.A) ((· * a⁻¹) ⁻¹' B.vA.𝓕) B.vA.μ :=
    B.vA.fund.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (B.vA.fund.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

end GlobalTheory.Core.Mi.Shift

open GlobalTheory.Core.Mi.Shift in

theorem GlobalTheory.Core.Mi.per_rTrans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ)
    (f : GA D B.V → ℂ) (a : GA D B.A), IsStdChar D ψ (-1) → IsContAut B.A φ → IsContAut B.V f →
    B.per ψ (rTrans a φ) (rTrans (embA B.d B.o a) f) = B.per ψ φ f := by
  intro D ψ ρ B φ f a hψ hφ hf
  have hshift : ∀ h, ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ (rTrans a φ) (rTrans (embA B.d B.o a) f) h n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (h * a) n ∂B.vN.ν := fun h => by
    simp only [besFun, rTrans, map_mul, mul_assoc]
  unfold BesLev.per besPer
  simp_rw [hshift]
  exact setIntegral_mul_right B (fun h => ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν)
    (fun γ hγ h => inner_left B ψ hψ.1 φ f hφ.1 hf.1 hγ h) a

end
