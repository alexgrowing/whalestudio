import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

theorem kfin_of_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A T : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ)) (ν : Measure (WO A T)) (𝓨 : Set (WO A T)) (μ : D.host.E) (κ : GA D (dblSp A) ≃* GlobalTheory.StdUnn.G D A.rank) (omS : GlobalTheory.StdUnn.G D A.rank →* Module.End ℂ (schwartzA θ T.rank A.rank)), Pass ψ θ A T χ om ν 𝓨 μ κ omS → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), GlobalTheory.StdUnn.IsConj A a κ p → ∀ f, IsThetaFunO ψ (dblSp A) T f → IsKFinVec om (Khat A a) f → ∀ (h : GA D T) (Φ : schwartzA θ T.rank A.rank), Φ.1 = sch ψ A T ν 𝓨 (om ((p : GA D (dblSp A))⁻¹, h) f) → KFin omS Φ := by
  intro D ψ θ A T χ om ν 𝓨 μ κ omS hP a p hC f hf hK h Φ hΦ
  have lin := fun (g g' : WO (dblSp A) T → ℂ) (hg : IsThetaFunO ψ (dblSp A) T g)
      (hg' : IsThetaFunO ψ (dblSp A) T g') (c : ℂ) =>
    GlobalTheory.StdUnn.sch_linear D ψ hP.weil.std A T ν 𝓨 hP.cov g g' hg hg' c
  set S := Submodule.span ℂ {v : WO (dblSp A) T → ℂ | ∃ k ∈ Khat A a, v = om (k, 1) f} with hSdef
  have hSth : ∀ v ∈ S, IsThetaFunO ψ (dblSp A) T v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k, -, rfl⟩ := hx; exact hP.weil.om_pres _ _ hf
    | zero => simpa using (lin f f hf hf 0).2.1
    | add x y _ _ hx hy => exact (lin x y hx hy 1).1
    | smul c x _ hx => exact (lin x x hx hx c).2.1
  let q : GA D (dblSp A) × GA D T := ((p : GA D (dblSp A))⁻¹, h)
  let L : S →ₗ[ℂ] (Mx D T.rank A.rank → ℂ) :=
    { toFun := fun v => sch ψ A T ν 𝓨 (om q v.1)
      map_add' := fun v w => by
        have hv := hP.weil.om_pres q _ (hSth v.1 v.2)
        have hw := hP.weil.om_pres q _ (hSth w.1 w.2)
        simp only [Submodule.coe_add, map_add]
        exact (lin _ _ hv hw 1).2.2.1
      map_smul' := fun c v => by
        have hv := hP.weil.om_pres q _ (hSth v.1 v.2)
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        exact (lin _ _ hv hv c).2.2.2 }
  haveI : FiniteDimensional ℂ S := hK
  have hle : Submodule.map (schwartzA θ T.rank A.rank).subtype
      (Submodule.span ℂ {Ψ : schwartzA θ T.rank A.rank | ∃ k ∈ StdUnn.K D A.rank, Ψ = omS k Φ}) ≤
      LinearMap.range L := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨Ψ, ⟨k, hk, rfl⟩, rfl⟩
    have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
      rw [hC]; simpa [mul_assoc] using hk
    refine ⟨⟨om ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹, 1) f,
      Submodule.subset_span ⟨_, hk', rfl⟩⟩, ?_⟩
    have htr := hP.trans (κ.symm k) (om q f) (hP.weil.om_pres q f hf) Φ hΦ
    rw [MulEquiv.apply_symm_apply] at htr
    show sch ψ A T ν 𝓨 (om q (om ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹, 1) f)) = (omS k Φ).1
    rw [htr, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 3
    ext <;> simp [q, mul_assoc]
  haveI : FiniteDimensional ℂ (Submodule.map (schwartzA θ T.rank A.rank).subtype
      (Submodule.span ℂ {Ψ : schwartzA θ T.rank A.rank | ∃ k ∈ StdUnn.K D A.rank, Ψ = omS k Φ})) :=
    Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm

end GlobalTheory.RegSch
