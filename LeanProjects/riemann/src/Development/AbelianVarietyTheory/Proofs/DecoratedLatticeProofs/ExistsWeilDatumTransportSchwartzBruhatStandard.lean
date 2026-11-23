import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

section Model

variable {X Y G H : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [Monoid G] [Monoid H]

theorem exists_hom_of_model (P : X → Prop) (s : X → Y) (S : Submodule ℂ Y)
    (hadd : ∀ f f', P f → P f' → P (f + f') ∧ s (f + f') = s f + s f')
    (hsmul : ∀ (c : ℂ) f, P f → P (c • f) ∧ s (c • f) = c • s f)
    (hin : ∀ f, P f → s f ∈ S) (honto : ∀ φ ∈ S, ∃ f, P f ∧ s f = φ)
    (hinj : ∀ f f', P f → P f' → s f = s f' → f = f')
    (om : G →* Module.End ℂ X) (hpres : ∀ g f, P f → P (om g f)) (κ : G ≃* H) :
    ∃ ρ : H →* Module.End ℂ S, ∀ g f, P f → ∀ Φ : S, Φ.1 = s f → (ρ (κ g) Φ).1 = s (om g f) := by
  classical
  choose lift hlP hls using fun Φ : S => honto Φ.1 Φ.2
  have hlift : ∀ (Φ : S) f, P f → Φ.1 = s f → lift Φ = f := fun Φ f hf h =>
    hinj _ _ (hlP Φ) hf ((hls Φ).trans h)
  let act : H → Module.End ℂ S := fun h =>
    { toFun := fun Φ => ⟨s (om (κ.symm h) (lift Φ)), hin _ (hpres _ _ (hlP Φ))⟩
      map_add' := fun Φ Ψ => by
        have e : lift (Φ + Ψ) = lift Φ + lift Ψ :=
          hlift _ _ (hadd _ _ (hlP Φ) (hlP Ψ)).1 (by rw [(hadd _ _ (hlP Φ) (hlP Ψ)).2, hls, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [e, map_add]
        exact (hadd _ _ (hpres _ _ (hlP Φ)) (hpres _ _ (hlP Ψ))).2
      map_smul' := fun c Φ => by
        have e : lift (c • Φ) = c • lift Φ :=
          hlift _ _ (hsmul c _ (hlP Φ)).1 (by rw [(hsmul c _ (hlP Φ)).2, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [e, map_smul]
        exact (hsmul c _ (hpres _ _ (hlP Φ))).2 }
  have hact : ∀ h (Φ : S), ((act h Φ : S) : Y) = s (om (κ.symm h) (lift Φ)) := fun _ _ => rfl
  refine ⟨{ toFun := act, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [hact, map_one, map_one]
    exact hls Φ
  · intro h₁ h₂
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [Module.End.mul_apply, hact, hact, map_mul, map_mul, Module.End.mul_apply,
      hlift (act h₂ Φ) _ (hpres _ _ (hlP Φ)) (hact h₂ Φ)]
  · intro g f hf Φ hΦ
    show s (om (κ.symm (κ g)) (lift Φ)) = s (om g f)
    rw [κ.symm_apply_apply, hlift Φ f hf hΦ]

end Model

theorem exists_transport_std : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, ∃ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ κ
  have hS := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hW.std θ hθ A B ν 𝓨 hν
  have hL := GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hW.std A B ν 𝓨 hν
  obtain ⟨ρ, hρ⟩ := exists_hom_of_model (IsThetaFunO ψ (dblSp A) B) (sch ψ A B ν 𝓨) (schwartzA θ B.rank A.rank)
    (fun f f' hf hf' => ⟨(hL f f' hf hf' 0).1, (hL f f' hf hf' 0).2.2.1⟩)
    (fun c f hf => ⟨(hL f f hf hf c).2.1, (hL f f hf hf c).2.2.2⟩)
    hS.1 hS.2.1 hS.2.2 (omh.comp (MonoidHom.inl _ _)) (fun g f hf => hW.om_pres _ _ hf) κ
  exact ⟨ρ, fun g f hf Φ hΦ => hρ g f hf Φ hΦ⟩

end GlobalTheory.StdUnn

end
