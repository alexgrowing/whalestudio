import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem reads_linear_injective_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx f f' φ φ' hf hf'
  obtain ⟨-, -, hlin⟩ := thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hS hev x hx φ hf.1
  obtain ⟨hl, hinj⟩ := hlin φ' hf'.1
  obtain ⟨-, -, -, -, hp⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x
  obtain ⟨p, -, hp, -⟩ := hp hx
  refine ⟨fun a b => ⟨(hl a b).1, fun w hw => ?_⟩, fun h => hinj ?_, fun h h' e => ?_⟩
  · rw [(hl a b).2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.2 w hw, hf'.2 w hw]
    ring
  · funext z
    have h1 := hf.2 (p z) (hp z).1
    have h2 := hf'.2 (p z) (hp z).1
    rw [h, h2, (hp z).2] at h1
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) h1).symm
  · refine theta_eq_of_real D ψ V W hψ f f' h h' fun w hw => ?_
    rw [hf.2 w hw, hf'.2 w hw, e]

theorem IsONFr.mem_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}
    (hx : IsONFr X x) : x ∈ X.dom :=
  PIW.FdPA.orthonormal_domain r X x hx

theorem reads_linear_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx
  exact reads_linear_injective_dom D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx.mem_dom

end GlobalTheory.AdTh
