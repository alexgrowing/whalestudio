import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoxInvariantSnd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTraceEq
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.ConjugationInvariantDistributions.TheoremA

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev Mx (n : ℕ) : Type := Matrix (Fin (n + 1)) (Fin (n + 1)) k

abbrev Vc (n : ℕ) : Type := Fin (n + 1) → k

variable {k}

def cj {n : ℕ} (g : GL (Fin (n + 1)) k) (x : Mx k n) : Mx k n :=
  (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * x * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)

def PInvX {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) : Prop := ∀ p ∈ Mir k n, ∀ f ∈ SB (Mx k n), Λ (f ∘ cj p) = Λ f

def GInvX {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) : Prop := ∀ g : GL (Fin (n + 1)) k, ∀ f ∈ SB (Mx k n), Λ (f ∘ cj g) = Λ f

open Classical in

def sec {n : ℕ} (w : Vc k n) : GL (Fin (n + 1)) k :=
  if h : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j then h.choose else 1

open Classical in

def phi {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) (F : Mx k n × Vc k n → ℂ) (w : Vc k n) : ℂ :=
  if w = 0 then 0 else Λ (fun x => F (cj (sec w)⁻¹ x, w))

def lt [MeasurableSpace k] (ν : Measure k) {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) (F : Mx k n × Vc k n → ℂ) : ℂ :=
  ∫ w, phi Λ F w ∂(Measure.pi fun _ => ν)

variable (k)

def SecSpec : Prop := ∀ (n : ℕ) (w : Vc k n), w ≠ 0 → ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j

def PhiIndep : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), ∀ w : Vc k n, w ≠ 0 →
  ∀ s : GL (Fin (n + 1)) k, (∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j) →
    phi Λ F w = Λ (fun x => F (cj s⁻¹ x, w))

def PhiLin : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), ∀ F ∈ SB (Mx k n × Vc k n), ∀ G ∈ SB (Mx k n × Vc k n),
  ∀ a b : ℂ, phi Λ (a • F + b • G) = a • phi Λ F + b • phi Λ G

def PhiEquiv : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), ∀ h : GL (Fin (n + 1)) k,
  ∀ w : Vc k n, phi Λ (fun q => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) w =
    phi Λ F ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w)

def PhiInt : Prop := ∀ [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : ℕ)
  (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), Integrable (phi Λ F) (Measure.pi fun _ => ν)

def eN (n : ℕ) : Vc k n := Pi.single (Fin.last n) 1

def PhiNear : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ f₀ ∈ SB (Mx k n), ∃ t : kˣ, ∀ s : kˣ,
  box (Fin (n + 1)) s ⊆ box (Fin (n + 1)) t →
    phi Λ (fun q => f₀ q.1 * ({w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s}.indicator 1 q.2)) =
      {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s}.indicator fun _ => Λ f₀

def PfAct : Prop := ∀ [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ),
  HasConductor ψ c → ∀ (n : ℕ) (F : Mx k n × Vc k n → ℂ), F ∈ SB (Mx k n × Vc k n) → ∀ h : GL (Fin (n + 1)) k,
    GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) =
      fun z => (((nabs k (GeneralLinearGroup.det h))⁻¹ : ℝ) : ℂ) * GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) F
        (cj h⁻¹ z.1, ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z.2)

def LtEquiv : Prop := ∀ [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : ℕ)
  (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), ∀ h : GL (Fin (n + 1)) k,
    lt ν Λ (fun q => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) =
      (((nabs k (GeneralLinearGroup.det h))⁻¹ : ℝ) : ℂ) * lt ν Λ F

def Recover : Prop := ThmT k → ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ →
  ∃ L : (Mx k n → ℂ) →ₗ[ℂ] ℂ, GInvX L ∧ ∀ f ∈ SB (Mx k n), Λ f = L f

def CoreX : Prop := ThmT k → ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → GInvX Λ

end PositivityTheory.RgUd.AB
