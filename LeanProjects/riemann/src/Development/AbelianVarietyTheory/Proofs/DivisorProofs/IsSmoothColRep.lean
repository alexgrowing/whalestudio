import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.RowOneCell

def sz (u v : ℕ) (i j : Bool) : ℕ := cond i (cond j v 1) (cond j u 0)

def sigTwo (b : Bool → ℕ) (x y : ℕ) (h0 : b false = x) (h1 : b true = y) :
    (Σ j, Fin (b j)) ≃ Σ j, Two (Fin x) (Fin y) j :=
  Equiv.sigmaCongrRight fun j => match j with
    | false => finCongr h0
    | true => finCongr h1

def rowPart (u v : ℕ) : ∀ i, (Σ j, Fin (sz u v i j)) ≃ Two (Fin u) (Fin (v + 1)) i
  | false => (sigTwo (sz u v false) 0 u rfl rfl).trans (two (stdSum (Nat.zero_add u)))
  | true => (sigTwo (sz u v true) 1 v rfl rfl).trans (two (stdSum (Nat.add_comm 1 v)))

def colPart (u v : ℕ) : ∀ j, (Σ i, Fin (sz u v i j)) ≃ Two (Fin 1) (Fin (u + v)) j
  | false => (sigTwo (fun i => sz u v i false) 0 1 rfl rfl).trans (two (stdSum (Nat.zero_add 1)))
  | true => (sigTwo (fun i => sz u v i true) u v rfl rfl).trans (two (stdSum rfl))

theorem eq_sz {u v : ℕ} (b : Bool → Bool → ℕ)
    (hb : (∀ i, ∑ j, b i j = Fintype.card (Two (Fin u) (Fin (v + 1)) i)) ∧
      ∀ j, ∑ i, b i j = Fintype.card (Two (Fin 1) (Fin (u + v)) j)) (h : b true false = 1) :
    b = sz u v := by
  have r0 := hb.1 false
  have r1 := hb.1 true
  have c0 := hb.2 false
  have c1 := hb.2 true
  simp only [Fintype.sum_bool] at r0 r1 c0 c1
  have e0 : Fintype.card (Two (Fin u) (Fin (v + 1)) false) = u := Fintype.card_fin u
  have e1 : Fintype.card (Two (Fin u) (Fin (v + 1)) true) = v + 1 := Fintype.card_fin _
  have e2 : Fintype.card (Two (Fin 1) (Fin (u + v)) false) = 1 := Fintype.card_fin _
  have e3 : Fintype.card (Two (Fin 1) (Fin (u + v)) true) = u + v := Fintype.card_fin _
  rw [e0] at r0
  rw [e1] at r1
  rw [e2] at c0
  rw [e3] at c1
  funext i j
  cases i <;> cases j <;> simp only [sz, cond_true, cond_false] <;> omega

def extTensorEquiv {G H V W V' W' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W} {ρ' : Representation ℂ G V'}
    {σ' : Representation ℂ H W'} (φ : ρ.Equiv ρ') (ψ : σ.Equiv σ') :
    (extTensor ρ σ).Equiv (extTensor ρ' σ') :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (ψ.toIntertwiningMap.isIntertwining _ _ g.2 w)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def colChar (v : ℕ) (χ₂ : kˣ →* ℂˣ) (j : Bool) : kˣ →* ℂˣ :=
  χ₂ * absPow k (cond j (1 / 2) (-(v : ℂ) / 2))

def colRep (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (j : Bool) :
    Representation ℂ (Levi k fun i => Fin (sz u v i j)) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin (sz u v false j)) χ₁) (detRep (Fin (sz u v true j)) (colChar v χ₂ j))).comp
    ((Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) false).prod
      (Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) true))

theorem isSmooth_colRep {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) (u v : ℕ) (j : Bool) :
    IsSmooth (colRep χ₁ χ₂ u v j) := by
  refine isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
    ((isSmooth_ofChar_iff _).2 (h₂.mul (GlobalTheory.LocGL.isSmoothChar_absPow _)).detChar)) _ ?_
  exact (continuous_apply false).prodMk (continuous_apply true)

end GlobalTheory.SmGL.RowOneCell
