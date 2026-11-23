import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.LamStarCMulVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LocCnt0LOfTheta

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def cjT (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) O :=
  fun a b => ⟨cj (Z b a), hO _ (Z b a).2⟩

def bRaw (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y y' : Fin (r + 1) → O) : E :=
  ∑ j, cj (y' j) * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j

def lamS (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y' : Fin (r + 1) → O) : E :=
  lamStarC cj (Z.map O.subtype) (fun b => (y' b : E))

def PairSet (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : Type :=
  {p : (MbMod Z₁ ≃ₗ[O] MbMod Z₂) × (MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂)) //
    (p.1 (bCls Z₁) = bCls Z₂ ∧ p.1 (eCl Z₁) = eCl Z₂) ∧
    (∀ y' y₂' : Fin (r + 1) → O, p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      lamS O cj Z₂ y₂' = lamS O cj Z₁ y') ∧
    (∀ y y' y₂ y₂' : Fin (r + 1) → O, p.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂ →
      p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      bRaw O cj Z₂ y₂ y₂' - bRaw O cj Z₁ y y' ∈ O)}

def projP (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (p : PairSet O cj hO Z₁ Z₂) : IsoMbe Z₁ Z₂ :=
  (⟨p.1.1, p.2.1⟩ : {γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂ // γ (bCls Z₁) = bCls Z₂ ∧ γ (eCl Z₁) = eCl Z₂})

def StepPair : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (T T' : E), T ∈ O → T' ∈ O → cj T = T → cj T' = T' →
    ∀ (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    IsUnit (gramC cj (Z₁.map O.subtype) T T').det → IsUnit (gramC cj (Z₂.map O.subtype) T T').det →
    Nat.card (ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) T T') =
      Nat.card (PairSet O cj hO Z₁ Z₂)

def StepInj : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    Function.Injective (projP O cj hO Z₁ Z₂)

def StepAdj : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    Function.Surjective (projP O cj hO Z₁ Z₂)

theorem unramifiedIsoCount_of_pair_inj_adj (h1 : StepPair) (hi : StepInj) (h2 : StepAdj) : UnramifiedIsoCountZero := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hd₁ hd₂ hg₁ hg₂
  rw [h1 E O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hd₁ hd₂ hg₁ hg₂]
  exact Nat.card_congr (Equiv.ofBijective _
    ⟨hi E O cj hcj hO r Z₁ Z₂ hu₁ hu₂, h2 E O cj hcj hO r Z₁ Z₂ hu₁ hu₂ hd₁ hd₂⟩)

theorem locCnt0L_of_pair (h1 : StepPair) (hi : StepInj) (h2 : StepAdj) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  Formalism.L2.SG.LocalCountModules.LocCnt0LWork.locCnt0L_of_alg (unramifiedIsoCount_of_pair_inj_adj h1 hi h2)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
