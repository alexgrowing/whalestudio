import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne

noncomputable section

namespace GlobalTheory.ThKAdm

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

variable (σ W) in

def FinPt : Set (UA σ W.J) := {g | At (fun a : AF F => a.2) (mat g - 1)}

variable (W) in

def IsLevel (L : Subgroup (UA σ W.J)) : Prop :=
  (L : Set (UA σ W.J)) ⊆ FinPt σ W ∧ ∃ U : Set (UA σ W.J), IsOpen U ∧ (1 : UA σ W.J) ∈ U ∧ U ∩ FinPt σ W ⊆ L

def IsKRep (B : Base F E) {m : ℕ} (τ : UA σ W.J → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) : Prop :=
  τ 1 = 1 ∧ (∀ k ∈ KInf σ W B.emb, ∀ k' ∈ KInf σ W B.emb, τ (k * k') = τ k * τ k') ∧
    (∀ k ∈ KInf σ W B.emb, ∀ v, ‖τ k v‖ = ‖v‖) ∧ ∀ v, ContinuousOn (fun k => τ k v) (KInf σ W B.emb)

def HasTypes (B : Base F E) (om : Rep σ Y W) {m : ℕ}
    (τ : UA σ W.J → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) (Ψ : Fn F n d) : Prop :=
  ∃ T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] Fn F n d, (∀ k ∈ KInf σ W B.emb, ∀ v, T (τ k v) = om (1, k) (T v)) ∧
    Ψ ∈ LinearMap.range T

end GlobalTheory.ThKAdm

end
