import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IsScalarOneOfComm
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def HasK (E : Type) [Field E] : Prop := ∃ (x : E) (d : ℕ), 0 < d ∧ x ^ 2 = -(d : E)

structure GoodK (σ : E →ₐ[F] E) (B : Base F E) : Prop where
  cm : IsCMExt F E σ
  galois : HasK E
  unram : Algebra.Unramified (𝓞 F) (𝓞 E)
  std : IsStd B.ψ
  inert : ∀ v w, Formalism.UG.IsInertAt F E v w → (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal ∧ PsiUnr B.ψ v
  psiP : ∀ v ∈ B.P, PsiUnr B.ψ v

structure IsLatRepK (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (hc : HeisClosedF σ JS JT ξ₀ ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)) : Prop where
  hw : w + sgOF σ w = 1
  sd : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)
  span : Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} = ⊤
  fin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0
  op : ∀ p x v, Om p (opFF hc w x v) = opFF hc w (rhoFF σ JS JT p x) (Om p v)
  sd' : ∀ p, SelfDual (gamFF σ JS JT ξ₀ ψ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p))
  vac : ∀ p e, Fixes (opFF hc w) (latF F E nS nT Λ) e →
    Om p e = normOp lam (opFF hc w) (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) e
  good : GoodNorm (sgOF σ) lam
  lev : ∀ x : XFF F E nS nT, ∃ N : ℕ, 0 < N ∧ ∀ l ∈ latF F E nS nT Λ,
    ψ (symplOHF σ JS JT ξ₀ (x : WOF F E nS nT) (N • (l : WOF F E nS nT))) = 1
  near : ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ
  near' : ∀ (x : XFF F E nS nT) (N : ℕ), 0 < N → ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT),
    ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l
  splitStab : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ

structure IsKap (σ : E →ₐ[F] E) (lam : ℕ →* ℂ) (κ : (AEF F E)ˣ →* Circle) : Prop where
  cont : Continuous κ
  sq : ∀ z, κ z * κ z = 1
  base : ∀ a, κ (idFF F E a) = 1
  ker : ∀ z, (∀ Q, ¬ Fx σ Q → wv F E Q z = 1) → κ z = 1
  gen : ∀ P, ¬ Fx σ P → ∀ z, wv F E P z = WithZero.exp (-1 : ℤ) → (∀ Q, Q ≠ P → wv F E Q z = 1) →
    lam (Ideal.absNorm P.asIdeal) = (κ z : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)

def NormK : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  GoodK σ B → ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam

def KapEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam → ∃ κ, IsKap σ lam κ

def EtaProdK : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ η : (AEF F E)ˣ →* Circle, IsHeckeCharF η → ResEtaF η 1 →
    HasExp B.emb η (fun _ => 1) → UnramInert σ η → ∀ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam → ∀ κ, IsKap σ lam κ →
    ∃ ε, IsHalfF σ ε ∧ ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ ((η * κ) y : ℂ) * lam k * ∏ v, tauB B v x = r

def CardDet : Prop := ∀ (R M : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] (f : M →ₗ[R] M), Function.Injective f →
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (R ⧸ Ideal.span {LinearMap.det f})

def IdxHalf : Prop := ∀ (R X M : Type) [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] (σ : R →+* R) (w : R)
  (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M), IsHeis σ w γ W → ∀ A B : Submodule R X, SelfDual γ A → SelfDual γ B → idx A B ≠ 0 →
    ∀ e e' : X →ₗ[R] X, (∀ x, e (e x) = e x) → (∀ x, e' (e' x) = e' x) → (∀ x, e (e' x) = 0) → (∀ x, e' (e x) = 0) →
    (∀ x y, γ (e x) y = γ x (e' y)) → (∀ a ∈ A, e a ∈ A ∧ e' a ∈ A) → (∀ a ∈ B, e a ∈ B ∧ e' a ∈ B) →
    (∀ x, x - e x - e' x ∈ A ↔ x - e x - e' x ∈ B) → idx A B = idx (A.map e) (B.map e) * idx (B.map e) (A.map e)

def IdxSign : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ (ψ : AddChar (AF F) ℂ) (hc : HeisClosedF σ JS JT ξ₀ ψ) (w : 𝓞 E),
    w + sgOF σ w = 1 → ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ →
    (∀ p, SelfDual (gamFF σ JS JT ξ₀ ψ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p))) →
    (∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) →
    ∀ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam → ∀ κ, IsKap σ lam κ → ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h →
    ∀ x y, IsDetAtF σ e JS g x → IsDetAtF σ e JT h y →
      lam (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)))) =
        ((κ x ^ nT * κ y ^ nS : Circle) : ℂ) * (Real.sqrt (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℂ)

end UpperTheory.TP.W

end
