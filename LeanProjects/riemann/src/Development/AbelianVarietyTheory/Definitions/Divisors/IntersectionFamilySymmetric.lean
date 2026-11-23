import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

noncomputable section
open ValuativeRel Matrix Polynomial
open scoped Classical

namespace GlobalTheory.DZA

def KO (k : Type) [Field k] [ValuativeRel k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map (algebraMap 𝒪[k] k)).range

def K1 {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map rd).ker.map (GeneralLinearGroup.map (algebraMap 𝒪[k] k))

def infl {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (x : GL (Fin n) k) : ℂ :=
  if h : ∃ y : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) y = x then
    fb (GeneralLinearGroup.map rd h.choose) else 0

def IsFinNorm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (γ : GL (Fin n) F) : Prop :=
  IsConj (GlobalTheory.LBC.incl F' n γ) (GlobalTheory.LBC.norm F s δ)

def normLift {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') : ℂ :=
  if h : ∃ γ, IsFinNorm s δ γ then fb h.choose else 0

def InflMatching : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K],
    Continuous (algebraMap k K) → CharZero k →
    ∀ (F F' : Type) [Field F] [Fintype F] [Field F'] [Fintype F'] [Algebra F F'],
      Module.finrank F F' = Module.finrank k K →
    ∀ (rk : 𝒪[k] →+* F) (rK : 𝒪[K] →+* F'), Function.Surjective rk → Function.Surjective rK →
      (∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x → rK y = algebraMap F F' (rk x)) →
    ∀ (s : K ≃ₐ[k] K) (sb : F' ≃ₐ[F] F'),
      (∀ x y : 𝒪[K], (y : K) = s x → rK y = sb (rK x)) →
      (∀ z : F', sb z = z ^ Fintype.card F) →
    ∀ (n : ℕ) (fb : GL (Fin n) F → ℂ), (∀ a b, fb (b⁻¹ * a * b) = fb a) →
      (∀ δ : GL (Fin n) K, (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly →
          GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct s n) (KO K n) δ (infl rK (normLift sb fb)) =
            GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb)) ∧
      (∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb) ≠ 0 →
          ∃ δ : GL (Fin n) K, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly)

end GlobalTheory.DZA
