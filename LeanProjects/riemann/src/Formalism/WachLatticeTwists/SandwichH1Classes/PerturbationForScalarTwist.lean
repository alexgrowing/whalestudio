import Formalism.WachLatticeTwists.SandwichH1Classes.HypothesisWGivesUnitCongruence

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

def aR (ℓ s e : ℕ) : ℕ := s + s * e + padicValNat ℓ e.factorial

def bR (ℓ s e : ℕ) : ℕ := if e = 0 then s - 1 else (e + 1) * (s - 1) + s + padicValNat ℓ e

def RVal {ℓ : ℕ} [Fact ℓ.Prime] (D : TBData ℓ) (s e : ℕ) {Os : Type} [AddCommGroup Os] [Module ℤ_[ℓ] Os]
    (cupL : Os →ₗ[ℤ_[ℓ]] D.HB) : Prop :=
  ∀ y : Os, ∃ z : D.HW, ((ℓ : ℤ_[ℓ]) ^ aR ℓ s e) • D.ex (D.jW z) = ((ℓ : ℤ_[ℓ]) ^ bR ℓ s e) • cupL y

def StatBetaAB : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ s e : ℕ, 1 ≤ s → (bR ℓ s e : ℤ) - aR ℓ s e = beta ℓ s e

def StatRecip : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (D : TBData ℓ) (s e : ℕ) (Os : Type) [AddCommGroup Os] [Module ℤ_[ℓ] Os]
    (cupL : Os →ₗ[ℤ_[ℓ]] D.HB), 1 ≤ s → (∀ x : D.HB, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →
    D.La0 = LinearMap.range cupL → RVal D s e cupL → D.Recip (beta ℓ s e)

def StatValE : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (D : TBData ℓ) (u : ℤ_[ℓ]ˣ) (s e : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → 1 ≤ e →
    ∀ (Os : Type) [AddCommGroup Os] [Module ℤ_[ℓ] Os] (cupL : Os →ₗ[ℤ_[ℓ]] D.HB)
      (abelian₂ : Type) [AddCommGroup abelian₂] [Module ℤ_[ℓ] abelian₂] (L : ℕ → Type)
      [∀ j, AddCommGroup (L j)] [∀ j, Module ℤ_[ℓ] (L j)] (V : ∀ j, abelian₂ →ₗ[ℤ_[ℓ]] L j)
      (β : ∀ j, L j ≃ₗ[ℤ_[ℓ]] L j) (inc : ∀ j, L j →ₗ[ℤ_[ℓ]] Os),
    (∀ y : Os, ∃ ω : ∀ j, L j, y = ∑ j ∈ Finset.Icc 1 s, inc j (ω j)) →
    (∀ t : ∀ j, L j, ∃ la : abelian₂, V 1 la = ((ℓ : ℤ_[ℓ]) ^ (s - 1)) • t 1 ∧
      ∀ j, 2 ≤ j → j ≤ s → V j la = ((ℓ : ℤ_[ℓ]) ^ (s - j + 1)) • t j) →
    (∀ la : abelian₂, ∃ z : D.HW, ((ℓ : ℤ_[ℓ]) ^ aR ℓ s e) • D.ex (D.jW z) =
      cupL (∑ j ∈ Finset.Icc 1 s, inc j ((((u ^ e : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) •
        (((ℓ : ℤ_[ℓ]) ^ (e * (s - j))) • β j (V j la))))) →
    RVal D s e cupL

def TraceShiftDecomposition : Prop :=
  ∀ (ℓ : ℕ) (O1 : Type) [AddCommGroup O1] (W0 : AddSubgroup O1) (σ : O1 ≃+ O1) (Tr : O1 →+ O1),
    (∀ c ∈ W0, σ c ∈ W0) → (∀ y, Tr y ∈ W0) → (∀ y, Tr (σ y) = σ (Tr y)) →
    (∀ c ∈ W0, Tr c + c = ℓ • c) → (∀ c ∈ W0, ∃ c' ∈ W0, ℓ • σ c' - c' = c) →
    ∀ ω : O1, ∃ c0 ∈ W0, ∃ v1 : O1, c0 - σ c0 = -Tr v1 ∧ σ.symm v1 + c0 = ω

def StatKerExp : Prop :=
  ∀ (F : Type) [Field F] (HV Tg : Type) [AddCommGroup HV] [Module F HV] [AddCommGroup Tg] [Module F Tg]
    [FiniteDimensional F HV] [FiniteDimensional F Tg] (ex : HV →ₗ[F] Tg) (Hf : Submodule F HV) (δ : ℕ)
    (S : Set Tg) (c : F), c ≠ 0 → Submodule.span F S = ⊤ → (∀ y ∈ S, ∃ z, ex z = c • y) →
    Module.finrank F HV = Module.finrank F Tg + δ →
    (∃ Lu : Submodule F HV, Lu ≤ Hf ∧ Lu ≤ LinearMap.ker ex ∧ Module.finrank F Lu = δ) →
    ∀ z, ex z = 0 → z ∈ Hf

def ClassOfWZeroInH1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type) [AddCommGroup M] [Module ℤ_[ℓ] M] [TopologicalSpace M] [T2Space M] [ContinuousAdd M]
    [ContinuousSMul ℤ_[ℓ] M]
    (MB : Type) [AddCommGroup MB] [Module ℤ_[ℓ] MB] [TopologicalSpace MB] [ContinuousAdd MB]
    [ContinuousSMul ℤ_[ℓ] MB]
    (a : Representation ℤ_[ℓ] G M) (aB : Representation ℤ_[ℓ] G MB) (F : EqMap a aB)
    (H : Subgroup G) (γ : G) (lg : G → ℤ_[ℓ]) (ε : ℤ_[ℓ]ˣ) (s N : ℕ) (La : Submodule ℤ_[ℓ] MB) (c : Z1 a),
    Continuous lg → (∀ g h, lg (g * h) = lg g + lg h) → (∀ h ∈ H, lg h = 0) →
    (∀ S : Subgroup G, IsClosed (S : Set G) → H ≤ S → γ ∈ S → S = ⊤) →
    lg γ = (ε : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ s →
    (∀ g, a g (c.1 γ) = c.1 γ) → (∀ h ∈ H, c.1 h = 0) → ((ℓ : ℤ_[ℓ]) ^ N) • F.f (c.1 γ) ∈ La →
    ∃ y ∈ La, ∃ c' : Z1 aB, (∀ σ, c'.1 σ = lg σ • y) ∧
      ((ℓ : ℤ_[ℓ]) ^ (s + N)) • F.onH (H1.mk a c) = H1.mk aB c'

def PerturbationForScalarTwist : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (Tt : TateTr ℓ) (r : ℕ) (z z' ϖ : Tt.Om) (u : ℤ_[ℓ]ˣ) (j : ℤ),
    z * z' = algebraMap ℤ_[ℓ] Tt.Om (ℓ : ℤ_[ℓ]) →
    IsAdicComplete (Ideal.span {ϖ}) (Fin r → Tt.Xm) → Tt.T2 z →
    z * ϖ ∣ algebraMap ℤ_[ℓ] Tt.Om ((u : ℤ_[ℓ]) - 1) →
    (∀ v, Tt.gXI (1 : Matrix (Fin r) (Fin r) Tt.Om) u j v = v → v = 0) ∧
    ∀ v, ∃ y, (ℓ : ℤ_[ℓ]) • v = Tt.gXI (1 : Matrix (Fin r) (Fin r) Tt.Om) u j y - y

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
