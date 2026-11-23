import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf

noncomputable section

open GlobalTheory.KZ GlobalTheory.K4 Polynomial

namespace UpperTheory.V.Z.Kato.Sym.PE

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def pj (X : Tower Ω ε) : Polynomial Ω →+* Kb X := (io X).comp (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom

def InU (X : Tower Ω ε) (u v : X.K) (σ : RingAut (Kb X)) : Prop :=
  (∀ c : Ω, σ (io X (algebraMap Ω X.K c)) = io X (algebraMap Ω X.K c)) ∧ σ (io X X.jK) = io X X.jK ∧
    σ (io X u) = io X u ∧ σ (io X v) = io X v

def Alg : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∃ φ : RatFunc Ω →+* Kb X,
    (∀ p : Polynomial Ω, φ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = pj X p) ∧ @Algebra.IsAlgebraic (RatFunc Ω) (Kb X) _ _ φ.toAlgebra

def Integ : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m →
    ∀ (u : X.K) (z : Kb X), IsU X u → z ^ m = io X u → z ≠ 0 ∧ (pj X).IsIntegralElem z ∧ (pj X).IsIntegralElem z⁻¹

def LcFin : Prop :=
  ∀ (F E A : Type) [Field F] [Field E] [Algebra F E] [IsGalois F E] (U : Subgroup (E ≃ₐ[F] E)), IsOpen (U : Set (E ≃ₐ[F] E)) →
    ∀ η : (E ≃ₐ[F] E) → A, IsLocallyConstant (fun g : U => η g) →
      ∃ B : Finset E, ∀ h ∈ U, ∀ h' ∈ U, (∀ b ∈ B, h b = h' b) → η h = η h'

def KaU : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m →
    ∀ θ : Kb X, θ ≠ 0 → ∀ g h : RingAut (Kb X), g (zt X m) = zt X m → h (zt X m) = zt X m → g (θ ^ m) = θ ^ m → h (θ ^ m) = θ ^ m →
      ka X m θ (g * h) = ka X m θ g + ka X m θ h ∧ ka X m (g θ) h = ka X m θ h ∧ ka X m θ (g⁻¹ * h * g) = ka X m θ h

def EtaEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m →
    ∀ (u v : X.K) (a b : Kb X), IsU X u → IsU X v → a ^ m = io X u → b ^ m = io X v →
      ∃ η : RingAut (Kb X) → ZMod m,
        (∀ g h, InU X u v g → InU X u v h → ka X m a g * ka X m b h = η h - η (g * h) + η g) ∧ LC X η ∧ Unr X η

end UpperTheory.V.Z.Kato.Sym.PE

end
