import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.SafeUGap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix

namespace UpperTheory.V.Af

section admitted

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def AttR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) : Prop :=
  AttachedSys ι r π.HasSat

def IsAutR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : TR.CuspSub F n, π.IsRegAlg ∧ AttR ι r π

def DualTw {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin n) k) (θ : Γ →* kˣ) : Prop :=
  ∃ P : GL (Fin n) k, ∀ s, (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) =
    (θ s : k) • (P : Matrix (Fin n) (Fin n) k)

omit [NumberField F] in
variable (l) in

def IsCycWt (wt : ℤ) (θ : G F Ω →* (Qbar l)ˣ) : Prop :=
  ∃ (M : ℕ) (χ : G F Ω →* (Qbar l)ˣ), 1 ≤ M ∧ KillsMu M χ ∧ θ = cycBar F Ω l ^ wt * χ

variable (l) in

structure LevelO (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop extends Level l M m r where
  odd : Odd n

structure AdmK [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutCsd ι r
  level : LevelO l M m r

structure AdmR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutQ ι r
  level : Level l M m r
  dual : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ
  safe : Keep.SafeU l M m r

end admitted

structure EigData (n q : ℕ) (m : Fin n → ℤ) (wt : ℤ) where

  S : Type
  fin : Finite S

  β : S → Multiset ℂ
  card : ∀ s, (β s).card = n
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, β (e s) = (β s).map σ
  pure : ∀ s, ∀ b ∈ β s, ‖b‖ = (q : ℝ) ^ ((wt : ℝ) / 2)
  int : ∀ a : ℤ, (∀ i, -a ≤ m i) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b)
  intInv : ∀ a : ℤ, (∀ i, m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)

instance {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} : Inhabited (EigData n q m wt) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim,
    fun _ _ s => s.elim, fun _ _ s => s.elim⟩⟩

def EigData.Classifies {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n q : ℕ}
    {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F))
    (admitted : (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, FrobEig ι r.1 w ((D.β (cl r)).map (·⁻¹))

def CountK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmK ι M m)

def CountQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal → ¬ p ∣ M →
      ∃ D : EigData n p m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmR ι M m wt)

def NewformAutR : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutR ι W

def NewformAut : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutQ ι W

section U3

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime]

structure Adm3 [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : IsAutCsd ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ

def Adm2 (ι : Qbar l ≃+* ℂ) (e M : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop :=
  ∃ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W ∧ (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧
    Level l M ![(e : ℤ), -(e : ℤ)] W ∧ IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω, ((g * ρ s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
      !![W (s.restrictScalars ℚ) 0 0, 0, W (s.restrictScalars ℚ) 0 1; 0, 1, 0;
         W (s.restrictScalars ℚ) 1 0, 0, W (s.restrictScalars ℚ) 1 1]

end U3

def eis3 (q e : ℕ) (z : ℂ) : ℂ := ((q : ℂ) ^ e)⁻¹ * z + 1 + (q : ℂ) ^ e * z⁻¹

def eis4 (p e : ℕ) (z₁ z₂ z₃ : ℂ) : ℂ := (p : ℂ) ^ (e + 1) * z₁ + (p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1

def CongruenceNumberRankThree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∃ c A : ℕ,
    ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → 7 ≤ p →
      ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K →
    ∀ (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) →
      (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Fintype.card Orb * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
        [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w →
        ∀ σ : G K Ω, IsFrob B (normV w) σ →
        ∀ X : Orb → Finset (G K Ω →* GL (Fin 3) (Qbar l)),
          (∀ o, ∀ ρ ∈ X o, Adm3 ι e N ρ ∨ Adm2 ι e (N * (discr K).natAbs) ρ) →
          (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') →
          (∀ o, ∀ ρ ∈ X o, (ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 (normV w) e (z o))) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤
            ∏ o, ∏ ρ ∈ X o, ‖(ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 (normV w) e (z o))‖

def NumberSp4 : Prop :=
  ∃ c A : ℕ, ∀ e : ℕ, 2 ≤ e → ∀ M : ℕ, 1 ≤ M → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal →
    5 ≤ p → ¬ p ∣ M → ∀ k : ℕ, 0 < k → ∀ z₁ z₂ z₃ : ℂ, z₁ ^ k = 1 → z₂ ^ k = 1 → z₃ ^ k = 1 →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Nat.totient k * ((M : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
        (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G ℚ Ω, IsFrob B p σ →
        ∀ X : Finset (G ℚ Ω →* GL (Fin 4) (Qbar l)),
          (∀ r ∈ X, AdmR ι M ![(e : ℤ) + 1, e, 1, 0] (e + 1) r) → (∀ r ∈ X, ∀ r' ∈ X, RepIso r r' → r = r') →
          (∀ r ∈ X, (r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace ≠ ι.symm (eis4 p e z₁ z₂ z₃)) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ r ∈ X, ‖(r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace - ι.symm (eis4 p e z₁ z₂ z₃)‖

section Ad

variable {F₀ F Ω : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω]
  {k : Type} [Field k] {n : ℕ}

def IsAdOf (r : G F Ω →* GL (Fin n) k) (μ : G F Ω →* kˣ) (ρ : Representation k (G F₀ Ω) (Matrix (Fin n) (Fin n) k)) : Prop :=
  ∃ (c : G F₀ Ω) (P : GL (Fin n) k), (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) ∧
    (∀ s s' : G F Ω, s'.restrictScalars F₀ = c * s.restrictScalars F₀ * c⁻¹ →
      (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s' : Matrix (Fin n) (Fin n) k) =
        (μ s : k) • (P : Matrix (Fin n) (Fin n) k)) ∧
    (∀ (s : G F Ω) (X : Matrix (Fin n) (Fin n) k), ρ (s.restrictScalars F₀) X =
      (r s : Matrix (Fin n) (Fin n) k) * X * ((r s)⁻¹ : GL (Fin n) k)) ∧
    ∀ X : Matrix (Fin n) (Fin n) k, ρ c X = -((P⁻¹ : GL (Fin n) k) * Xᵀ * (P : Matrix (Fin n) (Fin n) k))

end Ad

def AdVanishK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)), Continuous r → IsAutCsd ι r →
      IsIrr (r.comp (cycBar K Ω l).ker.subtype) →
      ∀ ρ : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l)),
        IsAdOf r (cycBar K Ω l ^ (1 - (n : ℤ))) ρ → BlochKatoSelmerVanishes l ρ

def AdVanishQ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ), Continuous r → IsAutQ ι r →
      IsCycWt l wt θ → DualTw r θ →
      IsIrr ((r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).comp (cycBar K Ω l).ker.subtype) →
      ∀ ρ : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l)),
        IsAdOf (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (θ.comp (AlgEquiv.restrictScalarsHom ℚ)) ρ →
        BlochKatoSelmerVanishes l ρ

end UpperTheory.V.Af
