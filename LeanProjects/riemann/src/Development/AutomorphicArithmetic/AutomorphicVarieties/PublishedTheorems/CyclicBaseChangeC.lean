import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af

namespace UpperTheory.V.Published

def HidaGal : Prop :=
  ∀ (k N : ℕ) [NeZero N], 2 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Sd.Eigenform k N χ) (l : ℕ) [Fact l.Prime]
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
    ∃ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ ∧ IsIrr ρ ∧
      ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), IsPlaceOver A w →
        (¬ normV w ∣ l * N → (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV w) σ →
          (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom =
            X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))) ∧
        (normV w = l → ‖ι.symm (g.a l)‖ = 1 → ∃ κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ, IsFlagOn ρ (Dec (F := ℚ) A) κ ∧
          (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 1 s = 1) ∧
          ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A l (σ : G ℚ Ω) → ‖(κ 1 σ : Qbar l)‖ = 1 ∧
            ι (κ 1 σ) ^ 2 - g.a l * ι (κ 1 σ) + χ (l : ZMod N) * (l : ℂ) ^ (k - 1) = 0) ∧
        (normV w ≠ l → normV w ∣ N → χ.conductor.factorization (normV w) = N.factorization (normV w) →
          IsDiagOn ρ (Ine (F := ℚ) A) ![1, Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom)])

section Sys

variable {F : Type} [Field F] [NumberField F]

def SelfTw (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (η : HChar F) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ ∃ B, sat v B ∧ B.map (· * η.val v) = B

def adSys (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (v : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ) : Prop :=
  ∃ α β : ℂˣ, sat v {α, β} ∧ B = {α / β, 1, β / α}

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

def IsNormChar (η : HChar F) : Prop :=
  η ≠ 1 ∧ η ^ Module.finrank F E = 1 ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ f : ℕ,
    normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1

variable {E} in

def WeakBC (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (satE : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
    ∃ B, sat (w.under (𝓞 F)) B ∧ satE w (B.map (· ^ f))

end Sys

def AdjointLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2),
    (∃ η : HChar F, η ≠ 1 ∧ η ^ 2 = 1 ∧ SelfTw π.HasSat η) ∨ ∃ P : TR.CuspSub F 3,
      (∀ v (x y : ℂ), π.HasInfChar v {x, y} → P.HasInfChar v {x - y, 0, y - x}) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, adSys π.HasSat w B ∧ P.HasSat w B

def SymCube : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2),
    (∃ η : HChar F, η ≠ 1 ∧ η ^ 2 = 1 ∧ SelfTw π.HasSat η) ∨ (∃ μ : HChar F, μ ≠ 1 ∧ μ ^ 3 = 1 ∧ SelfTw (adSys π.HasSat) μ) ∨
    ∃ P : TR.CuspSub F 4,
      (∀ v (x y : ℂ), π.HasInfChar v {x, y} → P.HasInfChar v {3 * x, 2 * x + y, x + 2 * y, 3 * y}) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
        P.HasSat w {α ^ 3, α ^ 2 * β, α * β ^ 2, β ^ 3}

def CyclicBaseChangeC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    [IsGalois F E], (Module.finrank F E).Prime → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub F a,
      (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨ ∃ P : CuspSub E a,
        (∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧
        WeakBC (CG.mk π).HasSat (CG.mk P).HasSat

def QuadInduction : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ π : TR.CuspSub E a,
      ((∀ (v v' : InfinitePlace E) (m : Multiset ℂ), v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
          π.HasInfChar v m → π.HasInfChar v' m) ∧
        ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
          ∃ B, π.HasSat w B ∧ π.HasSat w' B) ∨
      ∃ P : TR.CuspSub F (2 * a),
        (∀ (v v' : InfinitePlace E) (m m' : Multiset ℂ), v ≠ v' → v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
          π.HasInfChar v m → π.HasInfChar v' m' → P.HasInfChar (v.comap (algebraMap F E)) (m + m')) ∧
        ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
          (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
            ∃ B B', π.HasSat w B ∧ π.HasSat w' B' ∧ P.HasSat (w.under (𝓞 F)) (B + B')) ∧
          (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, π.HasSat w (B'.map (· ^ 2)) ∧
            B = B' + B'.map (fun b => -b) ∧ P.HasSat (w.under (𝓞 F)) B)

end UpperTheory.V.Published
