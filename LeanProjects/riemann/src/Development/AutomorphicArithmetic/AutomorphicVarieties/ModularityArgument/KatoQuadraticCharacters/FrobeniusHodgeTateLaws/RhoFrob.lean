import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaElementsUnramifiedOrdinaryOfEulerSystemInert
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.CycMOfNot
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace UpperTheory.V.Z.Kato.Joint

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def cyc1 (l : ℕ) [Fact l.Prime] (s : G ℚ Ω) : ZMod l := ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

open Classical in

def Expl (ι : Qbar l ≃+* ℂ) (e : ℕ) (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (j : Ω →+* Qbar l) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (cc : ℕ → ℂ) (n : ℕ) (β : Fin n → Qbar l) (t : Fin n → ℕ) : Prop :=
  ∃ (κ : Qbar l) (v : ℕ → Qbar l) (m₀ c₀ : ℕ), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
    HTLawCsOfCoef A c Z j m₀ c₀ fun m ψ' z => if ψ' (-1) = ι.symm s then
      v m * κ * ι.symm α ^ m * ((∑ i, β i * ψ'⁻¹ (t i : ZMod (l ^ m))) * (∑ b : (ZMod (l ^ m))ˣ, ψ' b * z ^ (b : ZMod (l ^ m)).val) *
        ι.symm (GlobalTheory.EisM.mesMu (2 * e + 1) l u w α B cc m fun y => ι (ψ' y))) else 0

def Meas3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ)
    (c : ℕ → ℂ) (v : ℂ) (n : ℕ) (β : Fin n → Qbar l) (t : Fin n → ℕ), l ≠ 2 → 1 ≤ e → s = (-1) ^ e * ψ (-1) →
    GlobalTheory.EisM.MeasMu ι e s u w ψ α B c v → v ≠ 0 → (∀ i, ¬ l ∣ t i) →
    (∑ i, ι (β i) * ψ⁻¹ (t i : ZMod l) * (t i : ℂ) ^ e) ≠ 0 →
    ∃ (cO : Coef l) (L : PowerSeries (Qbar l)) (κ : Qbar l) (φ : DirichletCharacter (Qbar l) l) (n₀ r₁ : ℕ), κ ≠ 0 ∧
      (∀ n, L.coeff n ∈ cO.O) ∧ (∀ x : ZMod l, ι (φ x) = ψ⁻¹ x) ∧
      (∀ m, 1 ≤ m → ∀ ψ' : DirichletCharacter (Qbar l) (l ^ m), ψ' (-1) = ι.symm s → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
        Cg (2 * m) (∑ b : (ZMod (l ^ m))ˣ, ψ' b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))
          (κ * (∑ i, β i * ψ'⁻¹ (t i : ZMod (l ^ m))) * (∑ b : (ZMod (l ^ m))ˣ, ψ' b * z ^ (b : ZMod (l ^ m)).val) *
            ι.symm (GlobalTheory.EisM.mesMu (2 * e + 1) l u w α B c m (fun y => ι (ψ' y))))) ∧
      (∀ m, 1 ≤ m → ∀ ψ' : DirichletCharacter (Qbar l) (l ^ m), ψ' (-1) = -ι.symm s → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
        Cg (2 * m) (∑ b : (ZMod (l ^ m))ˣ, ψ' b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val)) 0) ∧
      ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
        ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0

def JEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
    (l : Ω) ∈ A.nonunits ∧ ∃ j : Ω →+* Qbar l, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1

def CoefUb : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c c' : Coef l) (F : Finset (Qbar l)), (∀ x ∈ F, ‖x‖ ≤ 1) →
    ∃ c'' : Coef l, c.O ≤ c''.O ∧ c'.O ≤ c''.O ∧ ∀ x ∈ F, x ∈ c''.O

def Mono : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c c' : Coef l), c.O ≤ c'.O →
    (∀ (W : R2 Ω l) y S', Sys W c y S' → Sys W c' y S') ∧
    (∀ (A : ValuationSubring Ω) ν Z, IwSys2 c A ν Z → IwSys2 c' A ν Z) ∧
    ∀ (A : ValuationSubring Ω) Z j m₀ c₀ Rhs, HTLawCsOfCoef A c Z j m₀ c₀ Rhs → HTLawCsOfCoef A c' Z j m₀ c₀ Rhs

def PsiEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (χ : G ℚ Ω →* (Qbar l)ˣ),
    KillsMu l χ → ∃ ψ : DirichletCharacter ℂ l, ∀ s, (χ s : Qbar l) = ι.symm (ψ (cyc1 l s))

def FrobU : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω)
    (W : R2 Ω l), Nf e S A W → (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ) ∧ (∀ s ∈ Dec (F := ℚ) A, ‖mat W s 1 1‖ = 1) ∧
      ∀ s : G ℚ Ω, ‖eps l s‖ = 1

def RhoFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) → ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = (eps l s ^ e * (χ s : Qbar l)⁻¹) • mat W s) →
    (∃ S0 : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s →
      Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = ι.symm (g.a q) ∧
      Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = (q : Qbar l) ^ (2 * e) * ι.symm (g.χ (q : ZMod g.M))) ∧
    ∀ V : Submodule (Qbar l) (Fin 2 → Qbar l), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤

def DetIne : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    ¬ l ∣ g.M → g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) → ∀ s ∈ Ine (F := ℚ) A, dt W s = χ s ^ 2

def Unif : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (f : G ℚ Ω → Qbar l), Continuous f →
    ∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ

def HatW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N), l ≠ 2 →
    (∃ x : ZMod N, GlobalTheory.EisM.hat θ (x.val : ℤ) ≠ 0) ∧ (∀ d : ℤ, ‖ι.symm (GlobalTheory.EisM.hat θ d / 2)‖ ≤ 1) ∧
      ∀ d : ℤ, GlobalTheory.EisM.hat θ d = GlobalTheory.EisM.hat θ (((d : ZMod N).val : ℕ) : ℤ)

def PinOf : Prop := Meas3 → CoefUb → Mono →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (A : ValuationSubring Ω) (W : R2 Ω l)
    (c : Coef l) (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l) (u w : ℤ → ℂ)
    (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (cc : ℕ → ℂ) (v : ℂ) (n : ℕ) (β : Fin n → Qbar l) (t : Fin n → ℕ),
    l ≠ 2 → 1 ≤ e → ‖ι.symm α‖ = 1 → (∀ x ∈ A, ‖j x‖ ≤ 1) → (∀ s ∈ Ine (F := ℚ) A, ν s = 1) →
    (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ ∧ ‖(ν σ : Qbar l)‖ = 1) →
    GlobalTheory.EisM.MeasMu ι e ((-1) ^ e * ψ (-1)) u w ψ α B cc v → v ≠ 0 → (∀ i, ¬ l ∣ t i) →
    (∑ i, ι (β i) * ψ⁻¹ (t i : ZMod l) * (t i : ℂ) ^ e) ≠ 0 →
    Expl ι e A c Z j ((-1) ^ e * ψ (-1)) u w α B cc n β t →
    ∃ c' : Coef l, c.O ≤ c'.O ∧ Pin7 e A W c' ν (GlobalTheory.K4.chiK l fun x => ι.symm (ψ x)) Z

def smB (k c d : ℕ) (a b : Qbar l) : Fin 4 → Qbar l :=
  ![(c : Qbar l) ^ 2 * (d : Qbar l) ^ 2, -((c : Qbar l) ^ ((3 : ℤ) - k) * a * (d : Qbar l) ^ 2), -((c : Qbar l) ^ 2 * (d * b)),
    (c : Qbar l) ^ ((3 : ℤ) - k) * a * (d * b)]

def smT (N c d : ℕ) : Fin 4 → ℕ := ![N, N * c, N * d, N * c * d]

def SmNz : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N c d : ℕ) (ψ : DirichletCharacter ℂ l) (a b : ℂ), ¬ l ∣ N → 0 < N → 0 < c → 0 < d →
    ¬ l ∣ c → ¬ l ∣ d → ‖a‖ = 1 → (∀ z : ℂ, ‖z‖ = 1 → (c : ℂ) ^ e ≠ z) → (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (b * ψ d ^ (-1 : ℤ)) →
    (∀ i, ¬ l ∣ smT N c d i) ∧
      (∑ i, ι (smB (2 * e + 1) c d (ι.symm a) (ι.symm b) i) * ψ⁻¹ (smT N c d i : ZMod l) * (smT N c d i : ℂ) ^ e) ≠ 0

end UpperTheory.V.Z.Kato.Joint

end
