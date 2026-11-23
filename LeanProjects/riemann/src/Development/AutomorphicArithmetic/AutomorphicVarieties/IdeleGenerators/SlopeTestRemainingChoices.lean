import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.LiftC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

structure Hypotheses₂ : Prop where
  af : Af.Hypotheses₂
  hida : Published.HidaGal
  adj : Published.AdjointLift
  bc : Z.Bc.LiftC

section Sym

variable (R : Type) [CommRing R]

def symSquareMatrixHom : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 3) (Fin 3) R where
  toFun g := !![g 0 0 ^ 2, g 0 0 * g 0 1, g 0 1 ^ 2;
    2 * g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0, 2 * g 0 1 * g 1 1;
    g 1 0 ^ 2, g 1 0 * g 1 1, g 1 1 ^ 2]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

def symCubeMatrixHom : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 4) (Fin 4) R where
  toFun g := !![g 0 0 ^ 3, g 0 0 ^ 2 * g 0 1, g 0 0 * g 0 1 ^ 2, g 0 1 ^ 3;
    3 * g 0 0 ^ 2 * g 1 0, g 0 0 ^ 2 * g 1 1 + 2 * g 0 0 * g 0 1 * g 1 0, 2 * g 0 0 * g 0 1 * g 1 1 + g 0 1 ^ 2 * g 1 0,
      3 * g 0 1 ^ 2 * g 1 1;
    3 * g 0 0 * g 1 0 ^ 2, 2 * g 0 0 * g 1 0 * g 1 1 + g 0 1 * g 1 0 ^ 2, g 0 0 * g 1 1 ^ 2 + 2 * g 0 1 * g 1 0 * g 1 1,
      3 * g 0 1 * g 1 1 ^ 2;
    g 1 0 ^ 3, g 1 0 ^ 2 * g 1 1, g 1 0 * g 1 1 ^ 2, g 1 1 ^ 3]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

variable {Γ k : Type} [Group Γ] [Field k]

def ad0 (ρ : Γ →* GL (Fin 2) k) : Γ →* GL (Fin 3) k :=
  tw ((Units.map (symSquareMatrixHom k)).comp ρ) (Matrix.GeneralLinearGroup.det.comp ρ)⁻¹

def sym3 (ρ : Γ →* GL (Fin 2) k) : Γ →* GL (Fin 4) k := (Units.map (symCubeMatrixHom k)).comp ρ

def IrrOpen [TopologicalSpace Γ] {n : ℕ} (r : Γ →* GL (Fin n) k) : Prop :=
  ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → IsIrr (r.comp H.subtype)

end Sym

section Cong

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {n : ℕ}

def Cong (a b : (Qbar l)ˣ) : Prop := ‖(a : Qbar l) - (b : Qbar l)‖ < 1

def ResSum (r : Γ →* GL (Fin n) (Qbar l)) (χ : Fin n → Γ →* (Qbar l)ˣ) : Prop :=
  ∀ s i, ‖(r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - (∏ j, (X - C (χ j s : Qbar l))).coeff i‖ < 1

end Cong

section Gal

variable {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def IsCC {F : Type} [Field F] [Algebra F Ω] (c : G F Ω) : Prop := ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)

variable {F : Type} [Field F] [NumberField F] [Algebra F Ω]

def IsAlgChar (ι : Qbar l ≃+* ℂ) (κ : G F Ω →* (Qbar l)ˣ) : Prop :=
  Continuous κ ∧ ∃ (art : Ideles F →* Gab F Ω) (χ : HChar F) (a : (F →+* ℂ) → ℤ),
    IsGlobalArtin art ∧ IsAlgPos χ a ∧ IsLAdicOf art ι χ a κ

def IsAutC [IsTotallyComplex F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π

omit [NumberField F] in

def TypeAway (r : G F Ω →* GL (Fin n) (Qbar l)) (τ : Fin n → G F Ω →* (Qbar l)ˣ) : Prop :=
  ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → IsDiagOn r (Ine (F := F) A) τ

omit [NumberField F] in

def OrdAt (r : G F Ω →* GL (Fin n) (Qbar l)) (m : Fin n → ℤ) (ψ : Fin n → G F Ω →* (Qbar l)ˣ) (A : ValuationSubring Ω) : Prop :=
  ∃ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (Dec (F := F) A) κ ∧
    (∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i) ∧ ∀ i s, Cong (κ i s) (ψ i s)

variable [CharZero Ω] [IsAlgClosure ℚ Ω]

omit [NumberField F] [IsAlgClosure ℚ Ω] in

def IsPair [CharZero F] (c : G ℚ Ω) (r : G F Ω →* GL (Fin n) (Qbar l)) (μ : G F Ω →* (Qbar l)ˣ) (P : GL (Fin n) (Qbar l)) : Prop :=
  ∀ s s' : G F Ω, galEmb ℚ F Ω s' = c * galEmb ℚ F Ω s * c⁻¹ →
    (r s : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * (P : Matrix (Fin n) (Fin n) (Qbar l)) * (r s' : Matrix (Fin n) (Fin n) (Qbar l)) =
      (μ s : Qbar l) • (P : Matrix (Fin n) (Fin n) (Qbar l))

structure EisRep (ι : Qbar l ≃+* ℂ) (φ θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop where
  cont : Continuous ρ
  irr : IsIrr ρ
  aut : IsAutR ι ρ
  det : Matrix.GeneralLinearGroup.det.comp ρ = cycBar ℚ Ω l ^ (k - 1) * (φ * θ)
  res : ResSum ρ ![1, cycBar ℚ Ω l ^ (k - 1) * φ]
  away : TypeAway ρ ![1, φ * θ]
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    OrdAt ρ ![(k : ℤ) - 1, 0] ![cycBar ℚ Ω l ^ (k - 1) * φ, 1] A

structure SlopeTestRemainingChoices (N w : ℕ) (θ : G ℚ Ω →* (Qbar l)ˣ) : Prop where
  odd : l ≠ 2
  pos : 0 < N
  cop : ¬ l ∣ N
  prime : w.Prime
  wN : ¬ w ∣ N
  ne : θ ≠ 1
  pow : θ ^ l = 1
  mu : KillsMu w θ

omit [IsAlgClosure ℚ Ω] in

def SplitAt (N w : ℕ) (χ : G ℚ Ω →* (Qbar l)ˣ) : Prop :=
  KillsMu N χ ∧ ∀ s : G ℚ Ω, (∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ ^ w) → χ s = 1

structure IsSeed {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω)
    (ψ τ : Fin n → G L Ω →* (Qbar l)ˣ) (m : Fin n → ℤ) (ka : G L Ω →* (Qbar l)ˣ) (r : G L Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  irr : IsIrr r
  pair : ∃ P : GL (Fin n) (Qbar l), (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∧ IsPair c r 1 P
  res : ResSum r ψ
  away : TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A
  aut : IsAutCsd ι (tw r ka)

structure FieldPairCharacterTripleConditions (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω] (c : G ℚ Ω)
    (N w : ℕ) (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ) : Prop where
  cc : IsCC c
  aux : SlopeTestRemainingChoices N w θ
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  ab : IsAbelianGalois ℚ L
  KL : galOf ℚ L Ω ≤ galOf ℚ K Ω
  η_ker : η.ker = galOf ℚ K Ω
  η_split : SplitAt N w η
  χ_split : SplitAt N w χ'
  θL : galOf ℚ L Ω ≤ θ.ker
  par : χ' c = (-1) ^ j
  sq : ∃ s ∈ galOf ℚ L Ω, ¬ Cong (((cycBar ℚ Ω l ^ j * χ') s) ^ 2) 1

structure IsTwist {K : Type} [Field K] [NumberField K] [Algebra K Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (κ : G K Ω →* (Qbar l)ˣ) : Prop where
  cont : Continuous κ
  alg : ∃ (art : Ideles K →* Gab K Ω) (Y : HChar K) (a : (K →+* ℂ) → ℤ) (τ : K →+* ℂ), IsGlobalArtin art ∧ IsAlgPos Y a ∧
    IsLAdicOf art ι Y a κ ∧ a τ = -1 ∧ a (ComplexEmbedding.conjugate τ) = 0 ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ((discr K : ℤ) : 𝓞 K) ∉ v.asIdeal → Y.UnrAt v
  conj : ∀ s s' : G K Ω, galEmb ℚ K Ω s' = c * galEmb ℚ K Ω s * c⁻¹ → κ s * κ s' = (cycBar K Ω l s)⁻¹
  ver : ∀ (s : G K Ω) (t : G ℚ Ω), t ∉ galOf ℚ K Ω → galEmb ℚ K Ω s = t * t → κ s = -(cycBar ℚ Ω l t)⁻¹
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ¬ A.valuation ((discr K : ℤ) : Ω) < 1 →
    ∀ s ∈ Ine (F := K) A, κ s = 1
  ord : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := K) A, κ s ^ m = 1

end Gal

end UpperTheory.V.Sd
