import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af

section Rep

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

def IsIrr (r : Γ →* GL (Fin n) k) : Prop := IsIrrSub r ⊤

def RepIso (r r' : Γ →* GL (Fin n) k) : Prop := ∃ g : GL (Fin n) k, ∀ s, r' s = g * r s * g⁻¹

def tw (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) : Γ →* GL (Fin n) k where
  toFun s := Matrix.GeneralLinearGroup.scalar (Fin n) (χ s) * r s
  map_one' := by simp
  map_mul' s t := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul, mul_comm]

theorem tw_val (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s : Γ) :
    (tw r χ s : Matrix (Fin n) (Fin n) k) = (χ s : k) • (r s : Matrix (Fin n) (Fin n) k) := by
  simp [tw, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

def IsDiagOn (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (χ : Fin n → Γ →* kˣ) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s ∈ H, ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
    Matrix.diagonal fun i => (χ i s : k)

def IsFlagOn (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (κ : Fin n → ↥H →* kˣ) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
    ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)

end Rep

section Level

variable (F : Type) [Field F] [NumberField F]

def Ohat : Subring (Af F) := ⨅ w : HeightOneSpectrum (𝓞 F), (w.adicCompletionIntegers F).toSubring.comap (pLoc F w)

def KLev (n M : ℕ) : Subgroup (GL (Fin n) (Af F)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}))).ker.map
    (Matrix.GeneralLinearGroup.map (Ohat F).subtype)

variable {F} in

def HasFixed {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (U : Subgroup Γ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ u ∈ U, ρ u v = v

end Level

section Gal

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

omit [NumberField F] in

def KillsMu (M : ℕ) {C : Type} [Monoid C] (χ : G F Ω →* C) : Prop :=
  ∀ s : G F Ω, (∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) → χ s = 1

def FrobEig (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂ) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := F) A, r s = 1) ∧
    ∀ σ : G F Ω, IsFrob A (normV w) σ →
      (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = (B.map fun b => X - C b).prod

def algSat (n q : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun α => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)

def AttachedSys (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) : Prop :=
  IsSSRep r ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, sat w B ∧ FrobEig ι r w (algSat n (normV w) B)

def AttC [IsTotallyComplex F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n) : Prop :=
  AttachedSys ι r (CG.mk π).HasSat

def IsAutCsd [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π

variable (l) in

def LevelAway (M : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ χ : Fin n → G F Ω →* (Qbar l)ˣ, (∀ i, KillsMu M (χ i)) ∧ IsDiagOn r (Ine (F := F) A) χ

omit [NumberField F] in

def PotCrysAt (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O)
    (Bw : LocBridge l F Ω (Dec (F := F) A) O), GlobalTheory.Pst.Induces Bw ∧
      GlobalTheory.Pst.IsPotCrysAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)

variable (l) in

def LevelAt (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ (χ : Fin n → G F Ω →* (Qbar l)ˣ) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      (∀ i, KillsMu M (χ i)) ∧ IsFlagOn r (Dec (F := F) A) κ ∧
      (∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i * χ i s) ∧
      ((∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ PotCrysAt r A)

variable (l) in

structure Level (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  away : LevelAway l M r
  above : LevelAt l M m r

omit [NumberField F] in
variable (F) in

def decJ (j : Ω →+* Om l) : Subgroup (G F Ω × GQ l) where
  carrier := {x | ∀ y : Ω, x.2 (j y) = j (x.1 y)}
  one_mem' _ := rfl
  mul_mem' {x x'} hx hx' y := by
    change x.2 (x'.2 (j y)) = j (x.1 (x'.1 y))
    rw [hx' y, hx]
  inv_mem' {x} hx y := by
    change x.2.symm (j y) = j (x.1.symm y)
    rw [AlgEquiv.symm_apply_eq, hx]
    simp

variable {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]

variable (l) in

structure IsBK (ρ : Representation C (G F Ω) V) (c : G F Ω → V) : Prop where
  away : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ x : V, ∀ s ∈ Ine (F := F) A, c s = ρ s x - x
  above : ∀ τ : F →+* Om l, ∃ j : Ω →+* Om l, j.comp (algebraMap F Ω) = τ ∧
    (fun x : ↥(decJ F j) => c x.1.1) ∈ Loc.finiteCocycles ((MonoidHom.snd _ _).comp (decJ F j).subtype)
      (ρ.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype))

variable (l) in

def BlochKatoSelmerVanishes (ρ : Representation C (G F Ω) V) : Prop := ∀ c ∈ Z1 ρ, IsBK l ρ c → c ∈ ReciprocityTheory.Gal.B1 ρ

end Gal

end UpperTheory.V.Af
