import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}

variable (σ Y) in

def nA (b : GL (Fin n ⊕ Fin n) E) : AddSubgroup (Matrix (Fin n) (Fin n) (AE F E)) :=
  AddSubgroup.closure {β | ∃ x : G2 σ Y, inFrame b x = Matrix.fromBlocks 1 β 0 1}

variable (σ Y) in

def nF (b : GL (Fin n ⊕ Fin n) E) : AddSubgroup (nA σ Y b) :=
  AddSubgroup.closure {β | ∃ T : Matrix (Fin n) (Fin n) E, β.1 = incM F T}

def IsNMap (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y) : Prop :=
  ∀ β, inFrame b (nb β) = Matrix.fromBlocks 1 β.1 0 1

def CoefData (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y) (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) : Prop :=
  IsNMap b nb ∧ lam.IsAddHaarMeasure ∧ IsAddFundamentalDomain (nF σ Y b) 𝓖 lam ∧ lam 𝓖 = 1

def fc (ψ : AddChar (AF F) ℂ) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y) (lam : Measure (nA σ Y b))
    (𝓖 : Set (nA σ Y b)) (f : G2 σ Y → ℂ) (T : nF σ Y b) (x : G2 σ Y) : ℂ :=
  ∫ β in 𝓖, f (nb β * x) * ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam

def IsND {b : GL (Fin n ⊕ Fin n) E} (T : nF σ Y b) : Prop := T.1.1.det ≠ 0

def IsCont (f : ℂ → G2 σ Y → ℂ) (Ê : ℂ → G2 σ Y → ℂ) : Prop :=
  (∃ t : ℝ, ∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (f s) x) (Ê s x)) ∧
    ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → G2 σ Y → ℂ), U ∈ 𝓝 s₀ ∧
      (∀ s ∈ U, s ≠ s₀ → ∀ x, H s x = (s - s₀) ^ k * Ê s x) ∧ ∀ x, DifferentiableOn ℂ (H · x) U

def Coef (Ê : ℂ → G2 σ Y → ℂ) (s₀ : ℂ) (k j : ℕ) (c : G2 σ Y → ℂ) : Prop :=
  ∃ (U : Set ℂ) (H : ℂ → G2 σ Y → ℂ), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, H s x = (s - s₀) ^ k * Ê s x) ∧
    (∀ x, DifferentiableOn ℂ (H · x) U) ∧ ∀ x, c x = iteratedDeriv j (H · x) s₀ / (j.factorial : ℂ)

structure Std (B : Base F E) {m : ℕ} (A : Spc F E m) (Y : Spc F E n) (r s r' s' : ℕ) (χ : Chr F E) (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ)
    (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)) (Φ : (κ → AF F) → ℂ) : Prop where
  good : B.IsGood σ
  hm : 1 ≤ m
  hn : 1 ≤ n
  hnm : n < m
  aniso : min r s = 0
  sign : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s'
  hecke : IsHecke F E χ
  res : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m
  dbl : IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l
  frame : IsFrame2 σ Y b
  stdK : IsStdK (σ := σ) (Y := Y) B b K
  hgt : IsHgt K a
  haar : μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ A.J) D μ
  sch : Φ ∈ schA F κ
  fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ))

def s0 (m n : ℕ) : ℂ := ((m : ℂ) - n) / 2

def sec {κ : Type} (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (a : G2 σ Y → ℝ)
    (m : ℕ) (Φ : (κ → AF F) → ℂ) : ℂ → G2 σ Y → ℂ :=
  flat a (fun x => l (om x Φ)) (s0 m n)

def thetaMean {m : ℕ} {A : Spc F E m} {κ : Type} (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ))
    (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)) (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J))
    (Φ : (κ → AF F) → ℂ) (x : G2 σ Y) : ℂ :=
  ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ

def SWStdLt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ →
      EisValueAt (sec om l a m Φ) (s0 m n) (thetaMean om S μ D Φ)

def ContP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ → ∃ Ê, IsCont (sec om l a m Φ) Ê

def LcCoef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ → ∀ Ê, IsCont (sec om l a m Φ) Ê →
    ∀ nb lam 𝓖, CoefData b nb lam 𝓖 → ∀ (k j : ℕ) (c : G2 σ Y → ℂ), Coef Ê (s0 m n) k j c →
    ∀ T, Coef (fun z x => fc B.ψ b nb lam 𝓖 (Ê z) T x) (s0 m n) k j (fc B.ψ b nb lam 𝓖 c T)

def CoefND : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ → ∀ Ê, IsCont (sec om l a m Φ) Ê →
    ∀ nb lam 𝓖, CoefData b nb lam 𝓖 → ∀ T, IsND T → ∀ (k j : ℕ), j ≤ k →
    Coef (fun z x => fc B.ψ b nb lam 𝓖 (Ê z) T x) (s0 m n) k j
      (fun x => if j = k then fc B.ψ b nb lam 𝓖 (thetaMean om S μ D Φ) T x else 0)

def VanishPole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ → ∀ Ê, IsCont (sec om l a m Φ) Ê →
    ∀ nb lam 𝓖, CoefData b nb lam 𝓖 → ∀ (k j : ℕ) (c : G2 σ Y → ℂ), j < k → Coef Ê (s0 m n) k j c →
    (∀ T, IsND T → ∀ x, fc B.ψ b nb lam 𝓖 c T x = 0) → c = 0

def VanishVal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ → ∀ Ê, IsCont (sec om l a m Φ) Ê →
    ∀ nb lam 𝓖, CoefData b nb lam 𝓖 → ∀ (k : ℕ) (c : G2 σ Y → ℂ), Coef Ê (s0 m n) k k c →
    (∀ T, IsND T → ∀ x, fc B.ψ b nb lam 𝓖 c T x = fc B.ψ b nb lam 𝓖 (thetaMean om S μ D Φ) T x) →
    c = thetaMean om S μ D Φ

def CoefDataExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E), B.IsGood σ → IsFrame2 σ Y b → ∃ nb lam 𝓖, CoefData (σ := σ) (Y := Y) b nb lam 𝓖

def HeadPlus : Prop :=
  ContP → LcCoef → CoefND → VanishPole → VanishVal → CoefDataExists → SWStdLt

end PositivityTheory.SiegelWeilFormula

end
