import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped TensorProduct NNReal Matrix ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def blocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def upperLeft {R : Type} {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  g.submatrix (Fin.castAdd n) (Fin.castAdd n)

def blockIdx (n : ℕ) (i : Fin (n + n)) : ℕ := if (i : ℕ) < n then 0 else 1

variable (D : D7)

def skewJ (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E := blocks 0 1 (-1) 0

abbrev UA {k : ℕ} (T : Matrix (Fin k) (Fin k) D.host.E) : Type := AdelicU.GAd D.sp.cm.sig T

abbrev GG (n : ℕ) : Type := UA D (skewJ D n)

variable {D}

def mat {k : ℕ} {T : Matrix (Fin k) (Fin k) D.host.E} (g : UA D T) : Matrix (Fin k) (Fin k) (AE D) :=
  (AdelicU.matHom (AF D.host.F) D.sp.cm.sig T g).1

def mmul {k l r : ℕ} (x : Mx D k l) (y : Mx D l r) : Mx D k r := HMul.hMul x y

def adj {k l : ℕ} (x : Mx D k l) : Mx D l k := Formalism.UG.cT (cA D) x

variable (D)

def siegel (n : ℕ) : Subgroup (GG D n) where
  carrier := {g | (mat g).BlockTriangular (blockIdx n)}
  one_mem' := by
    change (mat (1 : GG D n)).BlockTriangular _
    rw [mat, map_one]; exact Matrix.blockTriangular_one
  mul_mem' := fun {g h} hg hh => by
    change (mat (g * h)).BlockTriangular _
    rw [mat, map_mul]; exact Matrix.BlockTriangular.mul hg hh
  inv_mem' := fun {g} hg => by
    change (mat g⁻¹).BlockTriangular _
    rw [mat, map_inv, Matrix.coe_units_inv]
    letI := (AdelicU.matHom (AF D.host.F) D.sp.cm.sig (skewJ D n) g).invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def maxCpt (n : ℕ) : Subgroup (GG D n) :=
  AdelicU.levelAll D.sp.cm.sig (skewJ D n) (AdelicU.stdLattice D.host.E (n + n)) 1

abbrev rat {k : ℕ} (T : Matrix (Fin k) (Fin k) D.host.E) : Subgroup (UA D T) := AdelicU.ratPts D.sp.cm.sig T

def Cosets (n : ℕ) : Type := Quotient (QuotientGroup.rightRel ((siegel D n).subgroupOf (rat D (skewJ D n))))

variable {D}

def Cosets.rep {n : ℕ} (c : Cosets D n) : GG D n := (Quotient.out c : rat D (skewJ D n))

def absDet {n : ℕ} (a : GL (Fin n) (AE D)) : ℝ≥0 :=
  Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a)

def IsAbsLevi {n : ℕ} (α : GG D n → ℝ≥0) : Prop :=
  ∀ p ∈ siegel D n, ∀ a : GL (Fin n) (AE D), upperLeft (mat p) = a.1 → ∀ k ∈ maxCpt D n, α (p * k) = absDet a

section Space

variable {m n : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E)

def wittIdx : ℕ :=
  sSup {r | ∃ W : Submodule D.host.E (Fin m → D.host.E),
    (∀ x ∈ W, ∀ y ∈ W, hE D.sp.cm.sig T x y = 0) ∧ Module.finrank D.host.E W = r}

def gramQ (x y : Mx D m n) : Mx D n n :=
  mmul (mmul (adj x) (T.map (incA D))) y

def trA (z : AE D) : AF D.host.F := Algebra.trace (AF D.host.F) (AE D) z

def quadTr (b : Mx D n n) (x : Mx D m n) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (Matrix.trace (mmul b (gramQ T x x)))

def pairing (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) : ℂ := ψ (trA (Matrix.trace (gramQ T x y)))

end Space

abbrev Sch (θ : InfFam D) (m n : ℕ) : Type := ModerateGrowthSchwartz.schwartzA θ m n

abbrev Rep (θ : InfFam D) (n : ℕ) {m : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E) : Type :=
  GG D n × UA D T →* Module.End ℂ (Sch θ m n)

section Weil

variable {θ : InfFam D} {m n : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E}

structure IsWeil (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : Rep θ n T) : Prop where

  levi : ∀ (g : GG D n) (a : GL (Fin n) (AE D)), mat g = blocks a.1 0 0 (adj (a⁻¹).1) → ∀ (Φ : Sch θ m n) (x : Mx D m n),
    (ω (g, 1) Φ).1 x = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * ((((absDet a : ℝ) ^ ((m : ℝ) / 2) : ℝ)) : ℂ) *
      Φ.1 (mmul x a.1)

  unip : ∀ (g : GG D n) (b : Mx D n n), mat g = blocks 1 b 0 1 → ∀ (Φ : Sch θ m n) (x : Mx D m n),
    (ω (g, 1) Φ).1 x = ψ (quadTr T b x) * Φ.1 x

  weyl : ∀ g : GG D n, mat g = blocks 0 1 (-1) 0 → ∀ μ : Measure (Mx D m n), SelfDual μ (pairing T ψ) →
    ∀ (Φ : Sch θ m n) (x : Mx D m n), (ω (g, 1) Φ).1 x = ∫ y, Φ.1 y * pairing T ψ x y ∂μ

  lin : ∀ (h : UA D T) (Φ : Sch θ m n) (x : Mx D m n), (ω (1, h) Φ).1 x = Φ.1 (mmul (mat h⁻¹) x)

def IsRealPart (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (c : D.what₂.Tau → ℝ) : Prop :=
  ∀ t : Ainf D.host.F, psiInf D.host.F ψ t =
    Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (c τ : ℂ) * θ τ (t ⊗ₜ[D.host.F] (1 : D.host.E)))

variable (T) in

def gauss (c : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * ∑ τ, ((|c τ| : ℝ) : ℂ) * Matrix.trace ((z τ)ᴴ * (T.map (tauE D τ) * s τ) * z τ))

def polyVal (P : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun v => if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1) P

variable (θ n T) in

def fockSpace (c : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {Φ | ∃ (P : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (f : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      f ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      Φ = fun x => polyVal P (fun τ => compAt θ τ x) * gauss T c s (fun τ => compAt θ τ x) *
        f (fun i j => finPart D (x i j))}

def s0 (m n : ℕ) : ℂ := (m : ℂ) / 2 - (n : ℂ) / 2

def sect (α : GG D n → ℝ≥0) (ω : Rep θ n T) (Φ : Sch θ m n) (s : ℂ) (g : GG D n) : ℂ :=
  ((α g : ℝ) : ℂ) ^ (s - s0 m n) * (ω (g, 1) Φ).1 0

def eisTerm (α : GG D n → ℝ≥0) (ω : Rep θ n T) (Φ : Sch θ m n) (g : GG D n) (s : ℂ) (γ : Cosets D n) : ℂ :=
  sect α ω Φ s (γ.rep * g)

def thetaTerm (ω : Rep θ n T) (Φ : Sch θ m n) (g : GG D n) (h : UA D T) (x : Matrix (Fin m) (Fin n) D.host.E) : ℂ :=
  (ω (g, h) Φ).1 (x.map (incA D))

def theta (ω : Rep θ n T) (Φ : Sch θ m n) (g : GG D n) (h : UA D T) : ℂ := ∑' x, thetaTerm ω Φ g h x

def FormulaAt (α : GG D n → ℝ≥0) (ω : Rep θ n T) (Φ : Sch θ m n) (g : GG D n) : Prop :=
  (∀ s : ℂ, (n : ℝ) / 2 < s.re → Summable fun γ => ‖eisTerm α ω Φ g s γ‖) ∧
  ∃ Eis : ℂ → ℂ, MeromorphicOn Eis Set.univ ∧ (∀ s : ℂ, (n : ℝ) / 2 < s.re → Eis s = ∑' γ, eisTerm α ω Φ g s γ) ∧
    AnalyticAt ℂ Eis (s0 m n) ∧
    (∀ h, Summable fun x => ‖thetaTerm ω Φ g h x‖) ∧
    ∀ (μ : Measure (UA D T)) (𝓕 : Set (UA D T)), μ.IsHaarMeasure → IsFundamentalDomain (rat D T) 𝓕 μ → μ 𝓕 = 1 →
      IntegrableOn (theta ω Φ g) 𝓕 μ ∧ Eis (s0 m n) = ∫ h in 𝓕, theta ω Φ g h ∂μ

end Weil

def FormulaFor (n : ℕ) {m : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D),
    IsCharAF D.host.F ψ → IsHeckeChar D χ → ResEta D χ m → IsInfFam θ →
    AllSome (IsWeil (θ := θ) (n := n) (T := T) ψ χ) fun ω =>
      ∀ α : GG D n → ℝ≥0, IsAbsLevi α →
      ∀ c : D.what₂.Tau → ℝ, IsRealPart ψ θ c →
      ∀ s : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, IsCartanInv (T.map (tauE D τ)) (s τ)) →
      ∀ Φ : Sch θ m n, Φ.1 ∈ fockSpace θ n T c s → ∀ g, FormulaAt α ω Φ g

def SiegelWeil (D : D7) : Prop :=
  ∀ (n m : ℕ) (T : Matrix (Fin m) (Fin m) D.host.E), IsHermND D.sp.cm.sig T →
    n < m → m ≤ 2 * n → n + wittIdx T < m → FormulaFor n T

theorem bddAbove_witt {m : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E) :
    BddAbove {r | ∃ W : Submodule D.host.E (Fin m → D.host.E),
      (∀ x ∈ W, ∀ y ∈ W, hE D.sp.cm.sig T x y = 0) ∧ Module.finrank D.host.E W = r} :=
  ⟨m, by rintro _ ⟨W, -, rfl⟩; simpa using W.finrank_le⟩

theorem upperLeft_blocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : upperLeft (blocks a b c d) = a := by
  ext i j; simp [upperLeft, blocks]

theorem mem_siegel_of_blocks {n : ℕ} {g : GG D n} {a b d : Mx D n n} (h : mat g = blocks a b 0 d) : g ∈ siegel D n := by
  change (mat g).BlockTriangular _
  rw [h]
  intro i j hij
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blocks, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [blockIdx] at hij ⊢

example {θ : InfFam D} {m n : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (α : GG D n → ℝ≥0) (ω : Rep θ n T)
    (Φ : Sch θ m n) (g : GG D n) : sect α ω Φ (s0 m n) g = (ω (g, 1) Φ).1 0 := by simp [sect]

end GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

end
