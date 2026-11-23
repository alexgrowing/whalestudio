import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable (σ) in

abbrev G2 (Y : Spc F E n) : Type := UG (cA σ) (dbl (incM F Y.J))

variable {Y : Spc F E n} {A : Spc F E m}

def mat2 (x : G2 σ Y) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := x.1.1

variable (σ Y) in

def rat2 : Subgroup (G2 σ Y) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf _

def ht2 (x : G2 σ Y) : ℝ≥0 := heightGL F x.1

def IsPar (p : G2 σ Y) (t : GL (Fin n) (AE F E)) : Prop :=
  mat2 p * diagCols (Fin n) = diagCols (Fin n) * (t : Matrix (Fin n) (Fin n) (AE F E))

variable (σ Y) in

def par2 : Subgroup (G2 σ Y) := Subgroup.closure {p | ∃ t, IsPar p t}

def IsEmb (h h' : UA σ Y.J) (x : G2 σ Y) : Prop := mat2 x = Matrix.fromBlocks (mat h) 0 0 (mat h')

def IsStab2 (B : Base F E) (K : Subgroup (G2 σ Y)) : Prop :=
  ∀ k, k ∈ K ↔ (∀ w, Commute ((mat2 k).map (piInf (B.emb w))) (Matrix.fromBlocks (Y.θ w) 0 0 (-Y.θ w))) ∧
    ∀ z z', z ∈ latHat Y → z' ∈ latHat Y → ∀ k' ∈ ({k, k⁻¹} : Set (G2 σ Y)),
      (mat2 k' *ᵥ Sum.elim z z') ∘ Sum.inl ∈ latHat Y ∧ (mat2 k' *ᵥ Sum.elim z z') ∘ Sum.inr ∈ latHat Y

structure IsHgt (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ) : Prop where
  iwa : ∀ x : G2 σ Y, ∃ p t, IsPar p t ∧ ∃ k ∈ K, x = p * k
  val : ∀ p t, IsPar p t → ∀ k ∈ K, a (p * k) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ)

def flat (a : G2 σ Y → ℝ) (f : G2 σ Y → ℂ) (s₀ s : ℂ) (x : G2 σ Y) : ℂ := (a x : ℂ) ^ (s - s₀) * f x

def eisTerm (f : G2 σ Y → ℂ) (x : G2 σ Y) (q : Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y)))) : ℂ :=
  f ((Quotient.out q).1 * x)

structure IsEisCont (f : ℂ → G2 σ Y → ℂ) (U : Set ℂ) (Ê : ℂ → G2 σ Y → ℂ) : Prop where
  isOpen : IsOpen U
  conn : IsPreconnected U
  disc : ∀ s : ℂ, ∀ᶠ s' in 𝓝[≠] s, s' ∈ U
  half : ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧ ∀ x, HasSum (eisTerm (f s) x) (Ê s x)
  hol : ∀ x, DifferentiableOn ℂ (Ê · x) U
  cont : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) (U ×ˢ Set.univ)
  grow : ∀ s ∈ U, ∃ (ε C : ℝ) (N : ℕ), 0 < ε ∧ ∀ s' ∈ Metric.ball s ε, ∀ x, ‖Ê s' x‖ ≤ C * (ht2 x : ℝ) ^ N

structure IsDbl (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (χ : Chr F E)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) : Prop where
  rat : ∀ x : Matrix (Fin m) (Fin n ⊕ Fin n) E, ∃ y z : κ → F,
    dd.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))
  weil : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F A.J) (dbl (incM F Y.J)) dd χ (diagCols (Fin n)) om
  lin : IsUSplitting (adeleClass F) ψ dd (fun (g : UA σ A.J) x => mat g * x) S
  adm : l ∈ (adeleClass F).adm κ
  kill : ∀ z : Matrix (Fin m) (Fin n) (AE F E), ∀ Φ ∈ schA F κ, l (dd.rho ψ (z * (diagCols (Fin n))ᵀ) Φ) = l Φ
  fix : ∀ g, ∀ Φ ∈ schA F κ, l (S g Φ) = l Φ
  theta : ∀ Φ ∈ schA F κ, HasSum (fun y : Matrix (Fin m) (Fin n) E =>
    l (dd.rho ψ (incM F (Matrix.fromCols y (-y))) Φ)) (thetaSum F Φ)

def EisValueAt (f : ℂ → G2 σ Y → ℂ) (s₀ : ℂ) (val : G2 σ Y → ℂ) : Prop :=
  ∀ x, ∃ e : ℂ → ℂ, MeromorphicOn e Set.univ ∧ (∃ t : ℝ, ∀ s : ℂ, t < s.re → HasSum (eisTerm (f s) x) (e s)) ∧
    AnalyticAt ℂ e s₀ ∧ e s₀ = val x

def SWAniso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ

structure IsSec (K : Subgroup (G2 σ Y)) (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) : Prop where
  cont : Continuous f
  law : ∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s₁ + n / 2) * f x
  fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1)))

def IsRegAt (Ê : ℂ → G2 σ Y → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → G2 σ Y → ℂ), 0 < r ∧ (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ x, H s x = (s - s₀) ^ k * Ê s x) ∧
    (∀ x, DifferentiableOn ℂ (H · x) (Metric.ball s₀ r)) ∧
    ContinuousOn (fun y : ℂ × G2 σ Y => H y.1 y.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ x, ‖H s x‖ ≤ C * (ht2 x : ℝ) ^ N

def EisContinues : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ b : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ b →
    ∀ K a, IsStab2 (σ := σ) (Y := Y) B K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ U Ê, IsEisCont (flat a f s₁) U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k

end GlobalTheory.ThK.Dbl

end
