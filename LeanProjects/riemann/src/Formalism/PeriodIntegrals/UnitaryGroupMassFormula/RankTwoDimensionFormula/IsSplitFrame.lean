import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGe

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

def hrow (x : Fin n → A) : Fin n → A := fun q => ∑ p, σ (x p) * J p q

def sMat (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  1 + ∑ i, ∑ j, ((C - 1) i j • Matrix.vecMulVec (b i) (hrow σ J (bs j)) +
    (D - 1) i j • Matrix.vecMulVec (bs i) (hrow σ J (b j)))

def IsSplitFrame (ε : A) (b bs : Fin k → Fin n → A) : Prop :=
  ε * ε = ε ∧ ε * σ ε = 0 ∧ (∀ i, b i = ε • b i) ∧ (∀ i, bs i = σ ε • bs i) ∧
    ∀ i j, Formalism.UG.hform σ J (bs i) (b j) = if i = j then ε else 0

end Alg

def IdxDAlg : Prop :=
  ∀ (A : Type) [CommRing A] (σ : A →+* A) (n k : ℕ) (J : Matrix (Fin n) (Fin n) A) (ε : A)
    (b bs : Fin k → Fin n → A), (∀ a, σ (σ a) = a) → Formalism.UG.IsHerm σ J → IsSplitFrame σ J ε b bs →
    (∀ (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A),
      (∀ j, Formalism.UG.hform σ J (b j) y = 0 ∧ Formalism.UG.hform σ J (bs j) y = 0) → sMat σ J b bs C D *ᵥ y = y) ∧
    (∀ C₁ D₁ C₂ D₂ : Matrix (Fin k) (Fin k) A,
      sMat σ J b bs C₁ D₁ * sMat σ J b bs C₂ D₂ = sMat σ J b bs (C₁ * C₂) (D₁ * D₂)) ∧
    (∀ C D : Matrix (Fin k) (Fin k) A, ε • (C - 1) = 0 → σ ε • (D - 1) = 0 → sMat σ J b bs C D = 1) ∧
    ∀ C C' : Matrix (Fin k) (Fin k) A, C' * C = 1 →
      Formalism.UG.cT σ (sMat σ J b bs C (C'.map σ)ᵀ) * J * sMat σ J b bs C (C'.map σ)ᵀ = J

def EgProp (F : Type) [Field F] [NumberField F] (g : ℕ) (e : Af F) : Prop :=
  e ∈ Formalism.UG.intAd F ∧ e * e = e ∧
    (∃ t ∈ Formalism.UG.intAd F, 1 - e = (g : Af F) * t) ∧
    ∀ c ∈ Formalism.UG.intAd F, ∃ y ∈ Formalism.UG.intAd F, e * (1 + (g : Af F) * c) * y = e

def IdxDAd : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ), ∃ e : Af F, EgProp F g e

def IdxDJacE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (g : ℕ)
    (e : Af F), EgProp F g e →
    ∀ m ∈ IntAf F E, ∃ y ∈ IntAf F E,
      ((1 : E) ⊗ₜ[F] e) * (1 + (g : E ⊗[F] Af F) * m) * y = (1 : E) ⊗ₜ[F] e

def IdxDInt : Prop :=
  ∀ I : AutInst, (∀ x ∈ I.Lf, ∀ y ∈ I.Lf, hA I x y ∈ IntAf I.F I.E) ∧
    ∀ c ∈ IntAf I.F I.E, sigA I c ∈ IntAf I.F I.E

def fixV {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Set (VA X.B.I) :=
  Set.range (fun a => incl X.B.I (X.eR a)) ∪ Set.range (fun a => incl X.B.I (X.fR a)) ∪
    {X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)}

abbrev JA (I : AutInst) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def epsX {D : D7} (X : HidaSetting D) (e : Af X.B.I.F) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * X.ew

def IdxDFrame : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
    ∃ b bs : Fin D.R.k → VA X.B.I,
      IsSplitFrame (sigA X.B.I) (JA X.B.I) (epsX X e) b bs ∧
      (∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf) ∧
      (∀ i, ∀ y ∈ fixV X u, hA X.B.I (b i) y = 0 ∧ hA X.B.I (bs i) y = 0) ∧
      ∀ i j, ZMod' X.B.I X.B.g (hA X.B.I (bs i) (X.bw j) - if i = j then X.ew else 0) ∧
        ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (b j) - if i = j then X.ew else 0)

def IdxDMat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (TR : TypedRed X) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
    ∀ A : Iof TR, ∃ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      C' * C = 1 ∧ (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) ∧
      ∀ v i j, resT TR v (epsX X e * C i j) = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j

def IdxDLevi : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (TR : TypedRed X) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
    ∀ b bs : Fin D.R.k → VA X.B.I, IsSplitFrame (sigA X.B.I) (JA X.B.I) (epsX X e) b bs →
      (∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf) →
      (∀ i j, ZMod' X.B.I X.B.g (hA X.B.I (bs i) (X.bw j) - if i = j then X.ew else 0) ∧
        ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (b j) - if i = j then X.ew else 0)) →
      ∀ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), C' * C = 1 →
        (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) →
        ∀ v i j, resT TR v (hA X.B.I (X.bwd i)
            (sMat (sigA X.B.I) (JA X.B.I) b bs C (C'.map (sigA X.B.I))ᵀ *ᵥ X.bw j)) =
          resT TR v (epsX X e * C i j)

def IdxDSig : Prop :=
  ∀ I : AutInst, (∀ a, sigA I (sigA I a) = a) ∧ Formalism.UG.IsHerm (sigA I) (JA I)

end PI.UnitaryDimensionFormula
