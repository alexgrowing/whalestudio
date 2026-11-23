import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

section Volume

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def IsCMFam {I : Type} (τ : I → (E →+* ℂ)) : Prop :=
  Function.Bijective fun i => NumberField.InfinitePlace.mk (τ i)

def latC (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def StabHat (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ} (L : Set (Fin M → E))
    (m : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) : Prop :=
  ∀ y, y ∈ latHat F E L ↔ m.mulVec y ∈ latHat F E L

def IsVolMeasF (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E)
    (P Q : I → ℕ) (μ : Measure (HA (AF F) cm.sig W.gram)) : Prop :=
  μ.IsHaarMeasure ∧
  AllSome (fun θ : I → (Ainf F ⊗[F] E →+* ℂ) => ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) fun θ =>
  AllSome (fun A : ∀ ρ : I, Matrix (Fin (P ρ) ⊕ Fin (Q ρ)) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (P ρ) (Q ρ) * A ρ = W.gram.map (τ ρ)) fun A =>
  ∀ B : ∀ ρ : I, Set (UpqT (P ρ) (Q ρ)), (∀ ρ, MeasurableSet (B ρ)) →
    μ {h | StabHat F (latC W) (finMat cm.sig W.gram h) ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat cm.sig W.gram (θ ρ) h} =
      ∏ ρ, cd.cd (P ρ) (Q ρ) (B ρ)

def VolIs (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E) (x : ℝ) : Prop :=
  AllSome (IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2)) fun μ =>
  AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF F) cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
    μ 𝓕 = ENNReal.ofReal x

open Classical in

def trueVol (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E) : ℝ :=
  if h : ∃ x : ℝ, 0 < x ∧ VolIs cm τ cd W x then Classical.choose h else 1

theorem trueVol_pos (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E) :
    0 < trueVol cm τ cd W := by
  unfold trueVol
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact one_pos

theorem trueVol_spec (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E)
    (h : ∃ x : ℝ, 0 < x ∧ VolIs cm τ cd W x) : VolIs cm τ cd W (trueVol cm τ cd W) := by
  unfold trueVol
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

end Volume

def CdScaleIs (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

open Classical in

def trueScale (cd : CDHaar) : ∀ n : ℕ, (Fin n → Bool) → NNReal :=
  if h : ∃ sc : ∀ n : ℕ, (Fin n → Bool) → NNReal, (∀ n ε, 0 < sc n ε) ∧ CdScaleIs cd sc then Classical.choose h
  else fun _ _ => 1

theorem trueScale_pos (cd : CDHaar) (n : ℕ) (ε : Fin n → Bool) : 0 < trueScale cd n ε := by
  unfold trueScale
  split_ifs with h
  · exact (Classical.choose_spec h).1 n ε
  · exact one_pos

def trueDsig (R : Ranks) (P : HCParam R) : ℝ := Formalism.QuantumDeterminants.fdegHC (lamSH R P)

def FiniteVolume₂ : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure →
        ∀ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → μ 𝓕 < ⊤

def DiscreteSeriesExist : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

def FormalDegreeFormula₂ : Prop :=
  ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal), CdScaleIs cd sc →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        fdegOf ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem volTieG_iff (D : D7) : Formalism.L2.Theta.VolTieG D ↔
    ∀ W : HSpace D.host.E, W.SigOK → VolIs D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W (D.vol W) := Iff.rfl

theorem cdScaleTie_iff (D : D7) : cdScaleTie D ↔ CdScaleIs D.cd D.s.cdScale := Iff.rfl

end GlobalTheory.Mem.Vol
