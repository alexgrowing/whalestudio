import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

def blk {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def IsWittBasis (J : Matrix (Fin n) (Fin n) E) (l : E) (T : GL (Fin (n + n)) E) : Prop :=
  ∃ Z : Matrix (Fin n) (Fin n) E, (2 : E) • (J * Z.map σ) = l • (1 : Matrix (Fin n) (Fin n) E) ∧ T.1 = blk 1 Z 1 (-Z)

def inBasis {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E) (g : UA σ J₂) :
    Matrix (Fin (n + n)) (Fin (n + n)) (AE F E) := incM F (T⁻¹).1 * mat g * incM F T.1

def IsStdK {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E) (K : Subgroup (UA σ J₂)) : Prop :=
  ∀ g, g ∈ K ↔
    (∀ v i j, compFin F E v (inBasis σ T g i j) ∈ intLoc F E v ∧ compFin F E v (inBasis σ T g⁻¹ i j) ∈ intLoc F E v) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (inBasis σ T g).map (piInf τ) ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

def IsAdapted (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ) : Prop :=
  (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : κ → F,
    co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
  (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) ∧
  ∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0

variable (F κ) in

def IsTamagawa [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F)) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ 𝓕 : Set (κ → AF F), μ 𝓕 = 1 ∧
    IsAddFundamentalDomain (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range 𝓕 μ

structure IsWeilFormulas (ψ : AddChar (AF F) ℂ) (χ : Chr F E) (T : GL (Fin (n + n)) E)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ)
    [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F))
    (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) : Prop where

  pres : ∀ p, ∀ Φ ∈ schA F κ, om p Φ ∈ schA F κ

  lin : ∀ h, ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (h, 1) Φ (co.e u).1 = Φ (co.e (mat h⁻¹ * u)).1

  levi : ∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype,
    (p : UA σ J₂) ∈ leviSubOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype →
    ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (1, (p : UA σ J₂)) Φ (co.e u).1 = (χ (aOf finSumFinEquiv _ p) : ℂ) *
      npow (absE F E (aOf finSumFinEquiv _ p)) ((m : ℂ) / 2) * Φ (co.e (u * (mat (p : UA σ J₂)⁻¹)ᵀ)).1

  unip : ∀ b ∈ unipOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype,
    ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (1, b) Φ (co.e u).1 =
      ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂) (u * (mat b)ᵀ) u) * Φ (co.e u).1

  weyl : ∀ w : UA σ J₂, inBasis σ T w = blk 0 1 (-1) 0 → ∃ (γ : ℂ) (k : ℕ), 0 < k ∧ γ ^ k = 1 ∧
    ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (1, w) Φ (co.e u).1 = γ * ∫ y, Φ y * ψ (y ⬝ᵥ (co.e (u * (mat w⁻¹)ᵀ)).2) ∂μ

end GlobalTheory.SWLit

end
