import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.UG Formalism.BasicNotions
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.PRep

namespace GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def rootPow (Λ : Fin N → ℝ) (r : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, if h : (i : ℕ) + 1 < N then (r i / r ⟨i + 1, h⟩) ^ Λ i else 1

def Bd (Λ : Fin N → ℝ) (f : GA E N → ℂ) : Prop :=
  ∀ Ω : Set (GL (Fin N) (Cinf E)), IsCompact Ω → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ (r : Fin N → ℝ) (d : GL (Fin N) (Cinf E)),
    (∀ i, 0 < r i) → (∀ i j : Fin N, (j : ℕ) = i + 1 → t * r j ≤ r i) →
    d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖f (infGL E N (d * c))‖ ≤ C * rootPow Λ r

def BdD (Λ : Fin N → ℝ) (φ : Sm E N) : Prop := ∀ l : List (Lie E N), Bd Λ ((l.map (lie E N)).prod φ).1

def locR (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin N) (w.adicCompletion E)) (Sm E N) :=
  (finRep E N).comp (locGL E N w)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

def LocMap (V : Submodule ℂ (Sm E N)) (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (y : Fin n → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) (hd : ∑ i, (y i).1 = N) : Prop :=
  ∃ b : Sm E N →ₗ[ℂ] GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.stdBlocks (fun i => (y i).1) hd) (GlobalTheory.SmGL.piTensor fun i => (y i).rep),
    (∃ φ ∈ V, b φ ≠ 0) ∧ ∀ φ ∈ V, ∀ g, b (locR N w g φ) = GlobalTheory.LocGL.prodIrr y hd g (b φ)

section CM

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

structure IsBCW (π : Submodule ℂ (UA L n → ℂ)) {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (V : ∀ i, Submodule ℂ (Sm L (N i)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 L)), SmIrr (GL (Fin (N i)) (w.adicCompletion L)))
    (m : Fin c → (L →+* ℂ) → Multiset ℂ) : Prop where
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  unram : ∀ w, IsUnramU π w → GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w n)
  inert : ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L)
    (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w (locProd h w (σ · w)) (GlobalTheory.LGrp.bcParam n α)
  split : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))
  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, m i τ = infOfWeight lam

end CM

def BCSpehU : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L],
    (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm L (N i)))
        (σ : ∀ i (w : HeightOneSpectrum (𝓞 L)), SmIrr (GL (Fin (N i)) (w.adicCompletion L)))
        (m : Fin c → (L →+* ℂ) → Multiset ℂ), IsBCW π h V σ m ∧
        ∀ i, ∃ (a d : ℕ) (P : CuspSub L a), SpehShape (V i) P d ∧ P.IsCsd

end GlobalTheory.ResW

end
