import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelSectionLeviMulEqAbsDetPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGoodCompatThree
import Development.AutomorphicSpectrum.PublishedTheorems.SiegelWeil₂.SiegelEisensteinDoublingOfContinuation

noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.AdelicU (frameLat)
open GlobalTheory.RegSch (Lvl Compat)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace FirstTermFar

variable {D : D7}

section Defs

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

def StdPos (b : GL (Fin T.rank) (AE D)) (b' : GL (Fin T'.rank) (AE D)) : Prop :=
  IsMaj T b ∧ IsMaj T' b' ∧ Compat d ⟨frameLat T, b⟩ ⟨frameLat T', b'⟩ ∧ HasIw d (Kmax T b)

def EisensteinContinuesFar (b : GL (Fin T.rank) (AE D)) : Prop :=
  (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ h, CosetConv (stab d) (GQ T) (sphericalSection d b s) h) ∧ (∀ h, Continues (sphericalEisenstein d b h)) ∧
    eisensteinResidue d b ≠ 0 ∧ ∀ h, PoleLE (sphericalEisenstein d b h) (rhoH T t) 1 ∧ ResidueAt (sphericalEisenstein d b h) (rhoH T t) (eisensteinResidue d b)

variable (V : HSp D) (Φ : ℂ → GA D (dblSp V) → ℂ)

def EisPoleLEFar (s₀ : ℂ) (k : ℕ) : Prop := EisConvFar V Φ ∧ ∀ g, PoleLE (eisSer V Φ g) s₀ k

def EisCoeffFar (s₀ : ℂ) (n : ℤ) (φ : GA D (dblSp V) → ℂ) : Prop :=
  EisConvFar V Φ ∧ ∀ g, CoeffAt (eisSer V Φ g) s₀ n (φ g)

end Defs

variable {T T' : HSp D} {t : ℕ} {d : HypDec T T' t} {b : GL (Fin T.rank) (AE D)}
  {V : HSp D} {Φ : ℂ → GA D (dblSp V) → ℂ} {s₀ : ℂ} {k : ℕ} {n : ℤ} {φ φ' : GA D (dblSp V) → ℂ}

end FirstTermFar

open FirstTermFar

def RegularisedSiegelWeilFirstTermIdentity₂ : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * V.rank → T'.rank < T.rank → 0 < T'.rank →
  ∀ (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp V) × GA D T →* Module.End ℂ (WO (dblSp V) T → ℂ))
    (ω' : GA D (dblSp V) × GA D T' →* Module.End ℂ (WO (dblSp V) T' → ℂ)),
    IsWeilDatumO ψ (dblSp V) T 1 χ ω → IsWeilDatumO ψ (dblSp V) T' 1 χ ω' →
  ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
  ∀ (b : GL (Fin T.rank) (AE D)) (b' : GL (Fin T'.rank) (AE D)), StdPos d b b' →
  ∀ (μ₀ : Measure (WO V T)) (𝓕₀ : Set (WO V T)), IsCovolOne (ratL T V) μ₀ 𝓕₀ →
  ∀ (μ₁ : Measure (Mx D t (dblSp V).rank)) (𝓕₁ : Set (Mx D t (dblSp V).rank)), IsCovolOne (ratMx D _ _) μ₁ 𝓕₁ →
  ∀ (ν : Measure (Kmax T b)), ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ (m : Measure (GA D T')), m.IsHaarMeasure →
    (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsThetaFunO ψ (dblSp V) T' (ikeda ψ d μ₁ 𝓕₁ φ)) ∧
    (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
      EisPoleLEFar V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) 1) ∧
    (IsAniso T' →
      (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsThetaFunO ψ (dblSp V) T (projK ω ν φ)) ∧
      (∀ φ', IsThetaFunO ψ (dblSp V) T' φ' → ∀ g, ThetaPairConv ω' m φ' 1 g) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
        EisCoeffFar V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) (-1)
          (κ • thetaInt ω' m (ikeda ψ d μ₁ 𝓕₁ (projK ω ν φ)))) ∧
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ b₀ : GL (Fin T₀.rank) (AE D), StdPos d₀ b' b₀ →
      (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsThetaFunO ψ (dblSp V) T (projK ω ν φ)) ∧
      EisensteinContinuesFar d₀ b' ∧
      ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, ∃ (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ),
        IsRegElt ψ ω' θ τ d₀ b' zG zH P ∧
        (∀ φ', IsThetaFunO ψ (dblSp V) T' φ' → RegIntProps ψ ω' m θ τ d₀ b' zH P φ') ∧
        ∃ κ : ℂ, κ ≠ 0 ∧ ∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
          EisCoeffFar V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) (-1)
            (κ • regRes ω' m θ τ d₀ b' zH P (ikeda ψ d μ₁ 𝓕₁ (projK ω ν φ)))

namespace FirstTermFar

open GlobalTheory.Published.SiegelSectionIwasawa (relat frameLat_relat hasIw_of_good)

variable {D : D7} {T T' : HSp D} {t : ℕ}

def relatDec (d : HypDec T T' t) (l : Lvl T) (hl : l.Good) : HypDec (relat T l hl) T' t :=
  ⟨d.e, d.e', d.i₀, d.ee, d.e'e', d.e'e, d.iso, d.i₀e, d.i₀e', d.rank_add⟩

def relatDec' (d : HypDec T T' t) (l' : Lvl T') (hl : l'.Good) : HypDec T (relat T' l' hl) t :=
  ⟨d.e, d.e', d.i₀, d.ee, d.e'e', d.e'e, d.iso, d.i₀e, d.i₀e', d.rank_add⟩

theorem exists_stdPos (d : HypDec T T' t) {b' : GL (Fin T'.rank) (AE D)} (hb : IsMaj T' b') :
    ∃ (l : Lvl T) (hl : l.Good), StdPos (relatDec d l hl) l.c b' := by
  obtain ⟨l, hl, hc⟩ := GlobalTheory.RegSch.exists_good_compat D T T' t d _ (Lvl.good_frameLat T' hb)
  refine ⟨l, hl, hl.2.2, hb, ?_, hasIw_of_good _ ⟨_, l.c⟩ (Lvl.good_frameLat (relat T l hl) hl.2.2)⟩
  rw [frameLat_relat]
  exact hc

example (D : D7) : ∃ (V T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (b : GL (Fin T.rank) (AE D)) (b' : GL (Fin T'.rank) (AE D)),
    T.rank + T'.rank = 2 * V.rank ∧ T'.rank < T.rank ∧ 0 < T'.rank ∧ StdPos d b b' := by
  obtain ⟨b', hb⟩ := exists_isMaj (diagSp D 1 ![false] 1 0)
  obtain ⟨l, hl, h⟩ := exists_stdPos (hypDecThree D) hb
  exact ⟨diagSp D 2 ![false, false] 2 0, _, _, 1, _, _, _, rfl, (by decide : 1 < 3), Nat.one_pos, h⟩

end FirstTermFar

end GlobalTheory.CompanionTheory.Hypotheses₂

end
