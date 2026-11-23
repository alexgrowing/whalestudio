import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SatakeDualWeyl.StatementG

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def bcPar (n : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  Finset.univ.val.map α + Finset.univ.val.map (fun l => (α l)⁻¹) + if Odd n then {1} else 0

def twPar (n n' : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  (bcPar n α).map fun z => ((-1 : ℂ) ^ n')⁻¹ * z

def strPar (q t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun l => (q : ℂ) ^ (-((t : ℤ) - 1 - 2 * (l : ℤ)))

def labInd {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (ϖ : L)
    (d : List ℤ) : Formalism.UG.GU σ n → ℂ :=
  Set.indicator {g | ∃ k₁ ∈ Formalism.UG.KU σ n, ∃ k₂ ∈ Formalism.UG.KU σ n,
    ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((k₁ : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) *
        (((k₂ : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)} 1

variable {D : D7}

def IsLocDat (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 D.host.E))
    (p : (P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) × P.adicCompletion D.host.E) : Prop :=
  (∀ x : D.host.E, p.1 (algebraMap D.host.E (P.adicCompletion D.host.E) x) =
      algebraMap D.host.E (P.adicCompletion D.host.E) (star x)) ∧
    Formalism.UG.IsUnramInv p.2 p.1 (Ideal.absNorm v.asIdeal)

def SatakeTransfer (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 D.host.E))
    (a b t : ℕ) (d : List ℤ) (c : List ℤ →₀ ℂ) : Prop :=
  AllSome (IsLocDat D v P) fun p =>
    ∀ (α : Fin (a / 2) → ℂ) (β : Fin (b / 2) → ℂ), (∀ l, α l ≠ 0) → (∀ l, β l ≠ 0) →
      twPar b a β = twPar a b α + strPar (Ideal.absNorm v.asIdeal) t →
      Formalism.UG.SatU p.2 (Ideal.absNorm v.asIdeal) (labInd p.1 b p.2 d) β =
        ∑ d' ∈ c.support, c d' * Formalism.UG.SatU p.2 (Ideal.absNorm v.asIdeal) (labInd p.1 a p.2 d') α

def InertOddResidueSetting (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  Formalism.UG.IsInertAt D.host.F D.host.E v P ∧ Odd (Ideal.absNorm v.asIdeal) ∧ 3 < Ideal.absNorm v.asIdeal

def UnramAtPlace (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D →
    (∀ v', v' ≠ v → Algebra.TensorProduct.map (evalV D.host.F v') (AlgHom.id D.host.F D.host.E)
      (finPart D (x : AE D)) = 1) →
    χ x = 1

def hypAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (GA D V) :=
  {k | k ∈ KsphC V ∅ ∧ ∃ ε, IsPlaceIdem D v ε ∧ SuppF V (algebraMap (AF D.host.F) (AE D) ε) k}

def IsSphOp (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V)) : Prop :=
  Hecke₂ V (KsphC V ∅) (fun _ => 1) ∅ P d R

def SphDatum (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ψ : AddChar (AF D.host.F) ℂ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ) : Prop :=
  IsWeilDatumO ψ S T χS χT om ∧ UnramAtPlace D χS v ∧ UnramAtPlace D χT v ∧ IsThetaFunO ψ S T f ∧
    ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w = v), heisO ψ S T u f = f

def VacFixed (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ ψ χS χT om f, SphDatum S T v ψ χS χT om f →
    ∀ k ∈ hypAt S v, ∀ k' ∈ hypAt T v, om (k, k') f = f

def TransferTargetLarge (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (t : ℕ) : Prop :=
  ∀ d R, IsSphOp T P d R →
    ∃ (c : List ℤ →₀ ℂ) (Rs : List ℤ → Finset (GA D S)),
      (∀ d' ∈ c.support, IsSphOp S P d' (Rs d')) ∧
      SatakeTransfer D v P S.rank T.rank t d c ∧
      ∀ ψ χS χT om f, SphDatum S T v ψ χS χT om f →
        ∑ b ∈ R, om (1, b) f = ∑ d' ∈ c.support, c d' • ∑ a ∈ Rs d', om (a, 1) f

def TransferSourceLarge (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (t : ℕ) : Prop :=
  ∀ d R, IsSphOp S P d R →
    ∃ (c : List ℤ →₀ ℂ) (Rs : List ℤ → Finset (GA D T)),
      (∀ d' ∈ c.support, IsSphOp T P d' (Rs d')) ∧
      SatakeTransfer D v P T.rank S.rank t d c ∧
      ∀ ψ χS χT om f, SphDatum S T v ψ χS χT om f →
        ∑ b ∈ R, om (b, 1) f = ∑ d' ∈ c.support, c d' • ∑ a ∈ Rs d', om (1, a) f

def SphericalThetaInert (D : D7) : Prop :=
  ∀ (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 D.host.E)),
    InertOddResidueSetting D v P → 2 ≤ S.rank → 2 ≤ T.rank →
      VacFixed S T v ∧
      (∀ t : ℕ, T.rank = S.rank + t → TransferTargetLarge S T v P t) ∧
      (∀ t : ℕ, S.rank = T.rank + t → TransferSourceLarge S T v P t)

end GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

end
