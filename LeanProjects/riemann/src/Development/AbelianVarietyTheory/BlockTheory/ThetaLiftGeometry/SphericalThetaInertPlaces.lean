import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SatakeDualWeyl.StatementF

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def bcPar (n : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  Multiset.map α Finset.univ.val + Multiset.map (fun l => (α l)⁻¹) Finset.univ.val + (if Odd n then {1} else 0)

def phPar (n n' : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  (bcPar n α).map fun z => ((-1 : ℂ) ^ n')⁻¹ * z

def strPar (q t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun k : ℕ => (q : ℂ) ^ (-((t : ℤ) - 1 - 2 * (k : ℤ)))

def ThetaPar (q a b t : ℕ) (α : Fin (a / 2) → ℂ) (α' : Fin (b / 2) → ℂ) : Prop :=
  phPar b a α' = phPar a b α + strPar q t

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

open Classical in

def divInd (σ : L →+* L) (n : ℕ) (ϖ : L) (d : List ℤ) (g : Formalism.UG.GU σ n) : ℂ :=
  if ∃ k₁ k₂ : GL (Fin n) (Formalism.UG.intL L),
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (k₁ : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)).map (Formalism.UG.intL L).subtype *
          Matrix.diagonal (fun i : Fin n => ϖ ^ (d.getD i.1 0)) *
          (k₂ : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)).map (Formalism.UG.intL L).subtype
  then 1 else 0

end Local

variable {D : D7}

def IsLocalInv (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (q : ℕ)
    (x : P.adicCompletion D.host.E × (P.adicCompletion D.host.E →+* P.adicCompletion D.host.E)) : Prop :=
  Formalism.UG.IsUnramInv x.1 x.2 q ∧
    ∀ y : D.host.E, x.2 (algebraMap D.host.E (P.adicCompletion D.host.E) y) =
      algebraMap D.host.E (P.adicCompletion D.host.E) (star y)

def IsInertPrime (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = P.asIdeal

def UnramAtIdem (D : D7) (e : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, e * ((x : AE D) - 1) = (x : AE D) - 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def KAt (V : HSp D) (e : AE D) : Set (GA D V) := {k | k ∈ KsphC V ∅ ∧ SuppF V e k}

def IsVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w = v), heisO ψ S T u f = f

def IsSphOp (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V)) : Prop :=
  Hecke₂ V (KsphC V ∅) (fun _ => 1) ∅ P d R

def HeckeTransfer {X : Type} (A B : HSp D) (t : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (q : ℕ)
    (ωA : GA D A → Module.End ℂ (X → ℂ)) (ωB : GA D B → Module.End ℂ (X → ℂ)) (Vac : (X → ℂ) → Prop) : Prop :=
  ∀ (d : List ℤ) (R : Finset (GA D B)), IsSphOp B P d R →
    ∃ (N : ℕ) (c : Fin N → ℂ) (dA : Fin N → List ℤ) (RA : Fin N → Finset (GA D A)),
      (∀ j, IsSphOp A P (dA j) (RA j)) ∧
      (∀ f, Vac f → ∑ b ∈ R, ωB b f = ∑ j, c j • ∑ a ∈ RA j, ωA a f) ∧
      AllSome (IsLocalInv D P q) fun x =>
        ∀ (α : Fin (A.rank / 2) → ℂ) (α' : Fin (B.rank / 2) → ℂ), (∀ l, α l ≠ 0) → (∀ l, α' l ≠ 0) →
          ThetaPar q A.rank B.rank t α α' →
          Formalism.UG.SatU x.1 q (divInd x.2 B.rank x.1 d) α' =
            ∑ j, c j * Formalism.UG.SatU x.1 q (divInd x.2 A.rank x.1 (dA j)) α

def SphericalThetaInert : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    2 ≤ S.rank → 2 ≤ T.rank →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 D.host.E)) (ε : AF D.host.F),
      IsInertPrime D v P → (2 : 𝓞 D.host.F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal → IsPlaceIdem D v ε →
      UnramAtIdem D (algebraMap (AF D.host.F) (AE D) ε) χS → UnramAtIdem D (algebraMap (AF D.host.F) (AE D) ε) χT →
      (∀ f, IsVacAt ψ S T v f →
        ∀ k ∈ KAt S (algebraMap (AF D.host.F) (AE D) ε), ∀ k' ∈ KAt T (algebraMap (AF D.host.F) (AE D) ε),
          om (k, k') f = f) ∧
      (∀ t : ℕ, T.rank = S.rank + t →
        HeckeTransfer S T t P (Ideal.absNorm v.asIdeal) (fun a => om (a, 1)) (fun b => om (1, b)) (IsVacAt ψ S T v)) ∧
      (∀ t : ℕ, S.rank = T.rank + t →
        HeckeTransfer T S t P (Ideal.absNorm v.asIdeal) (fun a => om (1, a)) (fun b => om (b, 1)) (IsVacAt ψ S T v))

example (q : ℕ) (z : ℂ) : ThetaPar q 2 3 1 (fun _ => z) (fun _ => -z) := by
  have h3 : Odd 3 := by decide
  have h2 : ¬ Odd 2 := by decide
  have e3 : ((-1 : ℂ) ^ 3)⁻¹ = -1 := by norm_num
  have e2 : ((-1 : ℂ) ^ 2)⁻¹ = 1 := by norm_num
  simp only [ThetaPar, phPar, bcPar, strPar, h3, h2, if_true, if_false, e3, e2]
  simp [inv_neg]

example (q : ℕ) : strPar q 2 = {(q : ℂ), (q : ℂ)⁻¹} := by
  simp [strPar, Multiset.range_succ]

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces

end
