import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCx GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo (Integ IsFnL)
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

instance algAt (S : Setup A n p) (w : Plc E) : Algebra S.G.F (w.adicCompletion E) := inferInstanceAs (Algebra E (w.adicCompletion E))

def Spl (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ) : Type := {w : Plc E // IsSplitAt w ∧ (p : 𝓞 E) ∉ w.asIdeal}

abbrev fac {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Spl E p) : Loc S.G.GAf (GL (Fin n) (w.1.adicCompletion E)) :=
  T.at hc w.1 w.2.1 w.2.2

structure Half (q : ℕ) (W : Finset (Spl E p)) : Prop where
  above : ∀ w ∈ W, (q : 𝓞 E) ∈ w.1.asIdeal
  all : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → ∃ w ∈ W, w.1 = u ∨ cj w.1 = u
  apart : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → GlobalTheory.Cong.Apart w.1 w'.1

def InSc {k : Type} [Field k] {n : ℕ} (X : Set (GL (Fin n) k)) (x : GL (Fin n) k) : Prop :=
  ∃ (c : kˣ) (y : GL (Fin n) k), y ∈ X ∧ x = GeneralLinearGroup.scalar (Fin n) c * y

def PlEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (T : Tr S) (hc : LocComm)
    (w : Spl E p), ∃ P : Pl S.G (w.1.adicCompletion E), ∀ g, P.at g = ((fac T hc w).pr g : Matrix (Fin n) (Fin n) (w.1.adicCompletion E))

def SplitEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Lv : G.Level) (k : Type) [Field k] [TopologicalSpace k] [Algebra G.F k] (P : Pl G k)
    (L : Loc G.GAf (GL (Fin G.n) k)), (∀ g, P.at g = (L.pr g : Matrix (Fin G.n) (Fin G.n) k)) →
    ∀ Kw : Subgroup (GL (Fin G.n) k), IsOpen (Kw : Set (GL (Fin G.n) k)) → IsCompact (Kw : Set (GL (Fin G.n) k)) →
    L.Fact Lv.K.toSubgroup Kw → ∃ (_ : TopologicalSpace L.pr.ker) (_ : IsTopologicalGroup L.pr.ker) (_ : T2Space L.pr.ker)
      (S : Split P Lv.K.toSubgroup L.pr.ker), ∀ g h, S.e.symm (g, h) = L.loc g * h

def AdmCusp : Prop :=
  ∀ (X : Type) [Group X] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (Ty : TyLev X (GL (Fin n) k)),
    IsOpen (Ty.J : Set (GL (Fin n) k)) → IsCompact (Ty.J : Set (GL (Fin n) k)) → IsOpen (Ty.ψ.ker : Set Ty.J) →
    (∀ (σ : SmIrr (GL (Fin n) k)) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) →
    ∀ f, Ty.admitted f → ∀ h : X, Ty.L.pr h = 1 → NoConst fun g => f (Ty.L.loc g * h)

def IwInv : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : GL (Fin n) k),
    ∃ φ ∈ Hecke ℂ (GlobalTheory.SmGL.iwahori k (Fin n)),
      conv (GlobalTheory.SmGL.iwahori k (Fin n)) φ (Formalism.UG.dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) t) =
        Formalism.UG.dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) 1

def RegOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (T : Tr S) (hc : LocComm)
    (q : ℕ), q.Prime → q ≠ p → ∀ W : Finset (Spl E p), Half q W → ∀ g : S.G.GAf,
    (∀ w ∈ W, ((fac T hc w).pr g : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).charpoly.Separable) → GlobalTheory.LKCx.RegAf S.G g

structure Data {S : Setup A n p} (T : Tr S) (hc : LocComm) (w₀ : Spl E p) (q : ℕ) (W : Finset (Spl E p))
    (Ty : TyLev S.G.GAf (GL (Fin n) (w₀.1.adicCompletion E))) : Prop where
  L_eq : Ty.L = fac T hc w₀
  prime : q.Prime
  ne : q ≠ p
  good : A.Good q
  off : (q : 𝓞 E) ∉ w₀.1.asIdeal
  half : Half q W
  iw : ∀ w ∈ W, (fac T hc w).Fact Ty.K (GlobalTheory.SmGL.iwahori (w.1.adicCompletion E) (Fin n))
  int : ∀ k ∈ Ty.K, Integ S.L k

def Away {S : Setup A n p} (T : Tr S) (hc : LocComm) {w₀ : Spl E p} (W : Finset (Spl E p))
    (Ty : TyLev S.G.GAf (GL (Fin n) (w₀.1.adicCompletion E))) : Submodule ℂ (S.G.GAf → ℂ) :=
  Submodule.span ℂ {f | ∃ h, Ty.L.pr h = 1 ∧ (∀ w ∈ W, (fac T hc w).pr h = 1) ∧ f = Ty.tf h}

def AuxiliaryPrimeFunction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (T : Tr S) (hc : LocComm)
    (w₀ : Spl E p) (q : ℕ) (W : Finset (Spl E p)) (Ty : TyLev S.G.GAf (GL (Fin n) (w₀.1.adicCompletion E))), Data T hc w₀ q W Ty →
    ∃ u ∈ Hecke ℂ Ty.K₀, ∃ u' ∈ Hecke ℂ Ty.K₀, conv Ty.K₀ (Ty.tf 1) u = u ∧ conv Ty.K₀ u (Ty.tf 1) = u ∧ conv Ty.K₀ u' u = Ty.tf 1 ∧
      (∀ f ∈ Away T hc W Ty, conv Ty.K₀ u f = conv Ty.K₀ f u) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ X : ∀ w : Spl E p, Set (GL (Fin n) (w.1.adicCompletion E)),
        (∀ w ∈ W, ∀ x ∈ X w, (x : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).charpoly.Separable ∧
          ∀ a, InSc (GlobalTheory.SmGL.iwahori (w.1.adicCompletion E) (Fin n) : Set _) a → a * x ∈ X w) ∧
        ∀ g, powFn Ty.K₀ u (Ty.tf 1) m g ≠ 0 → Integ S.L g⁻¹ ∧ ∀ w ∈ W, (fac T hc w).pr g ∈ X w

def SpecTr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p), S.G.a = 1 →
    ∀ (T : Tr S) (hc : LocComm) (w₀ : Spl E p) (q : ℕ) (W : Finset (Spl E p))
    (Ty : TyLev S.G.GAf (GL (Fin n) (w₀.1.adicCompletion E))), Data T hc w₀ q W Ty →
    ∀ (N : ℕ) (Lv : S.G.Level), Lv.K.toSubgroup = S.L.KN N → Ty.K₀ = S.L.KN N →
    (∃ Kw : Subgroup (GL (Fin n) (w₀.1.adicCompletion E)), IsOpen (Kw : Set (GL (Fin n) (w₀.1.adicCompletion E))) ∧
      IsCompact (Kw : Set (GL (Fin n) (w₀.1.adicCompletion E))) ∧ Ty.L.Fact Ty.K₀ Kw) →
    IsOpen (Ty.J : Set (GL (Fin n) (w₀.1.adicCompletion E))) → IsCompact (Ty.J : Set (GL (Fin n) (w₀.1.adicCompletion E))) →
    (∀ (σ : SmIrr (GL (Fin n) (w₀.1.adicCompletion E))) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) →
      GlobalTheory.SmGL.IsCuspidal σ.ρ) →
    ∀ (lam : (S.D.F →+* ℂ) → Fin S.G.n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ξ : Representation ℂ (S.G.Cˣ × ℚˣ) V), IsWt S.L lam ξ →
    ∀ (J : Type) (ψ : J → S.G.GAf → ℂ) (θ : J → ℂ), (∀ j, ψ j ∈ Hecke ℂ Ty.K₀) →
      (∀ j, conv Ty.K₀ (ψ j) (Ty.tf 1) ∈ Away T hc W Ty) →
      (∀ j j', conv Ty.K₀ (ψ j) (conv Ty.K₀ (ψ j') (Ty.tf 1)) = conv Ty.K₀ (ψ j') (conv Ty.K₀ (ψ j) (Ty.tf 1))) →
      (∀ j a, ψ j a ≠ 0 → ∀ w ∈ W, InSc (GlobalTheory.SmGL.iwahori (w.1.adicCompletion E) (Fin n) : Set _) ((fac T hc w).pr a)) →
      HasEig S.G ξ Ty.K₀ ψ θ (Ty.tf 1) → ∃ f, IsFnL S.L N f ∧ Spec S.L lam (S.L.KN N) ψ θ f

end UpperTheory.Gal.Spc
