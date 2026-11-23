import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem

noncomputable section

namespace GlobalTheory.StringRepresentationDecomposition

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal

def epsQ (D : D7) (i : D.nd.Loc) (g : G D.host.E D.nd.Om) : Qbar (D.nd.l i) :=
  iotaOQ D.nd D.naut i ((Formalism.MainNotions.N.Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)

def IsStringRep (D : D7) (i : D.nd.Loc) (p : Part D.naut.CG)
    (R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((R g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i)))) ∧ IsSSRep R ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i R w = D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)

def CentredStringDecomposition : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ r, GoodR D.nd i r →
    ∃ R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)),
      (∀ k, IsStringRep D i (Pa.get k) (R k)) ∧
      ∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a)

def PurityStringWeight : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ (k : Fin Pa.length) (R : G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))),
      IsStringRep D i (Pa.get k) R → ∀ a < (Pa.get k).d,
      (∃ v : Fin (Pa.get k).a → Qbar (D.nd.l i), v ≠ 0 ∧ ∀ g,
        ((epsQ D i g)⁻¹ ^ a) • ((R g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a)
          (Qbar (D.nd.l i))).mulVec v = iotaOQ D.nd D.naut i (chi1 D.nd i g) • v) →
      ((Pa.get k).d : ℤ) - 1 - 2 * a = (D.R.t : ℤ) - 1

def HeckeCharEqOfLAdicRealisation : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → ∀ (i : D.nd.Loc) (χ χ' : D.naut.CG 1) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))),
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ' w) s) →
    χ = χ'

def SSList : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (n : ℕ) (ρ : Γ →* GL (Fin n) k),
    ∃ L : List (Σ m : ℕ, Γ →* GL (Fin m) k), (∀ p ∈ L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) ∧
      ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly =
        (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod

def SSRankUnique : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (L L' : List (Σ m : ℕ, Γ →* GL (Fin m) k)),
    (∀ p ∈ L, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤) → (∀ p ∈ L', 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤) →
    (∀ g, (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod =
      (L'.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod) →
    ((L.map fun p => p.1 : List ℕ) : Multiset ℕ) = ((L'.map fun p => p.1 : List ℕ) : Multiset ℕ)

def EigenCharTwist : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] (n : ℕ) (ρ : Γ →* GL (Fin n) K)
    (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (χ : Γ →* Kˣ),
    IsSSRep ρ → (∀ p ∈ L, IsSSRep p.2) →
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod) →
    (∃ v : Fin n → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).mulVec v = ((χ g : Kˣ) : K) • v) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).mulVec v = ((χ g : Kˣ) : K) • v

def ValRingModel : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsAlgClosed (IsLocalRing.ResidueField A))
      (j : A →+* Qbar l), Function.Injective j ∧ Set.range j = {x : Qbar l | ‖x‖ ≤ 1} ∧
      (∀ x : A, x ∈ IsLocalRing.maximalIdeal A ↔ ‖j x‖ < 1) ∧
      ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
        (n : ℕ) (ρ : Γ →* GL (Fin n) (Qbar l)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l))) →
        ∃ (ρ0 : Γ →* GL (Fin n) A) (P : GL (Fin n) (Qbar l)), ∀ g,
          ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)) =
            (P : Matrix (Fin n) (Fin n) (Qbar l)) * ((ρ0 g : GL _ _) : Matrix (Fin n) (Fin n) A).map j *
              ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))

def MuChar : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → ∀ (i : D.nd.Loc), HG D.nd D.naut i →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g)) →
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)

def RbEx (D : D7) : Prop := ∀ i : D.nd.Loc, HG D.nd D.naut i → ∃ rb, IsRhoBar D.nd i rb

def ResCount : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → RbEx D → ∀ (i : D.nd.Loc), HG D.nd D.naut i →
    ∀ (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i)
    (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))),
    (∀ k, IsStringRep D i (Pa.get k) (R k)) →
    (∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a)) →
    ∃ Ak : Fin Pa.length → Multiset ℕ, (∀ k, (Ak k).sum = (Pa.get k).a ∧ ∀ a ∈ Ak k, 1 ≤ a) ∧
      ∑ k, (Pa.get k).d • Ak k = D.R.r ::ₘ Multiset.replicate D.R.t 1

def Numerics : Prop :=
  ∀ (r t d n a : ℕ) (A : Multiset ℕ), 1 < r → 2 ≤ t → a < d → (d : ℤ) - 1 - 2 * a = (t : ℤ) - 1 → A.sum = n → (∀ x ∈ A, 1 ≤ x) →
    1 ≤ n → d • A ≤ r ::ₘ Multiset.replicate t 1 → n = 1 ∧ d = t

def Rest : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (A : ι → Multiset ℕ) (r : ℕ), (∀ k, 1 ≤ d k) → (∀ k, A k ≠ 0) →
    ∑ k, d k • A k = {r} → Fintype.card ι = 1 ∧ ∀ k, d k = 1 ∧ A k = {r}

def EigPd (D : D7) : Prop :=
  ∀ i : D.nd.Loc, HG D.nd D.naut i → ∀ w ∈ D.nd.S i,
      w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      ∀ rb, IsRhoBar D.nd i rb →
      ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))

def LGC (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w : PlE D.host, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → Formalism.MainNotions.SumRepresentations.At.LGCat D.nd r D.naut w

def HOneTwo (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (rb : G D.host.E D.nd.Om →* GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) (w : PlE D.host),
    w ∈ D.nd.S i → IsRhoBar D.nd i rb →
    ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) →
    ∀ e : ℤ, Formalism.MainNotions.SumRepresentations.At.HOneTwoZero D.nd i w
      (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e))

example : (2 : ℕ) • ({1} : Multiset ℕ) ≤ 2 ::ₘ Multiset.replicate 2 1 := by decide

end GlobalTheory.StringRepresentationDecomposition

end
