import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DivMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi

section Lin

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

def glIwa : Iwa (GL (Fin n) k) := (glData k n).toIwa (glAx k n)

def piIwa {σ : Type} [Finite σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)) : Iwa (∀ v, G v) :=
  (piData I).toIwa (piAx σ G I)

variable {k n}

abbrev PS (ω : Fin n → kˣ →* ℂˣ) := prinSeries fun i => ω i * absPow k (((n : ℂ) - 1) / 2)

def psEig (ω : Fin n → kˣ →* ℂˣ) (j : ℕ) : ℂ :=
  ∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j, (ω i (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹

def IsInvOn (φ : (glIwa k n).T →* ℂˣ) (ω : Fin n → kˣ →* ℂˣ) : Prop := ∀ i (y : Uo k), φ (eT k n i y) = (ω i y)⁻¹

def Distinct {C : Type} [Monoid C] (φ : (glIwa k n).T →* C) : Prop := ∀ i j, i ≠ j → ∃ y, φ (eT k n i y) ≠ φ (eT k n j y)

def invPart {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (c : ℕ)
    (φ : (glIwa k n).T →* ℂˣ) : Submodule ℂ V :=
  ⨅ j : ℕ, ((glIwa k n).eig π c φ).map ((glIwa k n).uOp π (glIwa k n).z ^ j)

def sphOp {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] (π : Representation A (GL (Fin n) k) V) (j : ℕ) :
    Module.End A V := dc π (KO k (Fin n)) (KO k (Fin n)) (al k n j)

end Lin

def heckePol {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) : A[X] :=
  ∑ j ∈ Finset.range (n + 1), C ((-1) ^ j * (q : A) ^ (j * (j - 1) / 2) * a j) * X ^ (n - j)

section Gal

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def algPow (w : HeightOneSpectrum (𝓞 L)) (h : (L →+* Qbar l) → ℤ) (y : w.adicCompletion L) : Qbar l :=
  ∏ᶠ j : {j : w.adicCompletion L →+* Qbar l // Continuous j}, j.1 y ^ h (j.1.comp (algebraMap L (w.adicCompletion L)))

variable (L l n) in

abbrev Wt : Type := (L →+* Qbar l) → DomWeight n

omit [NumberField L] in

def lowW (lam : Wt L l n) (j : Fin n) (τ : L →+* Qbar l) : ℤ := (lam τ).w j.rev

omit [NumberField L] in

def htW (lam : Wt L l n) (j : Fin n) (τ : L →+* Qbar l) : ℤ := lowW lam j τ + (j : ℕ)

variable (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w)

def DRat (r : Dec (F := L) A →* GL (Fin n) (Qbar l)) (HT : (L →+* Qbar l) → Multiset ℤ) (P : Weil h → ℂ[X]) : Prop :=
  ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l L Ω (Dec (F := L) A) O)
    (hj : GlobalTheory.Pst.Induces Bw), IsdRAt (Loc.PP l) Bw r ∧
      (∀ (τ : L →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP l) Bw r τ (HT τ)) ∧
      ∀ s, (wdAt (Loc.PP l) ι Bw h hj r).charPol s = P s

def AtL (r : Dec (F := L) A →* GL (Fin n) (Qbar l)) (lam : Wt L l n) (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) : Prop :=
  ∀ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) →
    (∀ i j, i ≠ j → ∃ y : Uo (w.adicCompletion L), ω i y ≠ ω j y) → Nonempty (σ.ρ.Equiv (PS ω)) →
  ∀ rc, IsRec h rc → Lev.AbW (rc (algNorm σ)) → DRat ι h r (fun τ => Finset.univ.val.map fun j => htW lam j τ) fun s => (rc (algNorm σ)).charPol s

omit [NumberField L] [IsAlgClosure L Ω] in
variable (A) in

def PotCrys (r : Dec (F := L) A →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l L Ω (Dec (F := L) A) O),
    GlobalTheory.Pst.Induces Bw → IsPotCrysAt (Loc.PP l) Bw r

variable {h} in

def OnArt {C : Type} [Monoid C] (a : Weil h →* (w.adicCompletion L)ˣ) (ψ : Dec (F := L) A →* C)
    (S : Set (w.adicCompletion L)ˣ) (f : (w.adicCompletion L)ˣ → C) : Prop :=
  ∀ (s : Weil h) (g : Dec (F := L) A), (g : G L Ω) = (s : G L Ω) → a s ∈ S → ψ g = f (a s)

variable {h} in

structure OrdChar (a : Weil h →* (w.adicCompletion L)ˣ) (ω : (w.adicCompletion L)ˣ →* ℂˣ) (hh : (L →+* Qbar l) → ℤ)
    (ψ : Dec (F := L) A →* (Qbar l)ˣ) : Prop where
  smooth : IsSmoothChar ω
  cont : Continuous ψ
  val : OnArt a ((Units.coeHom _).comp ψ) Set.univ fun x => ι.symm (ω x) * algPow w (-hh) (x : w.adicCompletion L)

def IsTypeWD (χ : Fin n → Ine (F := L) A →* ℂˣ) (x : WD h) : Prop :=
  ∃ b : WDRep h (Fin n → ℂ), WD.mk b = x ∧ b.N = 0 ∧
    ∀ s : ↥(Ine (F := L) A), b.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (χ i s : ℂ))

end Gal

def OrdFlag : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a →
    ∀ (r : Dec (F := L) A →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (hh : Fin n → (L →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) →
    ∀ (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ),
      (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) → (∀ i j, i ≠ j → ∃ y : Uo (w.adicCompletion L), ω i y ≠ ω j y) →
      DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) →
      W.HasFlag r ψ ∧ PotCrys A r

def FlagWD : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a →
    ∀ (r : Dec (F := L) A →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (hh : Fin n → (L →+* Qbar l) → ℤ) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ)
      (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ), (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) → W.HasFlag r ψ →
      ∀ HT P, DRat ι h r HT P → DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) fun s => ∏ j, (X - C (ω j (a s) : ℂ))

end UpperTheory.V.Hi
