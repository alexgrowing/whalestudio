import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

variable (O F n) in

def IsTr {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (t : F.G0 → C) : Prop :=
  AdicCont (maximalIdeal C) t ∧ ∀ g, res O C (t g) = ∑ i, ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)

variable (O F n) in

def IsPsi {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (χ : ∀ v, Fin n → F.Gv v → C) : Prop :=
  ∀ v i, AdicCont (maximalIdeal C) (χ v i) ∧
    ∀ g, res O C (χ v i g) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O)

variable (O) in

structure Integral (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K]
    (ρ : NRep F n K) : Prop where
  tr : ∃ t : F.G0 → C, IsTr O F n t ∧ ∀ g, algebraMap C K (t g) = (ρ.r g).trace
  psi : ∃ χ : ∀ v, Fin n → F.Gv v → C, IsPsi O F n χ ∧ ∀ v i g, algebraMap C K (χ v i g) = ρ.ψ v i g
  ze : ∃ ζ : C, res O C ζ = (F.Ψ F.g0 : ResidueField O) - ((F.Ψ F.g0)⁻¹ : (ResidueField O)ˣ) ∧
    ∀ i, (ρ.r F.g0 - ρ.r (F.star F.g0)) i i = (w n i : K) * algebraMap C K ζ

variable (O) in

structure Cone (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K]
    (ρ : NRep F n K) : Prop where
  dg : ∀ g i, ∃ c : C, algebraMap C K c = ρ.r g i i ∧
    res O C c = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  cyc : ∀ L : List (F.G0 × Fin n × Fin n), (L.map fun s => w n s.2.1 - w n s.2.2).sum = 0 →
    (∃ s ∈ L, s.2.1 ≠ s.2.2) → ∃ c ∈ maximalIdeal C, algebraMap C K c = (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod
  fg : ∀ i j, (Submodule.span C (Set.range fun g => ρ.r g i j)).FG
  cont : ∀ i j (N : ℕ), IsLocallyConstant fun g =>
    (maximalIdeal C ^ N • Submodule.span C (Set.range fun g => ρ.r g i j)).mkQ (ρ.r g i j)
  psi : ∃ χ : ∀ v, Fin n → F.Gv v → C, IsPsi O F n χ ∧ ∀ v i g, algebraMap C K (χ v i g) = ρ.ψ v i g

variable (O) in

def IsResMap (C : Type) [CommRing C] [IsLocalRing C] [Algebra O C] (f : ResidueField O →+* ResidueField C) : Prop :=
  ∀ a, f (residue O a) = residue C (algebraMap O C a)

namespace Space

variable (S : Space O F n)

def x0 : Ideal S.A := S.mB.map (S.inc : S.B →+* S.A)

def td (η : Ideal S.A) : Cardinal := Algebra.trdeg (S.B ⧸ η.comap (algebraMap S.B S.A)) (S.A ⧸ η)

namespace Loc

variable {S} {x : Ideal S.A} (L : S.Loc x)

def b : S.B →+* L.R := (L.ι : S.A →+* L.R).comp (S.inc : S.B →+* S.A)

def Pres : Prop :=
  ∃ (N N' : ℕ) (p : MvPowerSeries (Fin N) L.O' →ₐ[L.O'] L.R) (f : Fin N' → MvPowerSeries (Fin N) L.O'),
    N = N' + (n * F.d + 1) ∧ Function.Surjective p ∧ RingHom.ker p = Ideal.span (Set.range f)

def par (a g : ℕ) : Fin a ⊕ Fin g → ZMod 2 := Sum.elim (fun _ => 0) fun _ => 1

structure EPres where
  a : ℕ
  b : ℕ
  g : ℕ
  p : MvPowerSeries (Fin a ⊕ Fin g) L.O' →ₐ[L.O'] L.R
  Fe : Fin b → MvPowerSeries (Fin a ⊕ Fin g) L.O'
  Go : Fin g → MvPowerSeries (Fin a ⊕ Fin g) L.O'
  num : a = b + (n * F.d + 1)
  surj : Function.Surjective p
  ker : RingHom.ker p = Ideal.span (Set.range Fe ∪ Set.range Go)
  even : ∀ i, Fe i ∈ wtPart L.O' (par a g) 0
  odd : ∀ i, Go i ∈ wtPart L.O' (par a g) 1
  min : ∀ f ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) f ∈ maximalIdeal L.O'
  ent : ∀ s i j, L.ρ.r s i j ∈ (wtPart L.O' (par a g) ((w n i - w n j : ℤ) : ZMod 2)).map p.toLinearMap
  base : ∀ y : S.B, L.b y ∈ (wtPart L.O' (par a g) 0).map p.toLinearMap
  ee : L.ρ.ee = Ideal.span (Set.range fun i => p (MvPowerSeries.X (.inr i)))

end Loc

end Space

def Chained {R : Type} [CommRing R] (I : Ideal R) (D : ℕ) : Prop :=
  (∀ P ∈ I.minimalPrimes, ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P)) ∧
  ∀ P ∈ I.minimalPrimes, ∀ Q ∈ I.minimalPrimes, Relation.ReflTransGen
    (fun P Q => P ∈ I.minimalPrimes ∧ Q ∈ I.minimalPrimes ∧ (D : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (P ⊔ Q))) P Q

structure Space.Loc.Sharp {S : Space O F 3} {x : Ideal S.A} (L : S.Loc x) (I : Ideal L.R) : Prop where
  triv : ¬ S.u.ee ≤ x → I = ⊥
  off : ∀ P : Ideal L.R, P.IsPrime → ¬ L.ρ.ee ≤ P → I ≤ P
  chained : Chained I (3 * F.d + 1)
  dich : ∀ P ∈ I.minimalPrimes, L.ρ.TI P ∨ Thick L.ρ P

end UpperTheory.V.Fr
