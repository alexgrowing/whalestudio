import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjStable

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing

structure Dat3 (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] where
  η : GQ l →* ℤˣ
  Ψ : GQ l →* Oˣ
  τ : GQ l →* Oˣ
  e : ℕ
  Kv : FinExt l
  odd : l ≠ 2
  e_pos : 1 ≤ e
  η_ker : ∀ g, η g = 1 ↔ g ∈ GK Kv
  η_unr : ∀ g ∈ Iq l, η g = 1
  τ_open : IsOpen (τ.ker : Set (GQ l))
  Ψ_cont : AdicCont (maximalIdeal O) fun g => (Ψ g : O)
  Ψ_I : ∀ g ∈ Iq l, Ψ g = cycA l l O g ^ e * τ g

def hodge0 (e : ℕ) (i : ℤ) : ℕ := if i = -(e : ℤ) ∨ i = 0 ∨ i = e then 1 else 0

namespace Dat3

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)

def HL : Subgroup (GQ l) := D.η.ker ⊓ D.τ.ker

def rz (A : Type) [CommRing A] [Algebra O A] : GQ l →* GG 3 A := (GG.map (algebraMap O A)).comp (r0 D.η D.Ψ)

section Types

variable {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]

def IsType (r : GQ l →* GG 3 B) : Prop :=
  ∃ ρ : ↥(GK D.Kv) →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧
    PotCrysType D.Kv (colRep ρ) 3 (hodge0 D.e)
      fun γ => algebraMap O B ((D.τ γ : O) + 1 + (((D.τ γ)⁻¹ : Oˣ) : O))

def IsLCr (r : GQ l →* GG 3 B) : Prop :=
  ∃ ρ : ↥D.HL →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧ IsCr D.HL.subtype (colRep ρ)

variable {E : Type} [CommRing E] [Algebra O E] (π : B →+* E)

structure InDcrAt (r₁ : GQ l →* GG 3 E) (r : GQ l →* GG 3 B) : Prop where
  mult : HasMult D.η r
  red : (GG.map π).comp r = r₁
  cont : ∀ a b, QCont l fun g => (r g).mat a b
  cr : D.IsLCr r

abbrev InDcr (r : GQ l →* GG 3 B) : Prop := D.InDcrAt π (D.rz E) r

structure InDtri (r : GQ l →* GG 3 B) : Prop extends D.InDcrAt π (D.rz E) r where
  tri : ∀ g a b, wt a b < 0 → (r g).mat a b = 0

def InDord (r : GQ l →* GG 3 B) : Prop :=
  ∃ (u : GQ l →* GG 3 B) (n : GL (Fin 3) B), D.InDtri π u ∧ CongOne (RingHom.ker π) n ∧
    (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) B) - 1) a b = 0) ∧ r = conjBy n u

end Types

abbrev Univ : Type 1 := U3.Univ (GCond.noCondition O D.η D.Ψ)

section Ord

open Polynomial

def IsInertiaInfiniteCyclotomic (s : GQ l) : Prop := s ∈ D.HL ∧ s ∈ Iq l ∧ ¬ IsOfFinOrder (cyc l l s)

def IsFr (σ : GQ l) : Prop :=
  (∃ h : σ ∈ D.HL, ((Iq l).comap D.HL.subtype ⊔ Subgroup.zpowers (⟨σ, h⟩ : ↥D.HL)).topologicalClosure = ⊤) ∧
    ∃ (σ₀ : GQ l) (m : ℕ), IsFrob σ₀ ∧ 1 ≤ m ∧ (σ₀ ^ m)⁻¹ * σ ∈ Iq l

def s0 : GQ l := Classical.epsilon (IsInertiaInfiniteCyclotomic D)

def fr : GQ l := Classical.epsilon (IsFr D)

def cc (a : Fin 3) : O :=
  (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 1) (s0 D)) *
    (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 2) (s0 D))

section Eq

variable {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C)

def sh (a : Fin 3) (s : GQ l) : Matrix (Fin 3) (Fin 3) C :=
  (r s).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))

def ordIdeal : Ideal C :=
  Ideal.span ({x | ∃ s ∈ D.HL ⊓ Iq l, ∃ i : ℕ, x = ((r s).mat.charpoly -
      ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i} ∪
    {x | ∃ s : Fin 3 → GQ l, (∀ a, s a ∈ D.HL ⊓ Iq l) ∧ ∃ i j,
      x = (sh D r 0 (s 0) * sh D r 1 (s 1) * sh D r 2 (s 2)) i j})

def tr (a : Fin 3) : C := (sh D r (a + 1) (s0 D) * sh D r (a + 2) (s0 D) * (r (fr D)).mat).trace

def dd (a : Fin 3) : C :=
  algebraMap O C (cc D (a + 1)) * tr D r a - algebraMap O C ((cycA l l O (fr D) : Oˣ) * cc D a) * tr D r (a + 1)

def del : C := (l : C) * dd D r 0 * dd D r 1

end Eq

end Ord

variable (U : D.Univ)

def IY : Ideal U.R where
  carrier := {a | ∃ n : ℕ, del D U.r.hom ^ n * a ∈ ordIdeal D U.r.hom}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have e : del D U.r.hom ^ (m + n) * (a + b) = del D U.r.hom ^ n * (del D U.r.hom ^ m * a) +
        del D U.r.hom ^ m * (del D U.r.hom ^ n * b) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)
  smul_mem' := by
    rintro c a ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ hn

def Icr : Ideal U.R := (IY D U).radical

def primesAt0 : Set (Ideal U.R) :=
  {P | P ∈ (D.Icr U).minimalPrimes ∧ ∀ x : U.R →ₐ[O] O, push x U.r.hom = r0 D.η D.Ψ → P ≤ RingHom.ker x}

def It : Ideal U.R := sInf (D.primesAt0 U)

abbrev Rt : Type := U.R ⧸ D.It U

def On {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C) : Prop :=
  ∃ f : U.R →ₐ[O] C, push f U.r.hom = r ∧ D.It U ≤ RingHom.ker f

def PtsCr (J : Ideal U.R) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B),
    J ≤ RingHom.ker f → D.IsLCr (push f U.r.hom)

def CrPts (J : Ideal U.R) : Prop :=
  ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ f : U.R →ₐ[O] B,
    D.InDcr (π : B →+* E) (push f U.r.hom) → J ≤ RingHom.ker f

end Dat3

structure IsCompl {O R E σ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field E] [Algebra O E]
    (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries σ E) : Prop where
  ker : RingHom.ker φ = I
  const : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)
  dense : ∀ (N : ℕ) (f : MvPowerSeries σ E), ∃ (a : R) (c : O), c ≠ 0 ∧
    c • f - φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N
  inj : ∀ (N : ℕ) (a : R), φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N →
    ∃ c : O, c ≠ 0 ∧ c • a ∈ RingHom.ker x ^ N ⊔ I

def DualDef {G E : Type} [Group G] [CommRing E] (r : G →* GG 3 E) (γ : G → Matrix (Fin 3) (Fin 3) E)
    (r' : G →* GG 3 (DualNumber E)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ ∀ a b, (r' g).mat a b = ⟨(r g).mat a b, (γ g * (r g).mat) a b⟩

example (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hc : AdicCont (maximalIdeal ℤ_[l]) fun g => (cycA l l ℤ_[l] g : ℤ_[l])) :
    Dat3 l ℤ_[l] where
  η := 1
  Ψ := cycA l l ℤ_[l]
  τ := 1
  e := 1
  Kv := botExt l
  odd := hl
  e_pos := le_rfl
  η_ker g := by simp [GK, botExt]
  η_unr _ _ := rfl
  τ_open := by simp
  Ψ_cont := hc
  Ψ_I g _ := by simp

end UpperTheory.V.Loc
