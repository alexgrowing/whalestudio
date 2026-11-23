import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.CuspRep
open Formalism.MainNotions.N Polynomial

namespace UpperTheory.V.W

section Abstract

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}

def Resid.V0ok (r : Resid F O n) : Prop :=
  (∀ i, F.I0 ≤ (r.chib i).ker) ∧ (∀ g ∈ F.D0, ∀ i j, r.chib i g = r.chib j g) ∧ ∃ g ∈ F.D0, F.eps O (ResidueField O) g ≠ 1

def Resid.IsTeich (r : Resid F O n) (t : Fin n → F.G₀ →* Oˣ) : Prop :=
  ∀ i g, residue O (t i g) = r.chib i g ∧ t i g ^ (Nat.card (ResidueField O) - 1) = 1

variable {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B)

def UniversalOrdinaryDeterminantRing.DD : GDet n (B.B ⧸ J) F.G₀ := B.u.D.map (Ideal.Quotient.mk J)

def UniversalOrdinaryDeterminantRing.psiT (v : F.Vl) (j : Fin n) : F.Gv v →* (B.B ⧸ J)ˣ := pushCh (Ideal.Quotient.mk J) (B.u.ψ v j)

structure UniversalOrdinaryDeterminantRing.RingProps : Prop where
  fin : ((Ideal.Quotient.mk J).comp (Λ.toPair B.u : Λ.Λ →+* B.B)).Finite
  tf : ∀ a : Λ.Λ, a ≠ 0 → ∀ b : B.B, Λ.toPair B.u a * b ∈ J → b ∈ J
  polar : F.IsPolar O (B.DD J)
  O1 : ∀ v g, (B.DD J).chi (MonoidAlgebra.single (F.φ v g) 1) = ∏ j, (X - C ((B.psiT J v j g : (B.B ⧸ J)ˣ) : B.B ⧸ J))
  O2 : ∀ v g, (B.DD J).Kills (F.oEl v (B.psiT J v) g) ∧ (B.DD J).Kills (F.star O _ n (F.oEl v (B.psiT J v) g))
  O3 : ∀ u, ∀ g ∈ r.Ip u, (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) ∧
    (B.DD J).Kills (F.star O _ n (MonoidAlgebra.single g 1) - 1)
  types : ∀ t, r.IsTeich t → ∀ u, (B.DD J).comap (F.Iu u).subtype =
    GDet.ofRep (diagRep fun i => pushCh (algebraMap O (B.B ⧸ J)) ((t i).comp (F.Iu u).subtype))
  unr0 : r.V0ok → ∀ g ∈ F.I0, (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) ∧
    (B.DD J).Kills (F.star O _ n (MonoidAlgebra.single g 1) - 1)

end Abstract

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

variable (L) in

def Large (c : Coef l) : Prop := ∀ (τ : L →+* Qbar l) (x : 𝓞 L), τ x ∈ c.O

variable {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n}

variable (s n) in

abbrev HidaSetting.Wt : Type := ∀ v : Vl l L, Fin n → Emb l (s.w v) → ℤ

def HidaSetting.Wt.Incr (h : s.Wt n) : Prop := ∀ v τ, StrictMono fun j => h v j τ

namespace UniversalOrdinaryDeterminantRing

variable (B : UniversalOrdinaryDeterminantRing r)

abbrev Pt : Type := B.B →ₐ[c.O] Qbar l

variable {B}

def Pt.psi (x : B.Pt) (v : Vl l L) (j : Fin n) : Dec (F := L) (s.A v) →* (Qbar l)ˣ :=
  pushCh (x : B.B →+* Qbar l) (B.u.ψ v j)

def Pt.D (x : B.Pt) : GDet n (Qbar l) V.frame.G₀ := B.u.D.map (x : B.B →+* Qbar l)

def Pt.IsRep (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop := x.D.comap V.pr = GDet.ofRep (mat ρ)

def Pt.Arith (x : B.Pt) (h : s.Wt n) : Prop := h.Incr ∧ ∀ (v : Vl l L) (j : Fin n), IsLocAlg (s.hw v) (x.psi v j) (h v j)

def Pt.Good (x : B.Pt) (h : s.Wt n) : Prop :=
  h.Incr ∧ ∀ v : Vl l L, ∃ ph : Fin n → Ine (F := L) (s.A v) →* (Qbar l)ˣ,
    (∀ j, IsWtPart (s.hw v) (x.psi v j) (h v j) (ph j)) ∧ Function.Injective ph

variable (B) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)

def Dense : Prop := ∀ h : s.Wt n, h.Incr → ∀ b : B.B, (∀ x : B.Pt, J ≤ RingHom.ker x → x.Good h → x b = 0) → b ∈ J

def PT : Prop :=
  ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → Af.IsAutCsd ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x

def arithmeticPointPurity : Prop :=
  ∀ (x : B.Pt) (h : s.Wt n), J ≤ RingHom.ker x → x.Arith h →
    ∃ ρ : G L Ω →* GL (Fin n) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ x.IsRep ρ ∧
      ∃ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, G L Ω →* GL (Fin (d i)) (Qbar l)),
        (∀ i, 1 ≤ d i ∧ 1 ≤ m i ∧ Continuous (ρ' i)) ∧
        (∀ g, (mat ρ g).charpoly =
          ∏ i, ∏ j ∈ Finset.range (m i), (mat (Af.tw (ρ' i) (cycBar L Ω l ^ (-(j : ℤ)))) g).charpoly) ∧
        ((∀ i, m i = 1) → ∀ (w : Plc L) (b : Multiset ℂ), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → Af.FrobEig ι ρ w b →
          ∀ z ∈ b, ‖z‖ = (normV w : ℝ) ^ (((n : ℝ) - 1) / 2))

def arithmeticPointClassicality : Prop :=
  ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ → Af.IsIrr ρ →
    Af.IsAutCsd ι ρ

def TwistOk : Prop :=
  ∀ (x x' : B.Pt) (h : s.Wt n) (β : V.frame.G₀ →* (Qbar l)ˣ), J ≤ RingHom.ker x → x.Good h →
    IsOpen (β.ker : Set V.frame.G₀) → (∃ k : ℕ, β ^ l ^ k = 1) → β.comp V.frame.conj = β⁻¹ →
    (∀ u, V.frame.Iu u ≤ β.ker) → V.frame.I0 ≤ β.ker →
    x.D.IsTwist β x'.D → (∀ (v : Vl l L) (j : Fin n), x'.psi v j = x.psi v j * β.comp (V.pr.comp (Dec (F := L) (s.A v)).subtype)) → J ≤ RingHom.ker x'

structure HidaProps (Λ : LamObj r) : Prop where
  ring : B.RingProps Λ J
  dense : B.Dense J
  pt : B.PT ι J
  end1 : B.arithmeticPointPurity ι J
  end2 : B.arithmeticPointClassicality ι J
  twist : B.TwistOk J

structure Modular (Λ : LamObj r) : Prop extends B.HidaProps ι J Λ where
  p1 : B.P1core J
  p3 : B.P3core J

end UniversalOrdinaryDeterminantRing

end U

def ModU : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 1 ≤ n → ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.Modular ι J Λ

def LevEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (S' : Set (Plc (Lp L))), S'.Finite → s.S ⊆ S' →
    (∀ v ∈ S', Dec (F := Lp L) (s.A v) ≤ (resP L Ω).range) → ∃ V : s.Lev, V.S' = S'

def LamEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n),
    ∃ Λ : LamObj r, Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin (n * Module.finrank ℚ (Lp L))) c.O)

def ProModularRingExists : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n)
    (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R], Nonempty (Pair r R) → Nonempty (UniversalOrdinaryDeterminantRing r)

end UpperTheory.V.W
