import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.HookKeyOrderGeOne

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def topStart (X : Loc) (j : Fin (numSeg X.TT)) : X.TT := ⟨segStart X.TT j, (start_mem X.TT j).1⟩

abbrev RHH (O : Type) [CommRing O] [IsDomain O] (X : Loc) := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)

def kSkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : RHH O X :=
  ∑ a : Fin (X.m + 1), MvPolynomial.X ((topStart X j, true), a) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), a)

def kWkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (c : Fin (X.m + 1)) : RHH O X :=
  MvPolynomial.X ((topOdd X j i, true), c) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
    MvPolynomial.X ((topOdd X j i, true), 0) * MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ (segDists X.TT j).get i)

def locC (O : Type) [CommRing O] [IsDomain O] (X : Loc) (c : Fin (X.m + 1)) : RHH O X :=
  ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ segG X.TT j - 1)

def locR (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j0 : Fin (numSeg X.TT)) : RHH O X :=
  MvPolynomial.X ((topStart X j0, true), 0) * ∏ c : Fin X.m, locC O X c.succ

def CoarseMultiplicityBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      (∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1) ∧
      liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
        S.w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
              MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) ∧
      ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
        S.w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) •
            (MvPolynomial.X ((topOdd X j i, true), 0) *
              MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X)

def LocalBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    (∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1) ∧
    ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        S.w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X)

def AsmRTAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  CoarseMultiplicityBoundAtIdentity → LocalBoundAtIdentity → RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RestAsmRT : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restRawTail1_of (h3 : CoarseMultiplicityBoundAtIdentity) (h4 : LocalBoundAtIdentity) (hA : RestAsmRT) : RestRawTail1 :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => h h3 h4) hA

section Fac

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

structure IsFac (w : O) (f : RHH O X) (o : ℕ) (sg : RHH O X) : Prop where
  inA : InA f
  ord : ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f o
  sym : InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) (o + 1)
  sgInt : InA sg

theorem isGLW_one' (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF X.p X.n')) := by
  unfold IsGLW
  rw [Matrix.det_one]
  exact isUnit_one

theorem IsFac.mul {w : O} {f f' sg sg' : RHH O X} {o o' : ℕ} (h : IsFac w f o sg) (h' : IsFac w f' o' sg') :
    IsFac w (f * f') (o + o') (sg * sg') where
  inA := by
    have := inWj_mul ((inA_iff_wj w).1 h.inA) ((inA_iff_wj w).1 h'.inA)
    exact (inA_iff_wj w).2 this
  ord := fun g hg => inWjRg_mul (h.ord g hg) (h'.ord g hg)
  sym := by
    have e : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (f * f') - (w ^ (o + o')) • (sg * sg') =
        (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) *
            liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' +
          ((w ^ o) • sg) * (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' - (w ^ o') • sg') := by
      rw [map_mul, pow_add, mul_smul_mul_comm]
      ring
    rw [e]
    have a1 := inWj_mul h.sym (h'.ord 1 (isGLW_one' _))
    have a2 := inWj_mul (wj_smul_pow ((inA_iff_wj w).1 h.sgInt) o) h'.sym
    have e1 : o + 1 + o' = o + o' + 1 := by ring
    have e2 : 0 + o + (o' + 1) = o + o' + 1 := by ring
    rw [e1] at a1
    rw [e2] at a2
    exact (wjSub w (o + o' + 1)).add_mem a1 a2
  sgInt := by
    have := inWj_mul ((inA_iff_wj w).1 h.sgInt) ((inA_iff_wj w).1 h'.sgInt)
    exact (inA_iff_wj w).2 this

end Fac

end Formalism.MainNotions.ColumnSystems.Pf
