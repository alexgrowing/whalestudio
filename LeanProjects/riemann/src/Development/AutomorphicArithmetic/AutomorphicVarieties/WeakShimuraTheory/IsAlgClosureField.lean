import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

instance isAlgClosure_field (F : IntermediateField ℚ Ω) : IsAlgClosure F Ω where
  isAlgClosed := IsAlgClosure.isAlgClosed ℚ
  isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := ℚ) F

structure Link (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) where
  s : W.HidaSetting l T.L Ω
  V : s.Lev
  hV : V.S' = s.S
  noMu : ¬ ∃ ζ : T.L, IsPrimitiveRoot ζ l
  large : W.Large T.L c'
  e : W.Vl l T.L ≃ T.ι
  hA : ∀ v : W.Vl l T.L, s.A v = T.pl (e v)
  κ : G T.L Ω →* c'.Oˣ
  β : G T.L Ω →* c'.Oˣ
  t : G T.L Ω →* Multiplicative ℤ_[l]
  κ_cont : AdicCont (maximalIdeal c'.O) fun g => (κ g : c'.O)
  β_cont : AdicCont (maximalIdeal c'.O) fun g => (β g : c'.O)
  t_cont : Continuous t
  β_t : t.ker ≤ β.ker
  β_red : ∀ g, residue c'.O (β g) = 1
  conj : ∀ g g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ →
    (κ g * κ g' : c'.O) * inc h (D.th (resQ T.L g)) * chiO T.L Ω l c'.O g ^ 3 = 1 ∧ β g * β g' = 1 ∧ t g * t g' = 1
  t_unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.L) A ≤ t.ker
  unr : ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp T.L)), IsPlaceOver A v → v ∉ s.S → ∀ g ∈ Ine (F := T.L) A,
    κ g = 1 ∧ D.rbar (resQ T.L g) = 1
  tame : ∃ m : ℕ, l.Coprime m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A, κ g ^ m = 1
  mu : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (s.A v)), g ∈ V.frame.mu v → κ g = 1 ∧ t g = 1
  cyc : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (a b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ g ∈ Ine (F := T.L) A,
    (κ g * chiO T.L Ω l c'.O g ^ (-a)) ^ k = 1 ∧ (β g ^ 2 * chiO T.L Ω l c'.O g ^ (-b)) ^ k = 1
  r : W.Resid V.frame c'.O 4
  chib : ∀ i (g : G T.L Ω), (r.chib i (V.pr g) : ResidueField c'.O) = residue c'.O (κ g * inc h (chi D T.pr i (resQ T.L g)))
  psib : ∀ (v : W.Vl l T.L) i (g : Dec (F := T.L) (s.A v)), r.psib v i g = r.chib i (V.pr g)
  th : ∀ v i, r.th v i = 1
  v0 : r.V0ok

namespace Link

variable {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h))

def IsPhi (n : ℕ) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B) : Prop :=
  (∀ g : G T.L Ω, (B.u.D.chi (MonoidAlgebra.single (K.V.pr g) 1)).map (φ : B.B →+* X.B) =
    (X.cp (resLe T.F_le g)).scaleRoots (algebraMap c'.O X.B (K.κ g * K.β g ^ n))) ∧
  ∀ (v : W.Vl l T.L) (i : Fin 4) (g : Dec (F := T.L) (K.s.A v)),
    φ (B.u.ψ v i g) = algebraMap c'.O X.B (K.κ g * K.β g ^ n) * X.ψ (K.e v) i (resLe T.F_le g)

end Link

structure UIn : Prop where
  coh : CohomologyHyp
  pr : Af.HypothesesH
  modU : W.ModU
  lev : W.LevEx
  lam : W.LamEx
  b0 : W.ProModularRingExists

end UpperTheory.V.Ws

end
