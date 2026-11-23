import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.HeckeSp

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Pts

variable {X : Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

def formPts (C : Col.CoefPk X n (Col.DecoSet X.E n ST SG)) (Λ : Col.LevFam X.E X.K n SG) :
    Col.DecoPts (Col.formGSD C Λ) X.E n ST SG where
  pts := Equiv.refl _
  hom := Col.FormG.incl Λ
  pts_smul := fun _ _ => rfl

end Pts

section Off

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def offSet (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    Set (HeightOneSpectrum (𝓞 E)) :=
  {P | conjIdeal (K := E) P.asIdeal ≠ P.asIdeal ∧
    P ∉ S0 ∪ (↑ST : Set (HeightOneSpectrum (𝓞 E))) ∪ (↑SG : Set (HeightOneSpectrum (𝓞 E))) ∧
    ∀ Q ∈ S0 ∪ (↑ST : Set (HeightOneSpectrum (𝓞 E))) ∪ (↑SG : Set (HeightOneSpectrum (𝓞 E))),
      Q.asIdeal ≠ conjIdeal (K := E) P.asIdeal}

def offSub (ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    Set (Col.LevOff ST SG S0) :=
  {P | P.1 ∈ offSet ST SG' S0}

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
  {ST SG' : Finset (HeightOneSpectrum (𝓞 E))}

def heckeCSD (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG') (SG : Finset (HeightOneSpectrum (𝓞 E)))
    (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    offSub ST SG SG' S0 × ℕ → Module.End K (S.toCSD h).Forms :=
  fun x => (S.res h).conj (Col.heckeFam c S0 (⟨x.1.1.1, x.1.2⟩, x.2))

end Off

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

def TupF (TU : Finset (Tup X.F X.E X.K S)) : Type := {τ : Tup X.F X.E X.K S // τ = mu0 X.F X.E X.K S ∨ τ ∈ TU}

def mu0F (TU : Finset (Tup X.F X.E X.K S)) : TupF TU := ⟨mu0 X.F X.E X.K S, Or.inl rfl⟩

theorem tupF_finite (TU : Finset (Tup X.F X.E X.K S)) : Finite (TupF TU) := by
  have h : ({τ | τ = mu0 X.F X.E X.K S ∨ τ ∈ TU} : Set (Tup X.F X.E X.K S)).Finite :=
    (TU.finite_toSet.insert (mu0 X.F X.E X.K S)).subset (fun τ hτ => by simpa using hτ)
  exact h.to_subtype

def colIn (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) :
    FamIn X.K (Col.G0 X.E Pr.vGs R.r) (Col.LevOff ∅ Pr.vGs S0) (TupF TU) R.m where
  v0 := v0
  μ0 := mu0F TU
  X := Xg
  r := R.r
  t := R.t
  q := fun P => Col.SplitOff.q P
  muVal := fun j τ P => Ch.muVal j P.1 * xiVal τ.1 P.1
  etaVal := fun P => Ch.etaVal P.1
  ok := fun τ => offSub ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0
  MtildeCSD := fun τ => Col.MtildeKCSD W Ch sel τ.1 (Col.mtildeKOk W Ch sel τ.1 hX)
  leftGroupActionRight := fun τ => Col.g0Act W Ch sel τ.1 (Col.mtildeKOk W Ch sel τ.1 hX)
  heckeR := fun τ => heckeCSD (Col.mtildeKGSD W Ch sel τ.1) (Col.mtildeKOk W Ch sel τ.1 hX) (formPts _ _) Pr.vGs S0
  MtCSD := fun j τ => Col.MtKCSD W Ch sel τ.1 (j.1 + 1) (Col.mtKOk W Ch sel τ.1 hX (j.1 + 1))
  leftGroupActionLift := fun j τ => Col.unipotentRightActionOnForms W Ch sel τ.1 (j.1 + 1) (Col.mtKOk W Ch sel τ.1 hX (j.1 + 1))
  heckeL := fun j τ => heckeCSD (Col.mtKGSD W Ch sel τ.1 (j.1 + 1)) (Col.mtKOk W Ch sel τ.1 hX (j.1 + 1)) (formPts _ _) Pr.vGs S0

variable (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)

def colFam : DefFam X.K (Col.G0 X.E Pr.vGs R.r) (Col.LevOff ∅ Pr.vGs S0) (TupF TU) (Fin R.m) :=
  (colIn W Ch sel hX v0 TU Xg S0 xiVal).fam

def colSide (P : Col.LevFam X.E X.K R.r Pr.vGs) (Zs : DefSub (colFam W Ch sel hX v0 TU Xg S0 xiVal).amb) :
    DefSide (colFam W Ch sel hX v0 TU Xg S0 xiVal).base :=
  (colIn W Ch sel hX v0 TU Xg S0 xiVal).side P.grp P.chr Zs

theorem twistPrimes_trivialTuple_empty : Col.QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = ∅ := by
  have h1 : ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = 1 := by
    simp [mu0]
  rw [h1]
  unfold Col.QE
  split_ifs with h
  · ext x
    simp [Qprime, MonoidHom.ker_one]
  · rfl

end Inst

end Formalism.L2.DIV
