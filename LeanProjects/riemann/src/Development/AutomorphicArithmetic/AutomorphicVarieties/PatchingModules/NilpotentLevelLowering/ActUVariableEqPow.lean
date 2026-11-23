import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa.Lev

def homComp {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G'' : Glob l L} (e : G.Hom G') (h : G'.Hom G'') : G.Hom G'' where
  p := h.p.comp e.p
  cont := h.cont.comp e.cont
  surj := h.surj.comp e.surj
  η g := (h.η _).trans (e.η g)
  c := by rw [MonoidHom.comp_apply, e.c, h.c]
  ε g := (h.ε _).trans (e.ε g)
  φ v g := by rw [MonoidHom.comp_apply, e.φ, h.φ]
  φu v g := by rw [MonoidHom.comp_apply, e.φu, h.φu]

def emb (O R : Type) [CommRing O] [CommRing R] [Algebra O R] {q n : ℕ} (j : Fin q) : MvPolynomial (Fin n) O →+* PU R q n :=
  (MvPolynomial.rename fun i => (j, i) : MvPolynomial (Fin n) R →ₐ[R] PU R q n).toRingHom.comp (MvPolynomial.map (algebraMap O R))

structure HkHyp (O : Type) {R V : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup V] [Module R V] {q n : ℕ}
    (Nq : Fin q → ℕ) (act : PU R q n →ₐ[R] Module.End R V) (e : Fin q → Module.End R V) (W : Fin q → Submodule R V) : Prop where
  ee : ∀ j j', Commute (e j) (e j')
  eX : ∀ j j' i, j ≠ j' → Commute (e j) (act (MvPolynomial.X (j', i)))
  esym : ∀ j (z : MvPolynomial (Fin n) O), z.IsSymmetric → Commute (e j) (act (emb O R j z))
  sum : ∀ j (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) O), Hk.IsDual a b →
    ∑ i, act (emb O R j (a i)) * e j * act (emb O R j (b i)) = act (emb O R j (Hk.NN n (Nq j : O)))
  WX : ∀ j j' i, j ≠ j' → ∀ v ∈ W j, act (MvPolynomial.X (j', i)) v ∈ W j
  We : ∀ j j', j ≠ j' → ∀ v ∈ W j, e j' v ∈ W j
  tr : ∀ j (x : MvPolynomial (Fin n) O), ∀ v ∈ W j,
    e j (act (emb O R j x) v) = act (emb O R j (Hk.dd (Hk.NN n (Nq j : O) * x))) v

section Th

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

abbrev qj (w : Fin q → Plc L) (j : Fin q) : ℕ := resCard ((w j).adicCompletion L)

structure ThData (l : ℕ) (ρ : Representation A (GV n w) M) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) where
  Θ1 : ∀ j, (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w fun _ => ellC l _)))ˣ
  h1 : IsThetaQ ρ (fun _ => ellC l _) Θ1
  Θw : ∀ j, (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w fun _ => ⊤)))ˣ
  hw : IsThetaQ ρ (fun _ => ⊤) Θw
  act1 : PUY A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ellC l _))
  act_uVariable_eq_pow : ∀ j i, act1 (uV A j i) = ((qj w j : A) ^ (i : ℕ)) • (Θ1 j (Pi.mulSingle i (x j)) : Module.End A _)
  act_yVariable : ∀ j i, act1 (1 + yV A j i) = (Θ1 j (Pi.mulSingle i (δ j)) : Module.End A _)
  actw : PU A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ⊤))
  actw_u : ∀ j i, actw (MvPolynomial.X (j, i)) = ((qj w j : A) ^ (i : ℕ)) • (Θw j (Pi.mulSingle i (x j)) : Module.End A _)

end Th

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} {b : TWBase (pairOf B.u) J Empty D}
  {V : s.Lev} {h : (globOf r V).Hom (globOf r V0)} {q : ℕ} {w : Fin q → Plc L}

def LocOk (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (ph ta : Fin q → (globOf r V).G₀) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, (∀ m : A.P, (∀ y : LevPt A ι, y.sp m = 0) → m = 0) ∧ ∀ (y : LevPt A ι) j,
    LocRel l (x j) (δ j) (y.σ j).ρ ((mat y.rep (ph j)).map ι) ((mat y.rep (ta j)).map ι)

end UpperTheory.V.Pa.Lev
