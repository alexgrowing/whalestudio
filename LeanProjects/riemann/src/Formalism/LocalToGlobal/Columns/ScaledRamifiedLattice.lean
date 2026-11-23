import Mathlib
import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section MovesA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.IsDnA (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) (d d' : Deco E n ST SG) : Prop :=
  d' = d.dn P (d'.f P) ∧ ∀ e ∈ d.N, d.f P e = 1 → d'.f P (q • e) = a

theorem Deco.isDnA_one (P : ST) (q : 𝓞 E) (d d' : Deco E n ST SG) :
    Deco.IsDnA P q 1 d d' ↔ Deco.IsDn P q d d' := Iff.rfl

theorem Deco.IsDnA.act {P : ST} {q : 𝓞 E} {a : 𝓞 E ⧸ P.1.asIdeal} {d d' : Deco E n ST SG}
    (hdd : Deco.IsDnA P q a d d') {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) (h : GLG E n SG) :
    Deco.IsDnA P q a (d.act g h) (d'.act g h) := by
  obtain ⟨h1, h2⟩ := hdd
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [h1]
    exact (d.dn_act hg h P (d'.f P)).symm
  · intro e he hfe
    change d'.f P (g.symm (q • e)) = a
    rw [equiv_osmul]
    exact h2 _ ((mem_gmap _ _ _).1 he) hfe

def DecoSet.dnSetA (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) (d : DecoSet E n ST SG) :
    Set (DecoSet E n ST SG) :=
  {d' | Deco.IsDnA P q a d.1 d'.1}

theorem DecoSet.dnSetA_one (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG) : d.dnSetA P q 1 = d.dnSet P q := rfl

theorem DecoSet.smul_mem_dnSetA (x : UF E n × GLG E n SG) (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal)
    (d d' : DecoSet E n ST SG) : x • d' ∈ (x • d).dnSetA P q a ↔ d' ∈ d.dnSetA P q a := by
  constructor
  · intro h
    have := Deco.IsDnA.act h (x⁻¹).1.2 (x⁻¹).2
    have e1 : ((x • d).1.act (x⁻¹).1.1 (x⁻¹).2) = (x⁻¹ • x • d).1 := rfl
    have e2 : ((x • d').1.act (x⁻¹).1.1 (x⁻¹).2) = (x⁻¹ • x • d').1 := rfl
    rw [e1, e2, inv_smul_smul, inv_smul_smul] at this
    exact this
  · intro h
    exact Deco.IsDnA.act h x.1.2 x.2

theorem DecoSet.dnSetA_finite (d : DecoSet E n ST SG) (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) :
    (d.dnSetA P q a).Finite := by
  by_cases h : (d.1.dnN P).FG
  · refine (DecoSet.finite_fibre (ST := ST) (SG := SG) (d.1.dnN P) h).subset ?_
    intro d' hd'
    have := congrArg Deco.N hd'.1
    exact this
  · have he : d.dnSetA P q a = ∅ := by
      ext d'
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hd'
      apply h
      have h1 : d'.1.N = d.1.dnN P := congrArg Deco.N hd'.1
      rw [← h1]
      exact d'.2.lat.fg
    rw [he]
    exact Set.finite_empty

end MovesA

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

def diaG (c : DiaG X.E ST) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofMap (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _) (fun d => DecoSet.dia c d) LinearMap.id
    (fun g d => DecoSet.dia_smul c (FormG.incl Λ g) d) (fun _ _ => rfl)).op

def diamondOperatorOnForms' (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofMap (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _) (fun d => DecoSet.dia1 P c d) LinearMap.id
    (fun g d => DecoSet.dia_smul _ (FormG.incl Λ g) d) (fun _ _ => rfl)).op

def NmG (P : ST) : Module.End X.K (formGSD C Λ).EqFun :=
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := Fintype.ofFinite _
  ∑ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, diamondOperatorOnForms' C Λ P c

def UG (P : ST) (q : 𝓞 X.E) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.upSet_finite d P q).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_upSet (FormG.incl Λ g) P q d' d) (fun _ _ => rfl)).op

def DaG (P : ST) (q : 𝓞 X.E) (a : 𝓞 X.E ⧸ P.1.asIdeal) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.dnSetA_finite d P q a).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_dnSetA (FormG.incl Λ g) P q a d' d) (fun _ _ => rfl)).op

def DG (P : ST) (q : 𝓞 X.E) : Module.End X.K (formGSD C Λ).EqFun := DaG C Λ P q 1

def GsG (P : ST) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) : Module.End X.K (formGSD C Λ).EqFun :=
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := Fintype.ofFinite _
  ∑ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, ψ (c : 𝓞 X.E ⧸ P.1.asIdeal) • diamondOperatorOnForms' C Λ P c

def FFG (P : ST) (q : 𝓞 X.E) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) : Module.End X.K (formGSD C Λ).EqFun :=
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal) := Fintype.ofFinite _
  ∑ a : 𝓞 X.E ⧸ P.1.asIdeal, ψ a • DaG C Λ P q a

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def diaOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    Module.End X.K (ColV W Ch u j) :=
  diamondOperatorOnForms' (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P c

def NmOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  NmG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P

def UOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  UG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E)

def DaOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (a : 𝓞 X.E ⧸ P.1.asIdeal) :
    Module.End X.K (ColV W Ch u j) :=
  DaG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E) a

def DOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  DG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E)

end Cols

structure CharT (X : Fields) (Pr : Primes X) where

  psiT : ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}), AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K

structure CharT.Ok {X : Fields} {Pr : Primes X} (Ps : CharT X Pr) : Prop where
  ne : ∀ u P, Ps.psiT u P ≠ 1
  same : ∀ (u : Pr.Word) (P P' : {P // P ∈ Pr.vT u}) (a : ℤ),
    Ps.psiT u P (a : 𝓞 X.E ⧸ P.1.asIdeal) = Ps.psiT u P' (a : 𝓞 X.E ⧸ P'.1.asIdeal)

section Cols2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

def GsOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  GsG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Ps.psiT u P)

def FFOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  FFG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E) (Ps.psiT u P)

def ColRamV (u : Pr.Word) (j : ℕ) : Submodule X.K (ColV W Ch u j) :=
  ⨅ P : {P // P ∈ Pr.vT u}, LinearMap.ker (NmOp W Ch u j P)

def ramifiedColumnLattice (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColV W Ch u j) :=
  ColL W Ch u j ⊓ (ColRamV W Ch u j).restrictScalars (𝓞 X.K)

def ColRamL (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColRamV W Ch u j) :=
  (ColL W Ch u j).comap ((ColRamV W Ch u j).subtype.restrictScalars (𝓞 X.K))

abbrev MramV (u : Pr.Word) : Submodule X.K (MfV W Ch u) := ColRamV W Ch u 0

def ramifiedSublattice (u : Pr.Word) : Submodule (𝓞 X.K) (MfV W Ch u) := ramifiedColumnLattice W Ch u 0

def MramL (u : Pr.Word) : Submodule (𝓞 X.K) (MramV W Ch u) := ColRamL W Ch u 0

def ramIncl (u : Pr.Word) : MramV W Ch u →ₗ[X.K] MfV W Ch u := (MramV W Ch u).subtype

end Cols2

section Seen

variable {X : Fields}

def Fields.embO (X : Fields) (τ : X.Tau) : 𝓞 X.E →+* 𝓞 X.K := RingOfIntegers.mapRingHom (X.emb τ)

def pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := w.asIdeal.comap (X.embO τ)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have h1 : ((prW w : ℕ) : 𝓞 X.E) ∈ w.asIdeal.comap (X.embO τ) := by
      rw [Ideal.mem_comap, map_natCast]
      exact natCast_prW_mem w
    rw [h, Ideal.mem_bot] at h1
    exact (prW_prime w).ne_zero (by exact_mod_cast h1)

def SeesP (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : HeightOneSpectrum (𝓞 X.E)) : Prop := pullW τ w = P

def SeesPbar (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  pullW τ w = conjPrime₂ P

def tauOfC [Nonempty X.Tau] (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)) : X.Tau :=
  Classical.epsilon fun τ => SeesP w τ P ∨ SeesPbar w τ P

variable (Pr : Primes X)

def seenC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Prop := ∀ τ, X.embO τ (Pr.piT u) ∈ w.asIdeal

def seenBarC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ τ, X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal

end Seen

section Nlam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

open Classical in

def topsP (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Finset X.Tau :=
  W.tops.filter fun τ => pullW τ w ∈ Pr.vT u

open Classical in

def VVTc (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Finset {P // P ∈ Pr.vT u} :=
  Finset.univ.filter fun P => ∃ τ ∈ W.tops, SeesP w τ P.1

def UprodC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (ColV W Ch u j) :=
  ((VVTc W u w).toList.map fun P => UOp W Ch u j P).prod

def expTc (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : ℤ :=
  (R.m : ℤ) * ∑ τ ∈ topsP W u w, W.bTop u τ

def TUmC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (MfV W Ch u) :=
  ((Pr.T u : X.K) ^ expTc W u w) • (UprodC W Ch u 0 w) ^ R.m

def scaledRamifiedLattice (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (𝓞 X.K) (MfV W Ch u) :=
  (ramifiedSublattice W Ch u).map ((TUmC W Ch u w).restrictScalars (𝓞 X.K))

def NlamG (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (𝓞 X.K) (MramV W Ch u) :=
  (scaledRamifiedLattice W Ch u w).comap ((MramV W Ch u).subtype.restrictScalars (𝓞 X.K))

def NlamC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (Ow w) (MramV W Ch u) :=
  atW w (NlamG W Ch u w)

def BvC (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Submodule (𝓞 X.K) (ColV W Ch u j) :=
  (colGSD W Ch u j).intOf fun d => BvLat W u j P d

def SwC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (Ow w) (ColV W Ch u j) :=
  atW w (ColL W Ch u j)

def SwNabC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (Ow w) (ColV W Ch u j) :=
  atW w (ColLnab W Ch u j)

def BvNabC (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Submodule (𝓞 X.K) (ColV W Ch u j) :=
  (colGSD W Ch u j).intOf fun d => nabAtr X.emb (W.lamTrue u j) (d.1.LshKer P)

def BvNabWC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) :
    Submodule (Ow w) (ColV W Ch u j) :=
  atW w (BvNabC W Ch u j P)

def BvWC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) :
    Submodule (Ow w) (ColV W Ch u j) :=
  atW w (BvC W Ch u j P)

end Nlam

end Formalism.L2.Col
