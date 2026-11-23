import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LogVandermondeBounds.FinrankFiberSumZero
import Formalism.LogVandermondeBounds.GaussOperatorProductFormula

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Coord

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

structure CoordAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, co (x + y) = co x + co y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, co (a • x) = Ideal.Quotient.mk P.asIdeal a • co x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → co x = 0
  surj : ∀ c, ∃ x ∈ N, co x = c
  ker : ∀ x ∈ N, co x = 0 → x ∈ P.asIdeal • N

structure FunAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, f (x + y) = f x + f y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, f (a • x) = Ideal.Quotient.mk P.asIdeal a * f x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → f x = 0

def coF {P : HeightOneSpectrum (𝓞 E)} (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) (c : Fin n → 𝓞 E ⧸ P.asIdeal)
    (y : Sp E n) : 𝓞 E ⧸ P.asIdeal := ∑ i, c i * co y i

def dualV {κ : Type} [CommRing κ] (x : Fin n → κ) : Fin n → κ := Classical.epsilon fun c => ∑ i, c i * x i = 1

def liftV {P : HeightOneSpectrum (𝓞 E)} (N : Submodule (𝓞 E) (Sp E n)) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.asIdeal) : Sp E n := Classical.epsilon fun y => y ∈ N ∧ co y = x

end Coord

section Fib

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.fibF (d : Deco E n ST SG) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : Deco E n ST SG := d.repl P d.N (coF co c)

def DecoSet.fibF (d : DecoSet E n ST SG) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet E n ST SG :=
  open Classical in if h : (d.1.fibF P co c).Ok then ⟨_, h⟩ else d

def DecoSet.fibX (d : DecoSet E n ST SG) (P : ST) (q : 𝓞 E) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet E n ST SG :=
  (d.fibF P co (dualV x)).up P q (liftV d.1.N co x)

def DecoSet.trSet (P : ST) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d' | d'.1 = d.1.repl P d.1.N (d'.1.f P)}

def DecoSet.dnAll (P : ST) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d' | d'.1 = d.1.dn P (d'.1.f P)}

def DecoSet.upAll (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  ⋃ d0 ∈ d.trSet P, d0.upSet P q

def DecoSet.trpSet (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  ⋃ d0 ∈ d.dnAll P, d0.upSet P q

def DecoSet.upSetA (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) (d : DecoSet E n ST SG) :
    Set (DecoSet E n ST SG) :=
  {d' | d' ∈ d.upAll P q ∧ d ∈ d'.dnSetA P q a}

theorem Deco.repl_act (d : Deco E n ST SG) (g : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) (P : ST)
    (N' : Submodule (𝓞 E) (Sp E n)) (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) :
    (d.act g h).repl P (gmap g N') (fun y => f' (g.symm y)) = (d.repl P N' f').act g h := by
  classical
  ext1
  · rfl
  · funext Q y
    by_cases hQ : Q = P
    · subst hQ
      simp only [Deco.repl, Deco.act, Function.update_self]
    · simp only [Deco.repl, Deco.act, Function.update_of_ne hQ]
  · rfl

theorem DecoSet.rel_smul_iff {r : DecoSet E n ST SG → DecoSet E n ST SG → Prop}
    (hr : ∀ (a : UF E n × GLG E n SG) d d', r d d' → r (a • d) (a • d')) (a : UF E n × GLG E n SG)
    (d d' : DecoSet E n ST SG) : r (a • d) (a • d') ↔ r d d' := by
  refine ⟨fun h => ?_, hr a d d'⟩
  have := hr a⁻¹ _ _ h
  rwa [inv_smul_smul, inv_smul_smul] at this

theorem DecoSet.smul_mem_trSet (a : UF E n × GLG E n SG) (P : ST) (d d' : DecoSet E n ST SG) :
    a • d' ∈ (a • d).trSet P ↔ d' ∈ d.trSet P := by
  refine DecoSet.rel_smul_iff (r := fun d d' => d' ∈ d.trSet P) (fun a d d' h => ?_) a d d'
  change (d'.1.act a.1.1 a.2) = _
  have h' : d'.1 = d.1.repl P d.1.N (d'.1.f P) := h
  conv_lhs => rw [h']
  exact (d.1.repl_act a.1.1 a.2 P d.1.N (d'.1.f P)).symm

theorem DecoSet.smul_mem_dnAll (a : UF E n × GLG E n SG) (P : ST) (d d' : DecoSet E n ST SG) :
    a • d' ∈ (a • d).dnAll P ↔ d' ∈ d.dnAll P := by
  refine DecoSet.rel_smul_iff (r := fun d d' => d' ∈ d.dnAll P) (fun a d d' h => ?_) a d d'
  change (d'.1.act a.1.1 a.2) = _
  have h' : d'.1 = d.1.dn P (d'.1.f P) := h
  conv_lhs => rw [h']
  exact (d.1.dn_act a.1.2 a.2 P (d'.1.f P)).symm

theorem DecoSet.smul_mem_upAll (a : UF E n × GLG E n SG) (P : ST) (q : 𝓞 E) (d d' : DecoSet E n ST SG) :
    a • d' ∈ (a • d).upAll P q ↔ d' ∈ d.upAll P q := by
  refine DecoSet.rel_smul_iff (r := fun d d' => d' ∈ d.upAll P q) (fun a d d' h => ?_) a d d'
  simp only [DecoSet.upAll, Set.mem_iUnion, exists_prop] at h ⊢
  obtain ⟨d0, h0, h1⟩ := h
  exact ⟨a • d0, (DecoSet.smul_mem_trSet a P d d0).2 h0, (DecoSet.smul_mem_upSet a P q d0 d').2 h1⟩

theorem DecoSet.smul_mem_trpSet (a : UF E n × GLG E n SG) (P : ST) (q : 𝓞 E) (d d' : DecoSet E n ST SG) :
    a • d' ∈ (a • d).trpSet P q ↔ d' ∈ d.trpSet P q := by
  refine DecoSet.rel_smul_iff (r := fun d d' => d' ∈ d.trpSet P q) (fun a d d' h => ?_) a d d'
  simp only [DecoSet.trpSet, Set.mem_iUnion, exists_prop] at h ⊢
  obtain ⟨d0, h0, h1⟩ := h
  exact ⟨a • d0, (DecoSet.smul_mem_dnAll a P d d0).2 h0, (DecoSet.smul_mem_upSet a P q d0 d').2 h1⟩

theorem DecoSet.smul_mem_upSetA (x : UF E n × GLG E n SG) (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal)
    (d d' : DecoSet E n ST SG) : x • d' ∈ (x • d).upSetA P q a ↔ d' ∈ d.upSetA P q a :=
  and_congr (DecoSet.smul_mem_upAll x P q d d') (DecoSet.smul_mem_dnSetA x P q a d' d)

theorem DecoSet.trSet_finite (P : ST) (d : DecoSet E n ST SG) : (d.trSet P).Finite :=
  (DecoSet.finite_fibre (ST := ST) (SG := SG) d.1.N d.2.lat.fg).subset fun d' hd' => by
    have h1 : d'.1 = d.1.repl P d.1.N (d'.1.f P) := hd'
    have := congrArg Deco.N h1
    exact this

theorem DecoSet.dnAll_finite (P : ST) (d : DecoSet E n ST SG) : (d.dnAll P).Finite := by
  by_cases h : (d.1.dnN P).FG
  · exact (DecoSet.finite_fibre (ST := ST) (SG := SG) (d.1.dnN P) h).subset fun d' hd' => by
      have h1 : d'.1 = d.1.dn P (d'.1.f P) := hd'
      have := congrArg Deco.N h1
      exact this
  · have he : d.dnAll P = ∅ := by
      ext d'
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hd'
      apply h
      have h0 : d'.1 = d.1.dn P (d'.1.f P) := hd'
      have h1 : d'.1.N = d.1.dnN P := by
        have := congrArg Deco.N h0
        exact this
      rw [← h1]
      exact d'.2.lat.fg
    rw [he]
    exact Set.finite_empty

theorem DecoSet.upAll_finite (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG) : (d.upAll P q).Finite :=
  (d.trSet_finite P).biUnion fun d0 _ => DecoSet.upSet_finite d0 P q

theorem DecoSet.trpSet_finite (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG) : (d.trpSet P q).Finite :=
  (d.dnAll_finite P).biUnion fun d0 _ => DecoSet.upSet_finite d0 P q

theorem DecoSet.upSetA_finite (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) (d : DecoSet E n ST SG) :
    (d.upSetA P q a).Finite := (d.upAll_finite P q).subset fun _ h => h.1

structure SepElt (ST : Finset (HeightOneSpectrum (𝓞 E))) (a : 𝓞 E) : Prop where
  conj : ∀ P : ST, cO E a ∈ P.1.asIdeal
  off : ∀ P : ST, a ∉ P.1.asIdeal

structure FibreModel (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG)
    (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal)) : Prop where

  injF : ∀ c c', c ≠ 0 → c' ≠ 0 → d.fibF P co c = d.fibF P co c' → c = c'

  injX : ∀ x x', x ≠ 0 → x' ≠ 0 → d.fibX P q co x = d.fibX P q co x' → x = x'

  tr : ∀ c, c ≠ 0 → ∀ d', d' ∈ (d.fibF P co c).trSet P ↔ ∃ c', c' ≠ 0 ∧ d' = d.fibF P co c'

  up : ∀ c, c ≠ 0 → ∀ d', d' ∈ (d.fibF P co c).upSet P q ↔ ∃ x, ∑ i, c i * x i = 1 ∧ d' = d.fibX P q co x

  dnAll : ∀ x, x ≠ 0 → ∀ d', d' ∈ (d.fibX P q co x).dnAll P ↔ ∃ c, c ≠ 0 ∧ d' = d.fibF P co c

  dn : ∀ x, x ≠ 0 → ∀ a d', d' ∈ (d.fibX P q co x).dnSetA P q a ↔
    ∃ c, c ≠ 0 ∧ ∑ i, c i * x i = a ∧ d' = d.fibF P co c

  diaF : ∀ (u : (𝓞 E ⧸ P.1.asIdeal)ˣ) c, c ≠ 0 → (d.fibF P co c).dia1 P u = d.fibF P co ((u : 𝓞 E ⧸ P.1.asIdeal) • c)

  diaX : ∀ (u : (𝓞 E ⧸ P.1.asIdeal)ˣ) x, x ≠ 0 →
    (d.fibX P q co x).dia1 P u = d.fibX P q co (((u⁻¹ : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) • x)

end Fib

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

def trG (P : ST) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.trSet_finite P d).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_trSet (FormG.incl Λ g) P d' d) (fun _ _ => rfl)).op

def trpG (P : ST) (q : 𝓞 X.E) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.trpSet_finite P q d).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_trpSet (FormG.incl Λ g) P q d' d) (fun _ _ => rfl)).op

def UaG (P : ST) (q : 𝓞 X.E) (a : 𝓞 X.E ⧸ P.1.asIdeal) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.upSetA_finite P q a d).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_upSetA (FormG.incl Λ g) P q a d' d) (fun _ _ => rfl)).op

def GsStarG (P : ST) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) : Module.End X.K (formGSD C Λ).EqFun :=
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := Fintype.ofFinite _
  ∑ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, ψ (-(c : 𝓞 X.E ⧸ P.1.asIdeal)) • diamondOperatorOnForms' C Λ P c⁻¹

def FFStarG (P : ST) (q : 𝓞 X.E) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) : Module.End X.K (formGSD C Λ).EqFun :=
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal) := Fintype.ofFinite _
  ∑ a : 𝓞 X.E ⧸ P.1.asIdeal, ψ (-a) • UaG C Λ P q a

variable {C Λ}

def resF {R : Type} (d : DecoSet X.E n ST SG) (P : ST) (co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal))
    (ℓ : C.V → R) (φ : (formGSD C Λ).EqFun) : (Fin n → 𝓞 X.E ⧸ P.1.asIdeal) → R :=
  fun c => ℓ ((φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.fibF P co c))

def resX {R : Type} (d : DecoSet X.E n ST SG) (P : ST) (q : 𝓞 X.E)
    (co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)) (ℓ : C.V → R) (φ : (formGSD C Λ).EqFun) :
    (Fin n → 𝓞 X.E ⧸ P.1.asIdeal) → R :=
  fun x => ℓ ((φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.fibX P q co x))

def chrC {P : ST} (σ : X.K →+* ℂ) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) : AddChar (𝓞 X.E ⧸ P.1.asIdeal) ℂ :=
  (σ : X.K →* ℂ).compAddChar ψ

end Ops

@[reducible] def resField {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal

@[reducible] def resFintype {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _

section Below

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ} (emb : ι → E →+* K)

def SameBelow (w : HeightOneSpectrum (𝓞 K)) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ τ, (∀ x ∈ L, ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L') ∧
    ∀ x ∈ L', ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L

end Below

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

def trOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  trG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P

def trpOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  trpG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E)

def UaOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (a : 𝓞 X.E ⧸ P.1.asIdeal) :
    Module.End X.K (ColV W Ch u j) :=
  UaG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E) a

def GsStarOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  GsStarG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Ps.psiT u P)

def FFStarOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  FFStarG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E) (Ps.psiT u P)

end Cols

end Formalism.L2.Col
