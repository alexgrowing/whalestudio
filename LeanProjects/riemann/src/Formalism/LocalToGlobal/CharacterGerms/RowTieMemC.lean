import Formalism.LocalToGlobal.CharacterGerms.ValBlocksCChart
import Formalism.LocalToGlobal.CharacterGerms.NormOneIntegral

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIs {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (o : Orb) : Type := Σ t : ZMod 2, Fin (r (tau o t))

def subG {C : Type} [Field C] {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T)
    (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n) :
    MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  MvPolynomial.aeval fun x => ∑ col : Fin 2, MvPolynomial.C (gm x.2.1 x.2.2.2.1 col x.2.2.1) *
    MvPolynomial.X (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n)

def WtTieC {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (gaC : Orb → ZMod 2 → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o s (i : ℕ), i < r (tau o s) → a (tau o s) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o s)), gaC o s k) ∧
  ∀ σ, (∀ o s, tau o s ≠ σ) → ∀ i, i < r σ → a σ i = 0

structure SelfConjugatePlaceSetting {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N) : Prop where

  inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2
  conj : ∀ o t, cc (tau o t) = tau o (t + 1)

  gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1

  hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1
  std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val

  alt : ∀ o, (X o).Alt
  hj : ∀ o, (X o).j' < (X o).n
  supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s

  mon : ∀ o, ∀ q ∈ L o, ∀ g e M, q.1 = GlobalTheory.mon g e M → ∃ s : ZMod 2, ∀ b k, b ≠ s → e b k = 0
  wt : ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k
  tie : WtTieC r tau gaC a
  plinj : Function.Injective pl

def IsotropicToStdSubstHarmonic : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n) (isX : T → Prop),
      subG r tau gm plc (blkProd X F N L pl) ∈ harmK r n C cc isX (fun _ => 1)

def IsotropicToStdSubstLineInvariant : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowInv r n C (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstLineDegree : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowDeg r n C a (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstIntegral : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N) (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n)
    (O : Subring C), (∀ o t q s, gm o t q s ∈ O) → ∀ m, (subG r tau gm plc (blkProd X F N L pl)).coeff m ∈ O

section Mem

variable {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
  (O : Subring C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def selfConjTuplesInLattice : Set (∀ o, MvPolynomial (Fin N × WV fun _ => IIs r tau o) C) :=
  {Po | subG r tau gm plc (∏ o, toAll o (Po o)) ∈ HaO r n C O cc isX a}

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

theorem block_membership_self_conj_first (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree) (h4 : IsotropicToStdSubstIntegral)
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (conj : ∀ o t, cc (tau o t) = tau o (t + 1))
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (gm_int : ∀ o t q s, gm o t q s ∈ O)
    (hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (alt : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s) (tie : WtTieC r tau gaC a) :
    BlockMembershipSelfConjugate X N F (selfConjTuplesInLattice r cc isX a tau gm O plc) gaC := by
  intro L mon wt pl plinj
  have H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl := ⟨inj, conj, gm_hyp, hty, std, alt, hj, supp, mon, wt, tie, plinj⟩
  exact ⟨⟨h1 C V T r cc a Orb tau gm J X F gaC N L pl H n plc isX, h2 C V T r cc a Orb tau gm J X F gaC N L pl H n plc,
    h3 C V T r cc a Orb tau gm J X F gaC N L pl H n plc⟩, h4 C V T r Orb tau gm J X F N L pl n plc O gm_int⟩

end Mem

def OP {C : Type} [Field C] (O : Subring C) (σ : Type) : Subring (MvPolynomial σ C) :=
  (MvPolynomial.map O.subtype).range

theorem coeff_mem_of_OP {C : Type} [Field C] {O : Subring C} {σ : Type} {P : MvPolynomial σ C} (h : P ∈ OP O σ)
    (m : σ →₀ ℕ) : P.coeff m ∈ O := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  rw [MvPolynomial.coeff_map]
  exact (Q.coeff m).2

theorem aeval_mem_OP {C : Type} [Field C] {O : Subring C} {σ τ : Type} (f : σ → MvPolynomial τ C)
    (hf : ∀ x, f x ∈ OP O τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) : MvPolynomial.aeval f P ∈ OP O τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  clear h
  induction Q using MvPolynomial.induction_on
  · rename_i z
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, eq_intCast (Int.castRingHom C) z, map_intCast]
    exact intCast_mem _ z
  · rename_i p q hp hq
    rw [map_add, map_add]
    exact add_mem hp hq
  · rename_i p x hp
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp (hf x)

theorem first_chern_integral : IsotropicToStdSubstIntegral := by
  intro C _ V T r Orb _ tau gm J _ X F N L pl n plc O hO m
  apply coeff_mem_of_OP
  unfold subG
  refine aeval_mem_OP _ (fun x => ?_) (blkProd_mem_ZP X F N L pl)
  refine sum_mem fun col _ => mul_mem ?_ ?_
  · exact RingHom.mem_range.2 ⟨MvPolynomial.C ⟨_, hO _ _ _ _⟩, by rw [MvPolynomial.map_C]; rfl⟩
  · exact RingHom.mem_range.2 ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩

end Formalism.L2.FormalSeriesBounds.RF
