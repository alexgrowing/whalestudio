import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Defs

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def latK (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (Pi.basisFun K (Fin n)) M (formAt (Pi.basisFun K (Fin n)) (hStd K n))

@[reducible] def weylH (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (bVV K (oneW lam)) (delK (oneW lam) fun _ => M) (formAt (bVV K (oneW lam)) (stdPair K lam))

@[reducible] def tenH {ι : Type} [Fintype ι] (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (bVV K lam) (delK lam M) (formAt (bVV K lam) (pairK lam fun _ => 1))

theorem weylH_std (lam : DomWeight n) : weylH K lam (colLat (1 : GL (Fin n) K)) = stdDelH K lam := by
  unfold weylH stdDelH
  rw [stdDelL_eq]

def WeylFunct : Prop :=
  ∀ (n : ℕ) (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsLattice K M →
    (weylH K lam M).mu = ((∑ i, lam.w i : ℤ) : ℝ) * (latK K M).mu + (stdDelH K lam).mu

def TensorSlope : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)),
    (∀ τ, Submodule.IsLattice K (M τ)) → (tenH K lam M).mu = ∑ τ, (weylH K (lam τ) (M τ)).mu

end Defs

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def EEC (u : Pr.Word) (d : (colGSD W Ch u 0).D) (τ : X.Tau) : Submodule (𝓞 X.K) (Fin (R.N 0) → X.K) :=
  dualFr (tauLat X.emb τ (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh)

theorem EEC_isLattice (u : Pr.Word) (d : (colGSD W Ch u 0).D) (τ : X.Tau) : Submodule.IsLattice X.K (EEC W Ch u d τ) := by
  unfold EEC
  have hL : Submodule.IsLattice X.E (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh :=
    (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).2.Lsh_lattice
  exact (dualFrameLattice_holds X.K (R.N 0) 1 _ (by simp)
    (tauLatticeLattice_holds X.E X.K X.Tau (R.N 0) X.emb τ _ hL)).1

theorem colValH_eq_tenH (u : Pr.Word) (d : (colGSD W Ch u 0).D) :
    (colGSD W Ch u 0).valH d = tenH X.K (W.lamTrue u 0) (EEC W Ch u d) := by
  have hg : gramKd X.emb (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) = fun _ => 1 := by
    funext τ
    simp [gramKd]
  have hpair : (colGSD W Ch u 0).pair = pairK (W.lamTrue u 0) fun _ => 1 := by
    show pairVr X.emb (W.lamTrue u 0) 1 = _
    rw [pairVr, hg]
  have hform : (fun v => (colGSD W Ch u 0).pairAt v) =
      formAt (bVV X.K (W.lamTrue u 0)) (pairK (W.lamTrue u 0) fun _ => 1) := by
    funext v x y
    rw [GSD.pairAt_eq_formAt, hpair]
    rfl
  show ofFormB (colGSD W Ch u 0).bV ((colGSD W Ch u 0).Del d) (fun v => (colGSD W Ch u 0).pairAt v) = _
  rw [hform]
  rfl

def EESlope (u : Pr.Word) : Prop :=
  ∀ (d : (colGSD W Ch u 0).D) (τ : X.Tau), (latK X.K (EEC W Ch u d τ)).mu = -(logTC Pr u) / (R.k : ℝ)

end Cols

end Formalism.L2.Col
