import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain

namespace Formalism.L2

instance hostCM {R : Ranks} (H : Host R) : IsCMField H.E := H.isCMField_hostE

def badPl (D : D7) (i : D.nd.Loc) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ∃ w : PlE D.host, NG.OverPl w v ∧ (w ∈ D.nd.Q i ∨ (∃ k, w ∈ placesOver D.host.E (D.host.g k)) ∨
    w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde))}

def iotaOC (D : D7) (i : D.nd.Loc) : D.nd.O i →+* ℂ :=
  ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

structure MtReal (D : D7) (μ : D.what₂.Tup) (j : ℕ) where

  wt : NG.AlgWt D.host.E D.R.nV

  J : Subgroup (GAf D.host.E D.R.nV)
  χ : J →* ℂˣ
  J_open : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1

  real : D.what₂.Mt μ j →ₗ[ℂ] (GAf D.host.E D.R.nV → wt.W)
  real_inj : Function.Injective real
  real_range : LinearMap.range real = NG.TypeSp wt.ρ J χ

abbrev MtFam (D : D7) : Type 1 := ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → MtReal D μ j

def MtFam.loc {D : D7} (M : MtFam D) (i : D.nd.Loc) : MtReal D (D.nd.mu i) (D.nd.j i) :=
  M (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2

structure HeckeTied (D : D7) (M : MtFam D) : Prop where

  J_hyp : ∀ i : D.nd.Loc, NG.HypOutside (M.loc i).J (M.loc i).χ (badPl D i)

  hT : ∀ (i : D.nd.Loc) (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut D.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ x x' : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
    (M.loc i).real (D.what₂.jMt (D.nd.mu i) (D.nd.j i) x') =
      NG.tN (M.loc i).J s ϖ k ((M.loc i).real (D.what₂.jMt (D.nd.mu i) (D.nd.j i) x)) →
    D.nd.prMt i x' = ((D.nd.act i (D.nd.hT i w k)).baseChange (FractionRing (D.nd.O i))) (D.nd.prMt i x)

  sameO : ∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' →
    ∃ φ : D.nd.O i ≃+* D.nd.O i', ∀ z, iotaOC D i z = iotaOC D i' (φ z)

  sep : ∀ (i i' : D.nd.Loc) (φ : D.nd.O i ≃+* D.nd.O i'), (∀ z, iotaOC D i z = iotaOC D i' (φ z)) →
    D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → i ≠ i' → ∀ (x : D.nd.X i) (x' : D.nd.X i'),
    ∃ (v : PlE D.host) (k : ℕ), SplitOut D.nd i v ∧ SplitOut D.nd i' v ∧ 1 ≤ k ∧ k ≤ D.R.nV ∧
      IsUnit (φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) - (D.nd.hT i' v k : D.nd.X i' → D.nd.O i') x')

  Q_conj : ∀ (i : D.nd.Loc) (w w' : PlE D.host), IsConjPl D.host w w' → w ∈ D.nd.Q i → w' ∈ D.nd.Q i

  Q_same : ∀ i i' : D.nd.Loc, D.nd.w i = D.nd.w i' → D.nd.Q i = D.nd.Q i'

def HeckeRational (D : D7) (M : MtFam D) : Prop :=
  ∀ (i : D.nd.Loc) (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut D.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ x : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
    ∃ x' : D.what₂.MtL (D.nd.mu i) (D.nd.j i), (M.loc i).real (D.what₂.jMt (D.nd.mu i) (D.nd.j i) x') =
      NG.tN (M.loc i).J s ϖ k ((M.loc i).real (D.what₂.jMt (D.nd.mu i) (D.nd.j i) x))

structure AVTied (D : D7) (M : MtFam D) where

  S : ∀ i, D.naut.AV i → Submodule ℂ (GAf D.host.E D.R.nV → (M.loc i).wt.W)
  irr : ∀ i P, NG.IsIrrRep (M.loc i).wt.ρ (S i P)

  inj : ∀ i P P', NG.IsoRep (S i P) (S i P') → P = P'

  surj : ∀ i S', NG.IsIrrRep (M.loc i).wt.ρ S' → (NG.isoTyp (M.loc i).wt.ρ S').comap (M.loc i).real ≠ ⊥ →
    ∃ P, NG.IsoRep (S i P) S'

  typeV : ∀ i P, D.naut.typeV i P = (NG.isoTyp (M.loc i).wt.ρ (S i P)).comap (M.loc i).real

  ptV : ∀ i P x, D.naut.ptV i P = some x ↔ ∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut D.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P,
    NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) • (M.loc i).real y

def AVTied.rep {D : D7} {M : MtFam D} (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) :
    NG.AutRep D.host.E D.R.nV :=
  { (M.loc i).wt with S := A.S i P, irrS := A.irr i P }

end Formalism.L2
