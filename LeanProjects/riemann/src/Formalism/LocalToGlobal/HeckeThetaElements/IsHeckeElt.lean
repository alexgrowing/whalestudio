import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.L2.NTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev LamHat (V : HSp D) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  latHat D.host.F D.host.E (L0c D V)

def KpC (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {h | h ∈ KsphC V ∅ ∧ ∀ y ∈ LamHat V, ∃ z ∈ LamHat V,
    (finMat D.sp.cm.sig V.gram h - 1).mulVec y = N • z}

def torAt (V : HSp D) (τ : D.what₂.Tau)
    (A : Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (z : Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2 → ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  let B : Matrix (Fin V.rank) (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) ℂ :=
    (gramAt D V τ)⁻¹ * A.conjTranspose * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * Matrix.diagonal z
  B * A

def wtChar {ι : Type} [Fintype ι] (lam : ι → ℤ) (z : ι → ℂ) : ℂ := ∏ a, z a ^ lam a

def holEnt (p q : ℕ) (lam : Fin p ⊕ Fin q → ℤ) : Fin p ⊕ Fin q → ℚ :=
  Sum.elim (fun i => (lam (Sum.inl i) : ℚ) - (q : ℚ) / 2 + ((p : ℚ) - 1) / 2 - (i : ℚ))
    (fun i => (lam (Sum.inr i) : ℚ) + (p : ℚ) / 2 + ((q : ℚ) - 1) / 2 - (i : ℚ))

def holPar (p q : ℕ) (lam : Fin p ⊕ Fin q → ℤ) : SPar :=
  Finset.univ.image fun a : Fin p ⊕ Fin q => (holEnt p q lam a, Sum.elim (fun _ => true) (fun _ => false) a)

def HolOK (p q : ℕ) (lam : Fin p ⊕ Fin q → ℤ) : Prop :=
  (∀ i i' : Fin p, i ≤ i' → lam (Sum.inl i') ≤ lam (Sum.inl i)) ∧
  (∀ i i' : Fin q, i ≤ i' → lam (Sum.inr i') ≤ lam (Sum.inr i)) ∧
  ∀ (i : Fin p) (i' : Fin q), holEnt p q lam (Sum.inr i') < holEnt p q lam (Sum.inl i)

variable {X : ThetaX D} {Ap : TH.ProvA}

def LevWt (A : AllTied D X Ap) (V : HSp D) (N : ℕ)
    (lam : ∀ τ : D.what₂.Tau, Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2 → ℤ) : Submodule ℂ (X.AF V) where
  carrier := {F | (∀ g : X.Gf V, ((A.T.eGf V g : GfC V) : GA D V) ∈ KpC V N → X.actF V g F = F) ∧
    ∀ (τ : D.what₂.Tau) (z : Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2 → ℂ), (∀ a, ‖z a‖ = 1) →
      X.actR V τ (torAt V τ (A.kf.cpt V τ) z) F = wtChar (lam τ) z • F}
  add_mem' := by
    intro F G hF hG
    refine ⟨fun g hg => ?_, fun τ z hz => ?_⟩
    · rw [map_add, hF.1 g hg, hG.1 g hg]
    · rw [map_add, hF.2 τ z hz, hG.2 τ z hz, smul_add]
  zero_mem' := by
    refine ⟨fun g _ => map_zero _, fun τ z _ => ?_⟩
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c F hF
    refine ⟨fun g hg => ?_, fun τ z hz => ?_⟩
    · rw [map_smul, hF.1 g hg]
    · rw [map_smul, hF.2 τ z hz, smul_comm]

def FmC (A : AllTied D X Ap) (V : HSp D) (N : ℕ)
    (lam : ∀ τ : D.what₂.Tau, Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2 → ℤ) : Submodule ℂ (X.AF V) :=
  X.cusp V ⊓ X.typ V (fun τ => holPar _ _ (lam τ)) ⊓ LevWt A V N lam

def IsIdemAt (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  IsSplitIdem D e ∧ ∀ x : 𝓞 D.host.E, x ≠ 0 →
    (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)

def IsHeckeElt (V : HSp D) (e : AE D) (ϖ : D.host.E) (k : ℕ) (α : GA D V) : Prop :=
  α ∈ GfC V ∧ SuppAt e V α ∧
  (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α).mulVec y a) ∈ LamHat V) ∧
  (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * (finPart D (incA D ϖ) * y a)) =
      fun a => finPart D e * (finMat D.sp.cm.sig V.gram α).mulVec z a) ∧
  ∃ u u' : AE D, finPart D u ∈ intAE D ∧ finPart D u' ∈ intAE D ∧ e * u * u' = e ∧
    e * (mt V α).det = e * incA D ϖ ^ k * u

def IsDCOp (A : AllTied D X Ap) (V : HSp D) (K : Set (GA D V)) (α : GA D V) (T : Module.End ℂ (X.AF V)) : Prop :=
  ∃ R : Finset (X.Gf V),

    (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, ((A.T.eGf V γ : GfC V) : GA D V) = k₁ * α * k₂) ∧
    (∀ x : GA D V, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) ↔
      ∃! γ : X.Gf V, γ ∈ R ∧ ((A.T.eGf V γ : GfC V) : GA D V)⁻¹ * x ∈ K) ∧
    ∀ F, T F = ∑ γ ∈ R, X.actF V γ F

end Formalism.L2.NTheta
