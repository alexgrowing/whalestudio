import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV NumberField IsDedekindDomain

abbrev StabDat {D : D7} {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Type :=
  ∀ i, C.cls i → Set (Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ)

section Gen

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}

def LawAt (O : GL3Theta.LiftObj D C) (i : ℕ) (g : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ) (f : C.Y i → ℂ) : Prop :=
  ∀ y y' : C.Y i, (∀ τ, O.frm i y τ = g.1.map (TaylorLogMetric.embT D τ) * O.frm i y' τ) → f y = g.2 * f y'

def FormsAre (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : GL3Theta.LiftObj D C)
    (G : StabDat C) : Prop :=
  (∀ i, i ≤ D.R.m → ∀ φ ∈ M.Fi i, ∀ c, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) (φ c)) ∧
  ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ φ : C.cls i → C.Y i → ℂ,
    φ ∈ M.Fi i ↔ ∀ c, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) (φ c) ∧ ∀ g ∈ G i c, LawAt O i g (φ c)

def TermLaw (O : GL3Theta.LiftObj D C) (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1))
    (g : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E × ℂ) : Prop :=
  g.1.det ≠ 0 ∧ ∃ k : ℂ,
    (∀ z : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)),
      O.Th i c c' (fun τ => (g.1.map (TaylorLogMetric.embT D τ) * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * O.Th i c c' z) ∧
    g.2 = k * ∏ τ, TaylorLogMetric.embT D τ g.1.det ^ (-C.sDiv i τ)

end Gen

def matE {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  (LinearMap.toMatrix' γ.toLinearMap).map s.iE

end GlobalTheory.KerJ
