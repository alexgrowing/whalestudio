import Mathlib
import Formalism.PeriodIntegrals.AdelClassFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf

noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

def DInj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Function.Injective (Formalism.UG.inclE (F := F) (E := E) (Af F))

def DInter : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (e : E),
    Formalism.UG.inclE (F := F) (Af F) e ∈ IntAf F E → e ∈ (algebraMap (𝓞 E) E).range

def DDenom : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (r : E ⊗[F] Af F),
    ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Af F) * r ∈ IntAf F E

def DDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ r ∈ IntAf F E, ∃ a : 𝓞 E, ∃ r' ∈ IntAf F E,
      r = Formalism.UG.inclE (F := F) (Af F) (a : E) + (N : E ⊗[F] Af F) * r'

def iv (I : AutInst) (v : Fin I.n → I.E) : Fin I.n → I.E ⊗[I.F] Af I.F :=
  fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (v i)

def hhat (I : AutInst) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) : I.E ⊗[I.F] Af I.F :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) y z

def LInter : Prop := ∀ (I : AutInst) (v : Fin I.n → I.E), iv I v ∈ I.Lf → v ∈ I.L

def LDenom : Prop :=
  ∀ (I : AutInst) (y : Fin I.n → I.E ⊗[I.F] Af I.F), ∃ m : ℕ, 0 < m ∧ (m : I.E ⊗[I.F] Af I.F) • y ∈ I.Lf

def LDense : Prop :=
  ∀ (I : AutInst) (N : ℕ), 0 < N → ∀ y ∈ I.Lf, ∃ l ∈ I.L, ∃ y' ∈ I.Lf, y = iv I l + (N : I.E ⊗[I.F] Af I.F) • y'

def LHatInt : Prop := ∀ (I : AutInst), ∀ y ∈ I.Lf, ∀ z ∈ I.Lf, hhat I y z ∈ IntAf I.F I.E

def LHatDual : Prop :=
  ∀ (I : AutInst) (z : Fin I.n → I.E ⊗[I.F] Af I.F), (∀ y ∈ I.Lf, hhat I y z ∈ IntAf I.F I.E) → z ∈ I.Lf

def abelian₂ (I : AutInst) (x : I.Gf) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := {v | I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf}
  add_mem' := fun {v w} hv hw => by
    have e : iv I (v + w) = iv I v + iv I w := by
      funext i; simp [iv]
    show I.fmat x⁻¹ *ᵥ iv I (v + w) ∈ I.Lf
    rw [e, Matrix.mulVec_add]
    exact I.Lf.add_mem hv hw
  zero_mem' := by
    have e : iv I (0 : Fin I.n → I.E) = 0 := by
      funext i; simp [iv]
    show I.fmat x⁻¹ *ᵥ iv I 0 ∈ I.Lf
    rw [e, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  smul_mem' := fun a v hv => by
    have ha : Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) ∈ IntAf I.F I.E :=
      Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)
    have e : iv I (a • v) = Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • iv I v := by
      funext i
      simp [iv, Algebra.smul_def]
    show I.fmat x⁻¹ *ᵥ iv I (a • v) ∈ I.Lf
    rw [e, Matrix.mulVec_smul]
    exact I.Lf.smul_mem ⟨_, ha⟩ hv

def MLat : Prop :=
  ∀ (I : AutInst) (x : I.Gf), (abelian₂ I x).FG ∧ Submodule.span I.E ((abelian₂ I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = ⊤

def MGen : Prop :=
  ∀ (I : AutInst) (x : I.Gf), ∀ y ∈ I.Lf,
    I.fmat x *ᵥ y ∈ Submodule.span (IntAf I.F I.E) (Set.range fun v : abelian₂ I x => iv I (v : Fin I.n → I.E))

def MDual : Prop := ∀ (I : AutInst) (x : I.Gf), SelfDual I.J (abelian₂ I x)

def MInj : Prop := ∀ (I : AutInst) (x y : I.Gf), abelian₂ I x = abelian₂ I y → ∃ k ∈ I.Kset, y = x * k

def MEquiv : Prop :=
  ∀ (I : AutInst) (γ : GL (Fin I.n) I.E), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J →
    ∃ c ∈ GFf I, I.fmat c = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) ∧
      ∀ x, IsImg γ (abelian₂ I x) (abelian₂ I (c * x))

theorem stDict_of (h1 : MLat) (h2 : MDual) (h3 : MInj) (h4 : MEquiv) : StDict :=
  fun I => ⟨abelian₂ I, fun x => ⟨(h1 I x).1, (h1 I x).2, h2 I x⟩, h3 I, h4 I⟩

end PIW.AdelClassFin
