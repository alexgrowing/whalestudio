import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UnramAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 F) = 1

abbrev Ev (v : HeightOneSpectrum (𝓞 F)) : Type := Fv F v ⊗[F] E

def OEv (v : HeightOneSpectrum (𝓞 F)) : Subalgebra (v.adicCompletionIntegers F) (Ev F E v) :=
  integralClosure (v.adicCompletionIntegers F) (Ev F E v)

variable {F E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (v : HeightOneSpectrum (𝓞 F))

def act (g : HA (Fv F v) σ J) (x : Fin M → Ev F E v) : Fin M → Ev F E v :=
  ((HA.mat (Fv F v) σ J g : GL (Fin M) (Ev F E v)) : Matrix (Fin M) (Fin M) (Ev F E v)).mulVec x

def IsSDLatIn (P : Submodule (Ev F E v) (Fin M → Ev F E v))
    (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Prop :=
  L.FG ∧ Submodule.span (Ev F E v) (L : Set (Fin M → Ev F E v)) = P ∧
    ∀ y : Fin M → Ev F E v, y ∈ L ↔ (y ∈ P ∧ ∀ z ∈ L, hR (Fv F v) σ J z y ∈ OEv F E v)

def IsSDLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Prop := IsSDLatIn σ J v ⊤ L

def perp (x : Fin M → Ev F E v) : Submodule (Ev F E v) (Fin M → Ev F E v) where
  carrier := {y | hR (Fv F v) σ J x y = 0}
  zero_mem' := by simp [hR, Formalism.UG.hform]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    have : ∑ i, ∑ j, sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * (c • a) j =
        c * ∑ i, ∑ j, sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * a j := by
      simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha, mul_zero]

def perpLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v) :
    Submodule (OEv F E v) (Fin M → Ev F E v) :=
  (perp σ J v x).restrictScalars (OEv F E v) ⊓ L

def stabLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Subgroup (HA (Fv F v) σ J) :=
  (Formalism.UG.stabGL L).subgroupOf (HR (Fv F v) σ J)

def stabVec (x : Fin M → Ev F E v) : Subgroup (HA (Fv F v) σ J) :=
  MulAction.stabilizer (HA (Fv F v) σ J) (fun _ : Fin 1 => x)

def unitaryLatIn (P : Submodule (Ev F E v) (Fin M → Ev F E v))
    (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) : Subgroup (P ≃ₗ[Ev F E v] P) where
  carrier := {u | (∀ y z : P, hR (Fv F v) σ J (u y) (u z) = hR (Fv F v) σ J y z) ∧
    ∀ y : P, (y : Fin M → Ev F E v) ∈ L' ↔ ((u y : P) : Fin M → Ev F E v) ∈ L'}
  one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨fun y z => (ha (b y) (b z)).trans (hb y z), fun y => (hb' y).trans (ha' (b y))⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun y z => ?_, fun y => ?_⟩
    · have := ha (a.symm y) (a.symm z)
      rw [a.apply_symm_apply, a.apply_symm_apply] at this
      exact this.symm
    · have := ha' (a.symm y)
      rw [a.apply_symm_apply] at this
      exact this.symm

def Xb (β : Fv F v) : Set (Fin M → Ev F E v) := {x | x ≠ 0 ∧ qR (Fv F v) σ J x = β}

def SL (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (β : Fv F v) : Set (Fin M → Ev F E v) :=
  {x | x ∈ L ∧ qR (Fv F v) σ J x = β}

def HasONB (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Prop :=
  ∃ b : Module.Basis (Fin M) (OEv F E v) L,
    ∀ i j, hR (Fv F v) σ J (b i) (b j) = if i = j then 1 else 0

def UnitVectors (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (β : Fv F v) : Prop :=

  (SL σ J v L β).Nonempty ∧

  (∀ x ∈ SL σ J v L β,
    L = Submodule.span (OEv F E v) {x} ⊔ perpLat σ J v L x ∧
      IsSDLatIn σ J v (perp σ J v x) (perpLat σ J v L x)) ∧

  (∀ x ∈ SL σ J v L β, ∀ x' ∈ SL σ J v L β, ∃ g ∈ stabLat σ J v L, act σ J v g x = x') ∧

  (∀ x ∈ SL σ J v L β,
    stabLat σ J v L ⊓ stabVec σ J v x = stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x ∧
    ∃ φ : (stabLat σ J v L ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) ≃*
        unitaryLatIn σ J v (perp σ J v x) (perpLat σ J v L x),
      ∀ g (y : perp σ J v x),
        (((φ g : perp σ J v x ≃ₗ[Ev F E v] perp σ J v x) y : perp σ J v x) : Fin M → Ev F E v) =
          act σ J v (g : HA (Fv F v) σ J) y) ∧

  (∀ x ∈ Xb σ J v β, ∀ x' ∈ Xb σ J v β, ∃ g : HA (Fv F v) σ J, act σ J v g x = x') ∧

  (∀ x ∈ Xb σ J v β, (∃ L₁, IsSDLat σ J v L₁ ∧ x ∈ L₁) ∧
    ∃ L', IsSDLatIn σ J v (perp σ J v x) L')

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def SelfDualLattices : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M →
    ∀ v : HeightOneSpectrum (𝓞 F), UnramAt F E v →
    ∀ L : Submodule (OEv F E v) (Fin M → Ev F E v), IsSDLat σ J v L →
      HasONB σ J v L ∧
      (∀ L₁ : Submodule (OEv F E v) (Fin M → Ev F E v), IsSDLat σ J v L₁ →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ act σ J v g y ∈ L₁) ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        UnitVectors σ J v L ((β : v.adicCompletionIntegers F) : Fv F v)

section Basic₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma involution_apply_eq_tensorProductMap_restrictScalars (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ a =
      ((Algebra.TensorProduct.map (AlgHom.id (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) σ).restrictScalars
        (v.adicCompletionIntegers F)) a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR; simp
  | add x y hx hy => simp [map_add, hx, hy]

open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.sigR_mem {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v}
    (ha : a ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ a ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v := by
  rw [involution_apply_eq_tensorProductMap_restrictScalars]
  exact IsIntegral.map _ ha

theorem hR_one {M : ℕ} (z y : Fin M → Ev F E v) :
    hR (Fv F v) σ (1 : Matrix (Fin M) (Fin M) E) z y = ∑ i, sigR (Fv F v) σ (z i) * y i := by
  simp only [hR, Formalism.UG.hform, JR]
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  simp [Matrix.one_apply]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
