import Mathlib
import GroundTheory.AutomorphicForms.HermitianSpaces
import GroundTheory.HeightsAndTheta.Theta.GaussianExample
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

namespace GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys

open GroundTheory.Automorphic GroundTheory.Heights₂.Theta MeasureTheory TensorProduct NumberField
open scoped NNReal ENNReal SchwartzMap NumberField.AdeleRing

noncomputable section

section SystemL

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable (A : Type*) [AddCommGroup A] [Module E A]

structure HermL where

  form : A →ₗ[E] A →ₛₗ[conjHom F E] E

  herm : ∀ x y, form y x = conj F E (form x y)

  nonsingular : Function.Bijective form

variable {F E A}

namespace HermL

def unitaryGroup (h : HermL F E A) : Subgroup (A ≃ₗ[E] A) where
  carrier := {g | ∀ x y, h.form (g x) (g y) = h.form x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb x y := by
    change h.form (a (b x)) (a (b y)) = _
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    change h.form (a.symm x) (a.symm y) = _
    conv_rhs => rw [← a.apply_symm_apply x, ← a.apply_symm_apply y]
    rw [ha]

theorem mem_unitaryGroup {h : HermL F E A} {g : A ≃ₗ[E] A} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h.form (g x) (g y) = h.form x y := Iff.rfl

end HermL

end SystemL

def HermBridge.Statement : Prop :=
  ∀ (F E V : Type) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [AddCommGroup V] [Module E V],
    (∀ h : HermitianForm F E V, ∃! k : HermL F E V, ∀ x y, k.form x y = h.toSesq y x) ∧
    (∀ k : HermL F E V, ∃! h : HermitianForm F E V, ∀ x y, h.toSesq x y = k.form y x) ∧
    (∀ (h : HermitianForm F E V) (k : HermL F E V), (∀ x y, k.form x y = h.toSesq y x) →
      k.unitaryGroup = h.unitaryGroup)

section Tensor

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {A B : Type*} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]

def tensorHermitianPartial (hA : HermL F E A) (hB : HermL F E B) (a : A) (b : B) :
    A →ₛₗ[conjHom F E] B →ₛₗ[conjHom F E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (conjHom F E) (fun a' b' => hA.form a a' * hB.form b b')
    (fun _ _ _ => by rw [map_add, add_mul])
    (fun _ _ _ => by rw [LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, mul_assoc])
    (fun _ _ _ => by rw [map_add, mul_add])
    (fun _ _ _ => by rw [LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, mul_left_comm])

def tensHerm (hA : HermL F E A) (hB : HermL F E B) :
    A ⊗[E] B →ₗ[E] A ⊗[E] B →ₛₗ[conjHom F E] E :=
  TensorProduct.lift (LinearMap.mk₂ E (fun a b => TensorProduct.lift (tensorHermitianPartial hA hB a b))
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.add_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_add, LinearMap.add_apply, add_mul])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.smul_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_smul, smul_eq_mul, mul_assoc])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.add_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_add, LinearMap.add_apply, mul_add])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.smul_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_smul, smul_eq_mul]
      ring))

@[simp] theorem tensHerm_tmul (hA : HermL F E A) (hB : HermL F E B) (a a' : A) (b b' : B) :
    tensHerm hA hB (a ⊗ₜ b) (a' ⊗ₜ b') = hA.form a a' * hB.form b b' := by
  simp only [tensHerm, TensorProduct.lift.tmul, LinearMap.mk₂_apply, tensorHermitianPartial,
    LinearMap.mk₂'ₛₗ_apply]

variable [Module F A] [IsScalarTower F E A]

def weilForm (ξ : E) (hA : HermL F E A) (hB : HermL F E B) : LinearMap.BilinForm F (A ⊗[E] B) :=
  LinearMap.mk₂ F (fun w w' => Algebra.trace F E (ξ * tensHerm hA hB w w'))
    (fun _ _ _ => by rw [map_add, LinearMap.add_apply, mul_add, map_add])
    (fun c w w' => by
      rw [← algebraMap_smul E c w, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_left_comm,
        ← Algebra.smul_def, map_smul, smul_eq_mul])
    (fun _ _ _ => by rw [map_add, mul_add, map_add])
    (fun c w w' => by
      rw [← algebraMap_smul E c w', LinearMap.map_smulₛₗ, smul_eq_mul]
      change Algebra.trace F E (ξ * (conj F E (algebraMap F E c) * _)) = _
      rw [conj_algebraMap, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul])

theorem weilForm_apply (ξ : E) (hA : HermL F E A) (hB : HermL F E B) (w w' : A ⊗[E] B) :
    weilForm ξ hA hB w w' = Algebra.trace F E (ξ * tensHerm hA hB w w') := rfl

end Tensor

def TensHerm.Statement : Prop :=
  ∀ (F E A B : Type) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [AddCommGroup A] [Module E A] [Module.Free E A] [Module.Finite E A]
    [AddCommGroup B] [Module E B] [Module.Free E B] [Module.Finite E B]
    (hA : HermL F E A) (hB : HermL F E B),
    ∃ h : HermL F E (A ⊗[E] B), h.form = tensHerm hA hB

def WeilFormSymplectic.Statement : Prop :=
  ∀ (F E A B : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsReduced E]
    [AddCommGroup A] [Module E A] [Module F A] [IsScalarTower F E A] [Module.Free E A]
    [Module.Finite E A]
    [AddCommGroup B] [Module E B] [Module.Free E B] [Module.Finite E B]
    (ξ : E), IsUnit ξ → conj F E ξ = -ξ → ∀ (hA : HermL F E A) (hB : HermL F E B),
      (weilForm ξ hA hB).IsAlt ∧ (weilForm ξ hA hB).Nondegenerate

def WeilFormSwap.Statement : Prop :=
  ∀ (F E A B : Type) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [AddCommGroup A] [Module E A] [Module F A] [IsScalarTower F E A]
    [AddCommGroup B] [Module E B] [Module F B] [IsScalarTower F E B]
    (ξ : E) (hA : HermL F E A) (hB : HermL F E B) (w w' : A ⊗[E] B),
      weilForm ξ hB hA (TensorProduct.comm E A B w) (TensorProduct.comm E A B w') =
        weilForm ξ hA hB w w'

def UnitaryActsSymp.Statement : Prop :=
  ∀ (F E A B : Type) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [AddCommGroup A] [Module E A] [Module F A] [IsScalarTower F E A]
    [AddCommGroup B] [Module E B]
    (ξ : E) (hA : HermL F E A) (hB : HermL F E B),
    ∀ g ∈ hA.unitaryGroup, ∀ g' ∈ hB.unitaryGroup, ∀ w w' : A ⊗[E] B,
      weilForm ξ hA hB (TensorProduct.map g.toLinearMap g'.toLinearMap w)
          (TensorProduct.map g.toLinearMap g'.toLinearMap w') = weilForm ξ hA hB w w'

section Heisenberg

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

def Sp (ω : LinearMap.BilinForm R W) : Subgroup (W ≃ₗ[R] W) where
  carrier := {g | ∀ w w', ω (g w) (g w') = ω w w'}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb w w' := by
    change ω (a (b w)) (a (b w')) = _
    rw [ha, hb]
  inv_mem' {a} ha w w' := by
    change ω (a.symm w) (a.symm w') = _
    conv_rhs => rw [← a.apply_symm_apply w, ← a.apply_symm_apply w']
    rw [ha]

theorem mem_Sp {ω : LinearMap.BilinForm R W} {g : W ≃ₗ[R] W} :
    g ∈ Sp ω ↔ ∀ w w', ω (g w) (g w') = ω w w' := Iff.rfl

@[ext]
structure Heis (ω : LinearMap.BilinForm R W) where

  w : W

  t : R

variable {ω : LinearMap.BilinForm R W}

instance : One (Heis ω) := ⟨⟨0, 0⟩⟩

@[simp] theorem Heis.one_w : (1 : Heis ω).w = 0 := rfl

@[simp] theorem Heis.indicator_eq_one_of_true : (1 : Heis ω).t = 0 := rfl

variable [Invertible (2 : R)]

instance : Mul (Heis ω) := ⟨fun h h' => ⟨h.w + h'.w, h.t + h'.t + ⅟2 * ω h.w h'.w⟩⟩

instance : Inv (Heis ω) := ⟨fun h => ⟨-h.w, -h.t + ⅟2 * ω h.w h.w⟩⟩

@[simp] theorem Heis.mul_w (h h' : Heis ω) : (h * h').w = h.w + h'.w := rfl

@[simp] theorem Heis.product_torus_component (h h' : Heis ω) : (h * h').t = h.t + h'.t + ⅟2 * ω h.w h'.w := rfl

@[simp] theorem Heis.inv_w (h : Heis ω) : h⁻¹.w = -h.w := rfl

@[simp] theorem Heis.exists_inverse_fontaineElement_mem_fil_neg_one (h : Heis ω) : h⁻¹.t = -h.t + ⅟2 * ω h.w h.w := rfl

instance : Group (Heis ω) :=
  Group.ofLeftAxioms
    (fun a b c => by
      ext
      · simp [add_assoc]
      · simp only [Heis.product_torus_component, Heis.mul_w, map_add, LinearMap.add_apply]
        ring)
    (fun a => by ext <;> simp)
    (fun a => by
      ext
      · simp
      · simp only [Heis.product_torus_component, Heis.exists_inverse_fontaineElement_mem_fil_neg_one, Heis.inv_w, Heis.indicator_eq_one_of_true, map_neg, LinearMap.neg_apply]
        ring)

structure Polarization (ω : LinearMap.BilinForm R W) (X Y : Type*) [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] where

  e : (X × Y) ≃ₗ[R] W

  isotropic_X : ∀ x x' : X, ω (e (x, 0)) (e (x', 0)) = 0

  isotropic_Y : ∀ y y' : Y, ω (e (0, y)) (e (0, y')) = 0

namespace Polarization

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
variable (P : Polarization ω X Y)

def xPart (w : W) : X := (P.e.symm w).1

def yPart (w : W) : Y := (P.e.symm w).2

def xIncl : X →ₗ[R] W := P.e.toLinearMap ∘ₗ LinearMap.inl R X Y

def yIncl : Y →ₗ[R] W := P.e.toLinearMap ∘ₗ LinearMap.inr R X Y

def xProj : W →ₗ[R] X := LinearMap.fst R X Y ∘ₗ P.e.symm.toLinearMap

def XX : Submodule R W := LinearMap.range P.xIncl

def YY : Submodule R W := LinearMap.range P.yIncl

def pair (x : X) (y : Y) : R := ω (P.e (x, 0)) (P.e (0, y))

def Stabilizes (g : W ≃ₗ[R] W) : Prop :=
  (∀ x, P.yPart (g (P.e (x, 0))) = 0) ∧ (∀ y, P.xPart (g (P.e (0, y))) = 0)

def detX (g : W ≃ₗ[R] W) : R := LinearMap.det (P.xProj ∘ₗ g.toLinearMap ∘ₗ P.xIncl)

end Polarization

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

def schr (ψ : AddChar R Circle) (P : Polarization ω X Y) (h : Heis ω) (φ : X → ℂ) (x : X) : ℂ :=
  (ψ (h.t + P.pair x (P.yPart h.w) + ⅟2 * P.pair (P.xPart h.w) (P.yPart h.w)) : ℂ) *
    φ (x + P.xPart h.w)

end Heisenberg

def SchrRep.Statement : Prop :=
  ∀ (R W X Y : Type) [CommRing R] [Invertible (2 : R)] [AddCommGroup W] [Module R W]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (ω : LinearMap.BilinForm R W), ω.IsAlt → ∀ (ψ : AddChar R Circle) (P : Polarization ω X Y),
    (∀ (h h' : Heis ω) (φ : X → ℂ), schr ψ P (h * h') φ = schr ψ P h (schr ψ P h' φ)) ∧
    (∀ (t : R) (φ : X → ℂ), schr ψ P ⟨0, t⟩ φ = fun x => (ψ t : ℂ) * φ x) ∧
    (∀ (x₁ : X) (φ : X → ℂ) (x : X), schr ψ P ⟨P.e (x₁, 0), 0⟩ φ x = φ (x + x₁)) ∧
    (∀ (y : Y) (φ : X → ℂ) (x : X),
      schr ψ P ⟨P.e (0, y), 0⟩ φ x = (ψ (ω (P.e (x, 0)) (P.e (0, y))) : ℂ) * φ x) ∧
    (∀ (w w' : W) (φ : X → ℂ),
      schr ψ P ⟨w, 0⟩ (schr ψ P ⟨w', 0⟩ φ) =
        fun x => (ψ (ω w w') : ℂ) * schr ψ P ⟨w', 0⟩ (schr ψ P ⟨w, 0⟩ φ) x)

def IsSchwartzBruhat {X : Type*} [AddCommGroup X] [TopologicalSpace X] (φ : X → ℂ) : Prop :=
  (IsLocallyConstant φ ∧ HasCompactSupport φ) ∨
    ∃ (d : ℕ) (e : EuclideanSpace ℝ (Fin d) ≃ₜ+ X) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)),
      ∀ v, φ (e v) = f v

open Classical in

def absF {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
    (a : F) : ℝ≥0 :=
  if h : a = 0 then 0 else distribHaarChar F (Units.mk0 a h)

section Local

variable {F W X Y : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [LocallyCompactSpace F] [CharZero F]
  [AddCommGroup W] [Module F W] [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
  {ω : LinearMap.BilinForm F W}

def rXX (P : Polarization ω X Y) (g : W ≃ₗ[F] W) (φ : X → ℂ) (x : X) : ℂ :=
  (((absF (P.detX g) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * φ (P.xPart (g.symm (P.e (x, 0))))

def Implements [MeasurableSpace X] (ψ : AddChar F Circle) (P : Polarization ω X Y)
    (μ : Measure X) (g : W ≃ₗ[F] W) (M : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ (w : W) (f f' : Lp ℂ 2 μ), (f' : X → ℂ) =ᵐ[μ] schr ψ P ⟨w, 0⟩ f →
    (M f' : X → ℂ) =ᵐ[μ] schr ψ P ⟨g w, 0⟩ (M f)

variable (F W) in

abbrev linEquivTopology [TopologicalSpace W] : TopologicalSpace (W ≃ₗ[F] W) :=
  TopologicalSpace.induced (fun g : W ≃ₗ[F] W => (g : W → W)) Pi.topologicalSpace

def IsSplitting [TopologicalSpace W] [MeasurableSpace X] (ψ : AddChar F Circle)
    (P : Polarization ω X Y) (μ : Measure X) (G : Subgroup (W ≃ₗ[F] W))
    (om : G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) : Prop :=
  (∀ g : G, Implements ψ P μ (g : W ≃ₗ[F] W) (om g)) ∧
    (ConnectedSpace F → ∀ f : Lp ℂ 2 μ,
      letI : TopologicalSpace (W ≃ₗ[F] W) := linEquivTopology F W
      Continuous fun g : G => om g f)

def partialFourier {X' Y' : Type*} [AddCommGroup X'] [Module F X'] [AddCommGroup Y'] [Module F Y']
    [MeasurableSpace W] (ψ : AddChar F Circle) (P : Polarization ω X Y)
    (P' : Polarization ω X' Y') (P₂ : Submodule F W) (ν : Measure P₂) (Φ : X → ℂ) (x' : X') : ℂ :=
  ∫ p : P₂, Φ (P.xPart (P'.e (x', 0) + p)) * (ψ (ω p (P'.e (x', 0))) : ℂ) ∂ν

end Local

def SchrUnitary.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : Measure X) [μ.IsAddHaarMeasure],
    ∀ (h : Heis ω) (φ : X → ℂ), MemLp φ 2 μ →
      MemLp (schr ψ P h φ) 2 μ ∧ eLpNorm (schr ψ P h φ) 2 μ = eLpNorm φ 2 μ

def SchrSchwartzBruhat.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (h : Heis ω) (φ : X → ℂ), IsSchwartzBruhat φ → IsSchwartzBruhat (schr ψ P h φ)

def SchrIrreducible.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : Measure X) [μ.IsAddHaarMeasure],
    ∀ S : Submodule ℂ (Lp ℂ 2 μ), IsClosed (S : Set (Lp ℂ 2 μ)) →
      (∀ (h : Heis ω), ∀ f ∈ S, ∃ g ∈ S, (g : X → ℂ) =ᵐ[μ] schr ψ P h f) → S = ⊥ ∨ S = ⊤

def StoneVonNeumann.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : Measure X) [μ.IsAddHaarMeasure],
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
      (π : Heis ω →* (H →L[ℂ] H)),
      (∀ h v, ‖π h v‖ = ‖v‖) →
      (∀ v, Continuous fun p : W × F => π ⟨p.1, p.2⟩ v) →
      (∀ t, π ⟨0, t⟩ = (ψ t : ℂ) • ContinuousLinearMap.id ℂ H) →
      (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ h, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) →
      ∃ U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ, ∀ h v, (U (π h v) : X → ℂ) =ᵐ[μ] schr ψ P h (U v)

def ImplUnique.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : Measure X) [μ.IsAddHaarMeasure],
    ∀ g ∈ Sp ω, ∀ M M' : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      Implements ψ P μ g M → Implements ψ P μ g M' → ∃ c : ℂ, ∀ f, M' f = c • M f

def SplittingsDiffer.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : Measure X) [μ.IsAddHaarMeasure],
    ∀ G : Subgroup (W ≃ₗ[F] W), G ≤ Sp ω → ∀ om om' : G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ),
      IsSplitting ψ P μ G om → IsSplitting ψ P μ G om' →
      ∃ χ : G →* Circle, ∀ g f, om' g f = (χ g : ℂ) • om g f

def RXX.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : Measure X) [μ.IsAddHaarMeasure],
    ∀ g ∈ Sp ω, P.Stabilizes g →
      (∀ φ : X → ℂ, MemLp φ 2 μ → MemLp (rXX P g φ) 2 μ ∧ eLpNorm (rXX P g φ) 2 μ = eLpNorm φ 2 μ) ∧
      (∀ (h : Heis ω) (φ : X → ℂ), rXX P g (schr ψ P h φ) = schr ψ P ⟨g h.w, h.t⟩ (rXX P g φ)) ∧
      (∀ g' ∈ Sp ω, P.Stabilizes g' → ∀ φ : X → ℂ, rXX P (g * g') φ = rXX P g (rXX P g' φ))

def LemmaFP.Statement : Prop :=
  ∀ (F W X Y : Type) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    [AddCommGroup X] [Module F X] [TopologicalSpace X] [IsModuleTopology F X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup Y] [Module F Y],
    ¬ DiscreteTopology F → ∀ (ω : LinearMap.BilinForm F W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (X' Y' : Type) [AddCommGroup X'] [Module F X'] [TopologicalSpace X'] [IsModuleTopology F X']
      [AddCommGroup Y'] [Module F Y'] [MeasurableSpace W] [BorelSpace W]
      (P₁ P₂ Q₁ Q₂ : Submodule F W),
      iSupIndep (![P₁, P₂, Q₁, Q₂] : Fin 4 → Submodule F W) → P₁ ⊔ P₂ ⊔ Q₁ ⊔ Q₂ = ⊤ →
      (∀ u ∈ P₁ ⊔ P₂, ∀ v ∈ P₁ ⊔ P₂, ω u v = 0) → (∀ u ∈ Q₁ ⊔ Q₂, ∀ v ∈ Q₁ ⊔ Q₂, ω u v = 0) →
      (∀ p ∈ P₁, ∀ q ∈ Q₂, ω p q = 0) → (∀ p ∈ P₂, ∀ q ∈ Q₁, ω p q = 0) →
      ∀ (P' : Polarization ω X' Y'), P.XX = P₁ ⊔ P₂ → P.YY = Q₁ ⊔ Q₂ →
        P'.XX = P₁ ⊔ Q₂ → P'.YY = Q₁ ⊔ P₂ →
      ∀ (ν : Measure P₂) [ν.IsAddHaarMeasure],
        (∀ Φ : X → ℂ, IsSchwartzBruhat Φ → IsSchwartzBruhat (partialFourier ψ P P' P₂ ν Φ)) ∧
        (∀ Ψ : X' → ℂ, IsSchwartzBruhat Ψ →
          ∃! Φ : X → ℂ, IsSchwartzBruhat Φ ∧ partialFourier ψ P P' P₂ ν Φ = Ψ) ∧
        (∀ (h : Heis ω) (Φ : X → ℂ), IsSchwartzBruhat Φ →
          partialFourier ψ P P' P₂ ν (schr ψ P h Φ) = schr ψ P' h (partialFourier ψ P P' P₂ ν Φ)) ∧
        (∀ g ∈ Sp ω, P₁.map g.toLinearMap = P₁ → P₂.map g.toLinearMap = P₂ →
          Q₁.map g.toLinearMap = Q₁ → Q₂.map g.toLinearMap = Q₂ →
          ∀ Φ : X → ℂ, IsSchwartzBruhat Φ →
            partialFourier ψ P P' P₂ ν (rXX P g Φ) = rXX P' g (partialFourier ψ P P' P₂ ν Φ))

section Adelic

variable (K : Type*) [Field K] [NumberField K]

abbrev invertibleTwoAdele : Invertible (2 : 𝔸[K]) where
  invOf := algebraMap K 𝔸[K] (1 / 2)
  invOf_mul_self := by
    rw [← map_ofNat (algebraMap K 𝔸[K]) 2, ← map_mul]
    norm_num
  mul_invOf_self := by
    rw [← map_ofNat (algebraMap K 𝔸[K]) 2, ← map_mul]
    norm_num

variable {K}
variable {W X Y : Type*} [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] {ω : LinearMap.BilinForm K W}

def adelicPolEquiv (P : Polarization ω X Y) :
    (AdelicPoints K X × AdelicPoints K Y) ≃ₗ[𝔸[K]] AdelicPoints K W :=
  (TensorProduct.prodRight K 𝔸[K] 𝔸[K] X Y).symm ≪≫ₗ P.e.baseChange K 𝔸[K] (X × Y) W

theorem adelicPolEquiv_tmul_fst (P : Polarization ω X Y) (a : 𝔸[K]) (x : X) :
    adelicPolEquiv P (a ⊗ₜ x, 0) = a ⊗ₜ P.e (x, 0) := by
  rw [show ((a ⊗ₜ[K] x : AdelicPoints K X), (0 : AdelicPoints K Y)) = (a ⊗ₜ x, a ⊗ₜ (0 : Y)) by
    rw [TensorProduct.tmul_zero]]
  rw [adelicPolEquiv, LinearEquiv.trans_apply, TensorProduct.prodRight_symm_tmul,
    LinearEquiv.baseChange_tmul]

theorem adelicPolEquiv_tmul_snd (P : Polarization ω X Y) (a : 𝔸[K]) (y : Y) :
    adelicPolEquiv P (0, a ⊗ₜ y) = a ⊗ₜ P.e (0, y) := by
  rw [show ((0 : AdelicPoints K X), (a ⊗ₜ[K] y : AdelicPoints K Y)) = (a ⊗ₜ (0 : X), a ⊗ₜ y) by
    rw [TensorProduct.tmul_zero]]
  rw [adelicPolEquiv, LinearEquiv.trans_apply, TensorProduct.prodRight_symm_tmul,
    LinearEquiv.baseChange_tmul]

def Polarization.baseChange (P : Polarization ω X Y) :
    Polarization (ω.baseChange 𝔸[K]) (AdelicPoints K X) (AdelicPoints K Y) where
  e := adelicPolEquiv P
  isotropic_X x x' := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [Prod.mk_zero_zero, map_zero, LinearMap.zero_apply]
    | tmul a x =>
      induction x' using TensorProduct.induction_on with
      | zero => simp only [Prod.mk_zero_zero, map_zero]
      | tmul b x' =>
        rw [adelicPolEquiv_tmul_fst, adelicPolEquiv_tmul_fst,
          LinearMap.BilinForm.baseChange_tmul, P.isotropic_X]
        simp
      | add u v hu hv =>
        rw [show ((u + v : AdelicPoints K X), (0 : AdelicPoints K Y)) = (u, 0) + (v, 0) by simp,
          map_add, map_add, hu, hv, zero_add]
    | add u v hu hv =>
      rw [show ((u + v : AdelicPoints K X), (0 : AdelicPoints K Y)) = (u, 0) + (v, 0) by simp,
        map_add, map_add, LinearMap.add_apply, hu, hv, zero_add]
  isotropic_Y y y' := by
    induction y using TensorProduct.induction_on with
    | zero => simp only [Prod.mk_zero_zero, map_zero, LinearMap.zero_apply]
    | tmul a y =>
      induction y' using TensorProduct.induction_on with
      | zero => simp only [Prod.mk_zero_zero, map_zero]
      | tmul b y' =>
        rw [adelicPolEquiv_tmul_snd, adelicPolEquiv_tmul_snd,
          LinearMap.BilinForm.baseChange_tmul, P.isotropic_Y]
        simp
      | add u v hu hv =>
        rw [show ((0 : AdelicPoints K X), (u + v : AdelicPoints K Y)) = (0, u) + (0, v) by simp,
          map_add, map_add, hu, hv, zero_add]
    | add u v hu hv =>
      rw [show ((0 : AdelicPoints K X), (u + v : AdelicPoints K Y)) = (0, u) + (0, v) by simp,
        map_add, map_add, LinearMap.add_apply, hu, hv, zero_add]

end Adelic

def AdelicSchrUnitary.Statement : Prop :=
  ∀ (K W X Y : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ (P : Polarization ω X Y) (ψ : AddChar 𝔸[K] Circle), Continuous ψ →
    letI := invertibleTwoAdele K
    ∀ (h : Heis (ω.baseChange 𝔸[K])) (φ : AdelicPoints K X → ℂ),
      MemLp φ 2 (adelicPointsMeasure K X) →
        MemLp (schr ψ P.baseChange h φ) 2 (adelicPointsMeasure K X) ∧
        eLpNorm (schr ψ P.baseChange h φ) 2 (adelicPointsMeasure K X) =
          eLpNorm φ 2 (adelicPointsMeasure K X)

section Examples

def gaussFormL : GaussQ →ₗ[GaussQ] GaussQ →ₛₗ[conjHom ℚ GaussQ] GaussQ :=
  LinearMap.mk₂'ₛₗ (RingHom.id GaussQ) (conjHom ℚ GaussQ) (fun x y => x * conj ℚ GaussQ y)
    (fun _ _ _ => add_mul _ _ _)
    (fun c x y => by rw [smul_eq_mul, smul_eq_mul, RingHom.id_apply, mul_assoc])
    (fun x y y' => by rw [map_add, mul_add])
    (fun c x y => by
      show x * conj ℚ GaussQ (c * y) = conj ℚ GaussQ c * (x * conj ℚ GaussQ y)
      rw [map_mul]
      ring)

theorem gaussFormL_apply (x y : GaussQ) : gaussFormL x y = x * conj ℚ GaussQ y := rfl

def gaussHermL : HermL ℚ GaussQ GaussQ where
  form := gaussFormL
  herm x y := by
    rw [gaussFormL_apply, gaussFormL_apply, map_mul, conj_conj, mul_comm]
  nonsingular := by
    constructor
    · intro x x' hxx'
      have h := LinearMap.congr_fun hxx' 1
      rwa [gaussFormL_apply, gaussFormL_apply, map_one, mul_one, mul_one] at h
    · intro f
      refine ⟨f 1, LinearMap.ext fun y => ?_⟩
      have h := f.map_smulₛₗ y 1
      rw [smul_eq_mul, mul_one, smul_eq_mul] at h
      rw [gaussFormL_apply, h, mul_comm]
      rfl

theorem gaussHermL_one_one : gaussHermL.form 1 1 = 1 := by
  show (1 : GaussQ) * conj ℚ GaussQ 1 = 1
  rw [map_one, mul_one]

def gaussI : GaussQ := ⟨0, 1⟩

theorem conj_gaussI : conj ℚ GaussQ gaussI = -gaussI := by
  ext
  · rw [conj_gaussQ_re]; simp [gaussI]
  · rw [conj_gaussQ_im]; simp [gaussI]

theorem isUnit_gaussI : IsUnit gaussI := by
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  have := congrArg QuadraticAlgebra.im h
  simp [gaussI] at this

theorem weilForm_gauss : weilForm gaussI gaussHermL gaussHermL (1 ⊗ₜ 1) (gaussI ⊗ₜ 1) = 2 := by
  rw [weilForm_apply, tensHerm_tmul]
  show Algebra.trace ℚ GaussQ
    (gaussI * ((1 * conj ℚ GaussQ gaussI) * (1 * conj ℚ GaussQ 1))) = 2
  rw [conj_gaussI, map_one, trace_gaussQ]
  simp [gaussI]

theorem weilForm_gauss_ne_zero : weilForm gaussI gaussHermL gaussHermL ≠ 0 := by
  intro h
  have := weilForm_gauss
  rw [h] at this
  simp at this

def stdSymp (R : Type*) [CommRing R] : LinearMap.BilinForm R (R × R) :=
  LinearMap.mk₂ R (fun u v => u.1 * v.2 - u.2 * v.1)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

theorem stdSymp_apply (R : Type*) [CommRing R] (u v : R × R) :
    stdSymp R u v = u.1 * v.2 - u.2 * v.1 := rfl

theorem stdSymp_isAlt (R : Type*) [CommRing R] : (stdSymp R).IsAlt := fun u => by
  rw [stdSymp_apply]; ring

theorem stdSymp_nondegenerate (K : Type*) [Field K] : (stdSymp K).Nondegenerate := by
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · have h1 := hu (0, 1)
    have h2 := hu (1, 0)
    rw [stdSymp_apply] at h1 h2
    simp only [mul_one, mul_zero, sub_zero, zero_sub, neg_eq_zero] at h1 h2
    exact Prod.ext h1 h2
  · have h1 := hv (0, 1)
    have h2 := hv (1, 0)
    rw [stdSymp_apply] at h1 h2
    simp only [one_mul, zero_mul, sub_zero, zero_sub, neg_eq_zero] at h1 h2
    exact Prod.ext h1 h2

def stdPol (R : Type*) [CommRing R] : Polarization (stdSymp R) R R where
  e := LinearEquiv.refl R (R × R)
  isotropic_X x x' := by simp [stdSymp_apply]
  isotropic_Y y y' := by simp [stdSymp_apply]

theorem heis_std_noncomm :
    (⟨(1, 0), 0⟩ * ⟨(0, 1), 0⟩ : Heis (stdSymp ℝ)) ≠ ⟨(0, 1), 0⟩ * ⟨(1, 0), 0⟩ := by
  intro h
  have := congrArg Heis.t h
  simp only [Heis.product_torus_component, stdSymp_apply] at this
  norm_num at this

theorem schr_stdPol (ψ : AddChar ℝ Circle) (a b t : ℝ) (φ : ℝ → ℂ) (x : ℝ) :
    schr ψ (stdPol ℝ) ⟨(a, b), t⟩ φ x = (ψ (t + x * b + ⅟2 * (a * b)) : ℂ) * φ (x + a) := by
  simp [schr, Polarization.pair, Polarization.xPart, Polarization.yPart, stdPol, stdSymp_apply]

theorem real_hypotheses :
    ¬ DiscreteTopology ℝ ∧ (stdSymp ℝ).IsAlt ∧ (stdSymp ℝ).Nondegenerate ∧
      Continuous Real.fourierChar ∧ Real.fourierChar ≠ 1 := by
  refine ⟨fun h => ?_, stdSymp_isAlt ℝ, stdSymp_nondegenerate ℝ, Real.continuous_fourierChar,
    fun h => ?_⟩
  · obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set ℝ)) 0 rfl
    have : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have h0 : ε / 2 = 0 := hb this
    linarith
  · have h1 := congrArg (fun χ : AddChar ℝ Circle => ((χ (1 / 2) : Circle) : ℂ)) h
    simp only [Real.fourierChar_apply, AddChar.one_apply, Circle.coe_one] at h1
    rw [show ((2 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I] at h1
    norm_num at h1

theorem isSchwartzBruhat_gaussian :
    IsSchwartzBruhat (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin 1)) :
      EuclideanSpace ℝ (Fin 1) → ℂ) :=
  Or.inr ⟨1, ContinuousAddEquiv.refl _, GroundTheory.Global.gaussianSchwartz _, fun _ => rfl⟩

theorem gaussianSchwartz_ne_zero :
    (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) → ℂ) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [GroundTheory.Global.gaussianSchwartz_apply] at this

def adelicStdPol : Polarization ((stdSymp ℚ).baseChange 𝔸[ℚ]) (AdelicPoints ℚ ℚ) (AdelicPoints ℚ ℚ) :=
  (stdPol ℚ).baseChange

theorem schr_adelicStdPol_translate (ψ : AddChar 𝔸[ℚ] Circle) (q : ℚ)
    (φ : AdelicPoints ℚ ℚ → ℂ) (x : AdelicPoints ℚ ℚ) :
    letI := invertibleTwoAdele ℚ
    schr ψ adelicStdPol ⟨(1 : 𝔸[ℚ]) ⊗ₜ ((q, 0) : ℚ × ℚ), 0⟩ φ x = φ (x + (1 : 𝔸[ℚ]) ⊗ₜ q) := by
  have he : adelicStdPol.e ((1 : 𝔸[ℚ]) ⊗ₜ q, 0) = (1 : 𝔸[ℚ]) ⊗ₜ ((q, 0) : ℚ × ℚ) :=
    adelicPolEquiv_tmul_fst (stdPol ℚ) 1 q
  have hs : adelicStdPol.e.symm ((1 : 𝔸[ℚ]) ⊗ₜ ((q, 0) : ℚ × ℚ)) = ((1 : 𝔸[ℚ]) ⊗ₜ q, 0) := by
    rw [← he, LinearEquiv.symm_apply_apply]
  simp only [schr, Polarization.xPart, Polarization.yPart, Polarization.pair, hs,
    Prod.mk_zero_zero, map_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, Circle.coe_one,
    one_mul]

end Examples

end

end GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys
