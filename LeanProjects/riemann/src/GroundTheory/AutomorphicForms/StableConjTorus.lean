import Mathlib
import GroundTheory.AutomorphicForms.HermitianOrthogonal
import GroundTheory.AutomorphicForms.StableConjCyclic

namespace GroundTheory.Automorphic

open Module

section CommuteField

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem commute_of_commute_of_separable_charpoly {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  let K := AlgebraicClosure E
  let φ : E →+* K := algebraMap E K
  let Φ : Module.End E V →+* Matrix (Fin n) (Fin n) K :=
    φ.mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom
  let Ψ : Matrix (Fin n) (Fin n) K →+* Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv.toRingHom
  have hsep : (Ψ (Φ f)).charpoly.Separable := by
    change (Matrix.toLin' ((LinearMap.toMatrix b b f).map φ)).charpoly.Separable
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    exact hf.map
  have hc := commute_of_commute_of_separable hsep ((hg.map Φ).map Ψ) ((hg'.map Φ).map Ψ)
  have hinj : Function.Injective (Ψ.comp Φ) := by
    intro x y hxy
    have h1 : Φ x = Φ y := (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective hxy
    have h2 : LinearMap.toMatrixAlgEquiv b x = LinearMap.toMatrixAlgEquiv b y := by
      ext i j
      exact φ.injective (congrFun (congrFun h1 i) j)
    exact (LinearMap.toMatrixAlgEquiv b).injective h2
  change g * g' = g' * g
  apply hinj
  rw [map_mul, map_mul]
  exact hc.eq

end CommuteField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]

namespace HermitianForm

variable (h : HermitianForm F E V)

noncomputable def adjoint (A : Module.End E V) : Module.End E V where
  toFun y := (Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)
  map_add' x y := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, map_add, LinearMap.add_comp]
  map_smul' c x := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, LinearMap.map_smulₛₗ, LinearMap.smul_comp,
      RingHom.id_apply]

theorem toSesq_adjoint_left (A : Module.End E V) (y x : V) :
    h.toSesq (h.adjoint A y) x = h.toSesq y (A x) := by
  change h.toSesq ((Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)) x = _
  rw [Equiv.ofBijective_apply_symm_apply (⇑h.toSesq) h.nonsingular]
  rfl

theorem toSesq_adjoint_right (A : Module.End E V) (x y : V) :
    h.toSesq x (h.adjoint A y) = h.toSesq (A x) y := by
  rw [← h.conj_toSesq, toSesq_adjoint_left, h.conj_toSesq]

theorem eq_adjoint_iff (A B : Module.End E V) :
    B = h.adjoint A ↔ ∀ y x, h.toSesq (B y) x = h.toSesq y (A x) := by
  refine ⟨fun hB y x => hB ▸ h.toSesq_adjoint_left A y x, fun hB => LinearMap.ext fun y => ?_⟩
  apply h.nonsingular.1
  ext x
  rw [hB, toSesq_adjoint_left]

theorem adjoint_mul (A B : Module.End E V) : h.adjoint (A * B) = h.adjoint B * h.adjoint A := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rw [Module.End.mul_apply, toSesq_adjoint_left, toSesq_adjoint_left, Module.End.mul_apply]

theorem adjoint_one : h.adjoint 1 = 1 := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rfl

noncomputable def adjointEquiv (g : V ≃ₗ[E] V) : V ≃ₗ[E] V where
  toLinearMap := h.adjoint g.toLinearMap
  invFun := h.adjoint g.symm.toLinearMap
  left_inv x := by
    change (h.adjoint g.symm.toLinearMap * h.adjoint g.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.toLinearMap * g.symm.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl
  right_inv x := by
    change (h.adjoint g.toLinearMap * h.adjoint g.symm.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.symm.toLinearMap * g.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl

theorem toSesq_adjointEquiv_left (g : V ≃ₗ[E] V) (y x : V) :
    h.toSesq (h.adjointEquiv g y) x = h.toSesq y (g x) :=
  h.toSesq_adjoint_left _ y x

theorem toSesq_adjointEquiv_right (g : V ≃ₗ[E] V) (x y : V) :
    h.toSesq x (h.adjointEquiv g y) = h.toSesq (g x) y :=
  h.toSesq_adjoint_right _ x y

theorem eq_adjointEquiv_iff (g b : V ≃ₗ[E] V) :
    b = h.adjointEquiv g ↔ ∀ y x, h.toSesq (b y) x = h.toSesq y (g x) := by
  refine ⟨fun hb y x => hb ▸ h.toSesq_adjointEquiv_left g y x, fun hb => ?_⟩
  apply LinearEquiv.ext fun y => ?_
  apply h.nonsingular.1
  ext x
  rw [hb, toSesq_adjointEquiv_left]

theorem adjointEquiv_mul (a b : V ≃ₗ[E] V) :
    h.adjointEquiv (a * b) = h.adjointEquiv b * h.adjointEquiv a := by
  symm
  rw [eq_adjointEquiv_iff]
  intro y x
  rw [LinearEquiv.mul_apply, toSesq_adjointEquiv_left, toSesq_adjointEquiv_left,
    LinearEquiv.mul_apply]

theorem adjointEquiv_one : h.adjointEquiv 1 = 1 := by
  symm
  rw [eq_adjointEquiv_iff]
  intro y x
  rfl

theorem adjointEquiv_adjointEquiv (a : V ≃ₗ[E] V) : h.adjointEquiv (h.adjointEquiv a) = a := by
  symm
  rw [eq_adjointEquiv_iff]
  intro y x
  rw [toSesq_adjointEquiv_right]

theorem adjointEquiv_inv (a : V ≃ₗ[E] V) : h.adjointEquiv a⁻¹ = (h.adjointEquiv a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← adjointEquiv_mul, mul_inv_cancel, adjointEquiv_one]

theorem toSesq_apply_apply (g : V ≃ₗ[E] V) (x y : V) :
    h.toSesq (g x) (g y) = h.toSesq ((h.adjointEquiv g * g) x) y := by
  rw [LinearEquiv.mul_apply, toSesq_adjointEquiv_left]

theorem mem_unitaryGroup_iff_adjointEquiv_mul (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔ h.adjointEquiv g * g = 1 := by
  rw [mem_unitaryGroup]
  constructor
  · intro hg
    apply LinearEquiv.ext fun x => h.nonsingular.1 (LinearMap.ext fun y => ?_)
    rw [← toSesq_apply_apply, hg]
    rfl
  · intro hg x y
    rw [toSesq_apply_apply, hg]
    rfl

theorem mem_unitaryGroup_iff_adjointEquiv (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔ h.adjointEquiv g = g⁻¹ := by
  rw [mem_unitaryGroup_iff_adjointEquiv_mul, mul_eq_one_iff_eq_inv]

theorem forall_toSesq_eq_iff (g c : V ≃ₗ[E] V) :
    (∀ x y, h.toSesq (g x) (g y) = h.toSesq (c x) y) ↔ h.adjointEquiv g * g = c := by
  constructor
  · intro hg
    apply LinearEquiv.ext fun x => h.nonsingular.1 (LinearMap.ext fun y => ?_)
    rw [← toSesq_apply_apply, hg]
  · intro hg x y
    rw [toSesq_apply_apply, hg]

noncomputable def twist (c : V ≃ₗ[E] V) (hc : h.adjointEquiv c = c) : HermitianForm F E V where
  toSesq := h.toSesq.comp c.toLinearMap
  isSymm := ⟨fun x y => by
    change conjHom F E (h.toSesq (c x) y) = h.toSesq (c y) x
    rw [conjHom_apply, h.conj_toSesq, ← hc, toSesq_adjointEquiv_left, hc]⟩
  nonsingular := h.nonsingular.comp c.bijective

end HermitianForm

section Stable

variable [FiniteDimensional E V]

def IsRegularSemisimple (γ : V ≃ₗ[E] V) : Prop :=
  (γ.toLinearMap).charpoly.Separable

def StablyConjugate (γ γ' : V ≃ₗ[E] V) : Prop :=
  ∃ g : V ≃ₗ[E] V, g * γ * g⁻¹ = γ'

def torusE (γ : V ≃ₗ[E] V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.centralizer {γ}

omit [FiniteDimensional E V] in
theorem mem_torusE {γ t : V ≃ₗ[E] V} : t ∈ torusE γ ↔ γ * t = t * γ := by
  simp [torusE, Subgroup.mem_centralizer_iff]

omit [FiniteDimensional E V] in
theorem commute_toLinearMap {a b : V ≃ₗ[E] V} (hab : a * b = b * a) :
    Commute a.toLinearMap b.toLinearMap :=
  LinearMap.ext fun x => DFunLike.congr_fun hab x

theorem torusE_mul_comm {γ a b : V ≃ₗ[E] V} (hγ : IsRegularSemisimple γ) (ha : a ∈ torusE γ)
    (hb : b ∈ torusE γ) : a * b = b * a := by
  have hc := commute_of_commute_of_separable_charpoly hγ
    (commute_toLinearMap (mem_torusE.1 ha)) (commute_toLinearMap (mem_torusE.1 hb))
  exact LinearEquiv.ext fun x => LinearMap.congr_fun hc.eq x

def TorusE (γ : V ≃ₗ[E] V) : Type _ := torusE γ

namespace TorusE

variable {γ : V ≃ₗ[E] V}

instance [Fact (IsRegularSemisimple γ)] : CommGroup (TorusE γ) :=
  { (inferInstance : Group (torusE γ)) with
    mul_comm := fun a b => Subtype.ext (torusE_mul_comm Fact.out a.2 b.2) }

def val (t : TorusE γ) : V ≃ₗ[E] V := Subtype.val (p := (· ∈ torusE γ)) t

omit [FiniteDimensional E V] in
theorem val_mem (t : TorusE γ) : t.val ∈ torusE γ := Subtype.prop (p := (· ∈ torusE γ)) t

def mk (t : V ≃ₗ[E] V) (ht : t ∈ torusE γ) : TorusE γ := (⟨t, ht⟩ : torusE γ)

omit [FiniteDimensional E V] in
@[simp] theorem val_mk (t : V ≃ₗ[E] V) (ht : t ∈ torusE γ) : (mk t ht).val = t := rfl

omit [FiniteDimensional E V] in
theorem ext {a b : TorusE γ} (hab : a.val = b.val) : a = b :=
  Subtype.ext (p := (· ∈ torusE γ)) hab

variable [Fact (IsRegularSemisimple γ)]

@[simp] theorem val_mul (a b : TorusE γ) : (a * b).val = a.val * b.val := rfl

@[simp] theorem val_one : (1 : TorusE γ).val = 1 := rfl

@[simp] theorem val_inv (a : TorusE γ) : a⁻¹.val = a.val⁻¹ := rfl

end TorusE

end Stable

end GroundTheory.Automorphic
