import Mathlib
import GroundTheory.AutomorphicForms.StableConjTorus

namespace GroundTheory.Automorphic

open Module

theorem mul_comm_of_mul_inv_comm {G : Type*} [Group G] {a x : G} (hx : x * a⁻¹ = a⁻¹ * x) :
    a * x = x * a := by
  calc a * x = a * (x * a⁻¹) * a := by group
    _ = a * (a⁻¹ * x) * a := by rw [hx]
    _ = x * a := by group

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

namespace HermitianForm

variable (h : HermitianForm F E V)

omit [FiniteDimensional E V] in

theorem adjointEquiv_mem_torusE {γ t : V ≃ₗ[E] V} (hγ : γ ∈ h.unitaryGroup)
    (ht : t ∈ torusE γ) : h.adjointEquiv t ∈ torusE γ := by
  rw [mem_torusE] at *
  have h1 := congrArg h.adjointEquiv ht
  rw [adjointEquiv_mul, adjointEquiv_mul, (h.mem_unitaryGroup_iff_adjointEquiv γ).1 hγ] at h1
  exact mul_comm_of_mul_inv_comm h1

omit [FiniteDimensional E V] in

theorem conj_mem_unitaryGroup_iff {γ : V ≃ₗ[E] V} (hγ : γ ∈ h.unitaryGroup) (g : V ≃ₗ[E] V) :
    g * γ * g⁻¹ ∈ h.unitaryGroup ↔ h.adjointEquiv g * g ∈ torusE γ := by
  have hγ' := (h.mem_unitaryGroup_iff_adjointEquiv γ).1 hγ
  rw [mem_unitaryGroup_iff_adjointEquiv_mul, mem_torusE, adjointEquiv_mul, adjointEquiv_mul,
    adjointEquiv_inv, hγ']
  set A := h.adjointEquiv g
  constructor
  · intro hX
    calc γ * (A * g) = γ * A * ((A⁻¹ * (γ⁻¹ * A)) * (g * γ * g⁻¹)) * g := by rw [hX]; group
      _ = A * g * γ := by group
  · intro hc
    calc A⁻¹ * (γ⁻¹ * A) * (g * γ * g⁻¹) = A⁻¹ * γ⁻¹ * ((A * g) * γ) * g⁻¹ := by group
      _ = A⁻¹ * γ⁻¹ * (γ * (A * g)) * g⁻¹ := by rw [hc]
      _ = 1 := by group

omit [FiniteDimensional E V] in

theorem mul_inv_mem_unitaryGroup {a b : V ≃ₗ[E] V}
    (hab : h.adjointEquiv a * a = h.adjointEquiv b * b) : b * a⁻¹ ∈ h.unitaryGroup := by
  rw [mem_unitaryGroup_iff_adjointEquiv_mul, adjointEquiv_mul, adjointEquiv_inv]
  calc (h.adjointEquiv a)⁻¹ * h.adjointEquiv b * (b * a⁻¹)
      = (h.adjointEquiv a)⁻¹ * (h.adjointEquiv b * b) * a⁻¹ := by group
    _ = 1 := by rw [← hab]; group

variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]

noncomputable def torusStar : TorusE (γ : V ≃ₗ[E] V) →* TorusE (γ : V ≃ₗ[E] V) where
  toFun t := TorusE.mk (h.adjointEquiv t.val) (h.adjointEquiv_mem_torusE γ.2 t.val_mem)
  map_one' := TorusE.ext (by simp [adjointEquiv_one])
  map_mul' a b := by
    rw [mul_comm a b]
    exact TorusE.ext (by simp [adjointEquiv_mul])

@[simp] theorem val_torusStar (t : TorusE (γ : V ≃ₗ[E] V)) :
    (h.torusStar γ t).val = h.adjointEquiv t.val := rfl

theorem torusStar_torusStar (t : TorusE (γ : V ≃ₗ[E] V)) : h.torusStar γ (h.torusStar γ t) = t :=
  TorusE.ext (by simp [adjointEquiv_adjointEquiv])

noncomputable def torusNorm : TorusE (γ : V ≃ₗ[E] V) →* TorusE (γ : V ≃ₗ[E] V) :=
  h.torusStar γ * MonoidHom.id _

theorem torusNorm_apply (t : TorusE (γ : V ≃ₗ[E] V)) : h.torusNorm γ t = h.torusStar γ t * t :=
  rfl

noncomputable def selfAdjointTorus : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  MonoidHom.eqLocus (h.torusStar γ) (MonoidHom.id _)

theorem mem_selfAdjointTorus {c : TorusE (γ : V ≃ₗ[E] V)} :
    c ∈ h.selfAdjointTorus γ ↔ h.torusStar γ c = c := Iff.rfl

noncomputable def normTorus : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  (h.torusNorm γ).range

theorem normTorus_le : h.normTorus γ ≤ h.selfAdjointTorus γ := by
  rintro _ ⟨t, rfl⟩
  rw [mem_selfAdjointTorus, torusNorm_apply, map_mul, torusStar_torusStar, mul_comm]

abbrev centralizerTorusFirstCohomology := h.selfAdjointTorus γ ⧸ (h.normTorus γ).subgroupOf (h.selfAdjointTorus γ)

noncomputable def torusF : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  (h.torusNorm γ).ker

theorem mem_torusF_iff (t : TorusE (γ : V ≃ₗ[E] V)) :
    t ∈ h.torusF γ ↔ t.val ∈ h.unitaryGroup := by
  rw [torusF, MonoidHom.mem_ker, torusNorm_apply, mem_unitaryGroup_iff_adjointEquiv_mul]
  constructor
  · intro ht; simpa using congrArg TorusE.val ht
  · intro ht; exact TorusE.ext (by simpa using ht)

theorem mk_eq_mk_iff (c c' : h.selfAdjointTorus γ) :
    (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c' ↔
      ∃ t, (c' : TorusE (γ : V ≃ₗ[E] V)) = c * h.torusNorm γ t := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    simp
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simp [ht]

noncomputable def normOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    h.selfAdjointTorus γ :=
  ⟨TorusE.mk (h.adjointEquiv g * g) ((h.conj_mem_unitaryGroup_iff γ.2 g).1 hg),
    TorusE.ext (by simp [adjointEquiv_mul, adjointEquiv_adjointEquiv])⟩

@[simp] theorem val_normOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    (h.normOf γ g hg : TorusE (γ : V ≃ₗ[E] V)).val = h.adjointEquiv g * g := rfl

noncomputable def invOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) : h.centralizerTorusFirstCohomology γ :=
  QuotientGroup.mk (h.normOf γ g hg)

theorem normOf_eq_of_adjoint (g g' : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup)
    (hg' : g' * γ * g'⁻¹ ∈ h.unitaryGroup)
    (hgg : h.adjointEquiv g * g = h.adjointEquiv g' * g') : h.normOf γ g hg = h.normOf γ g' hg' :=
  Subtype.ext (TorusE.ext hgg)

theorem invOf_eq_of_eq (g g' : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup)
    (hg' : g' * γ * g'⁻¹ ∈ h.unitaryGroup) (heq : g * γ * g⁻¹ = g' * γ * g'⁻¹) :
    h.invOf γ g hg = h.invOf γ g' hg' := by
  have htE : g⁻¹ * g' ∈ torusE (γ : V ≃ₗ[E] V) := by
    rw [mem_torusE]
    calc (γ : V ≃ₗ[E] V) * (g⁻¹ * g') = g⁻¹ * (g * γ * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * γ * g'⁻¹) * g' := by rw [heq]
      _ = g⁻¹ * g' * γ := by group
  set t := TorusE.mk _ htE
  rw [invOf, invOf, mk_eq_mk_iff]
  refine ⟨t, ?_⟩
  have hc : (h.normOf γ g hg : TorusE (γ : V ≃ₗ[E] V)) * h.torusNorm γ t =
      h.torusStar γ t * h.normOf γ g hg * t := by
    rw [torusNorm_apply]
    simp only [mul_comm, mul_left_comm]
  rw [hc]
  apply TorusE.ext
  simp only [TorusE.val_mul, val_torusStar, val_normOf, t, TorusE.val_mk, adjointEquiv_mul,
    adjointEquiv_inv]
  group

noncomputable def stableInv (γ' : V ≃ₗ[E] V) : h.centralizerTorusFirstCohomology γ := by
  classical
  exact if H : ∃ g : V ≃ₗ[E] V, g * γ * g⁻¹ = γ' ∧ γ' ∈ h.unitaryGroup then
    h.invOf γ H.choose (by rw [H.choose_spec.1]; exact H.choose_spec.2) else 1

theorem stableInv_conj (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    h.stableInv γ (g * γ * g⁻¹) = h.invOf γ g hg := by
  have H : ∃ g' : V ≃ₗ[E] V, g' * γ * g'⁻¹ = g * γ * g⁻¹ ∧ g * γ * g⁻¹ ∈ h.unitaryGroup :=
    ⟨g, rfl, hg⟩
  rw [stableInv, dif_pos H]
  exact h.invOf_eq_of_eq γ _ _ _ _ H.choose_spec.1

theorem stableInv_self : h.stableInv γ γ = 1 := by
  have hg : (1 : V ≃ₗ[E] V) * γ * 1⁻¹ ∈ h.unitaryGroup := by simp
  have := h.stableInv_conj γ 1 hg
  simp only [one_mul, inv_one, mul_one] at this
  have h1 : h.normOf γ 1 hg = 1 := Subtype.ext (TorusE.ext (by simp [adjointEquiv_one]))
  rw [this, invOf, h1, QuotientGroup.mk_one]

theorem stableInv_eq_stableInv_iff {γ₁ γ₂ : V ≃ₗ[E] V} (h₁ : γ₁ ∈ h.unitaryGroup)
    (h₂ : γ₂ ∈ h.unitaryGroup) (s₁ : StablyConjugate (γ : V ≃ₗ[E] V) γ₁)
    (s₂ : StablyConjugate (γ : V ≃ₗ[E] V) γ₂) :
    h.stableInv γ γ₁ = h.stableInv γ γ₂ ↔ ∃ u ∈ h.unitaryGroup, u * γ₁ * u⁻¹ = γ₂ := by
  obtain ⟨g₁, rfl⟩ := s₁
  obtain ⟨g₂, rfl⟩ := s₂
  rw [stableInv_conj _ _ _ h₁, stableInv_conj _ _ _ h₂]
  constructor
  · intro heq
    rw [invOf, invOf, mk_eq_mk_iff] at heq
    obtain ⟨t, ht⟩ := heq
    have htγ := mem_torusE.1 t.val_mem
    set a := g₁ * t.val with ha
    have hc : (h.normOf γ g₁ h₁ : TorusE (γ : V ≃ₗ[E] V)) * h.torusNorm γ t =
        h.torusStar γ t * h.normOf γ g₁ h₁ * t := by
      rw [torusNorm_apply]
      simp only [mul_comm, mul_left_comm]
    have key : h.adjointEquiv a * a = h.adjointEquiv g₂ * g₂ := by
      have := congrArg TorusE.val (ht.trans hc)
      simp only [TorusE.val_mul, val_torusStar, val_normOf] at this
      rw [this, ha, adjointEquiv_mul]
      group
    refine ⟨g₂ * a⁻¹, h.mul_inv_mem_unitaryGroup key, ?_⟩
    calc g₂ * a⁻¹ * (g₁ * γ * g₁⁻¹) * (g₂ * a⁻¹)⁻¹
        = g₂ * t.val⁻¹ * (γ * t.val) * g₂⁻¹ := by simp only [a]; group
      _ = g₂ * t.val⁻¹ * (t.val * γ) * g₂⁻¹ := by rw [htγ]
      _ = g₂ * γ * g₂⁻¹ := by group
  · rintro ⟨u, hu, hu'⟩
    have hug : (u * g₁) * γ * (u * g₁)⁻¹ = g₂ * γ * g₂⁻¹ := by
      rw [← hu']; group
    have hug' : (u * g₁) * γ * (u * g₁)⁻¹ ∈ h.unitaryGroup := by rw [hug]; exact h₂
    rw [← h.invOf_eq_of_eq γ _ _ hug' h₂ hug, invOf, invOf,
      h.normOf_eq_of_adjoint γ (u * g₁) g₁ hug' h₁]
    rw [adjointEquiv_mul, (h.mem_unitaryGroup_iff_adjointEquiv u).1 hu]
    group

noncomputable def twistOf (c : h.selfAdjointTorus γ) : HermitianForm F E V :=
  h.twist (c : TorusE (γ : V ≃ₗ[E] V)).val (congrArg TorusE.val c.2)

theorem twistOf_apply (c : h.selfAdjointTorus γ) (x y : V) :
    (h.twistOf γ c).toSesq x y = h.toSesq ((c : TorusE (γ : V ≃ₗ[E] V)).val x) y := rfl

theorem twistOf_isometric_of_mk_eq {c c' : h.selfAdjointTorus γ}
    (hcc : (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c') :
    Isometric (h.twistOf γ c) (h.twistOf γ c') := by
  rw [mk_eq_mk_iff] at hcc
  obtain ⟨t, ht⟩ := hcc
  have hc : (c : TorusE (γ : V ≃ₗ[E] V)) * h.torusNorm γ t =
      h.torusStar γ t * c * t := by
    rw [torusNorm_apply]
    simp only [mul_comm, mul_left_comm]
  refine Isometric.symm ⟨t.val, fun x y => ?_⟩
  rw [twistOf_apply, twistOf_apply, ← h.toSesq_adjointEquiv_left t.val, ht, hc]
  rfl

def InKernel (x : h.centralizerTorusFirstCohomology γ) : Prop :=
  Quotient.liftOn' x (fun c => Isometric (h.twistOf γ c) h) fun c c' hr => propext (by
    have hcc : (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c' := Quotient.sound hr
    exact ⟨fun H => (h.twistOf_isometric_of_mk_eq γ hcc).symm.trans H,
      fun H => (h.twistOf_isometric_of_mk_eq γ hcc).trans H⟩)

theorem inKernel_mk (c : h.selfAdjointTorus γ) :
    h.InKernel γ (QuotientGroup.mk c) ↔ Isometric (h.twistOf γ c) h := Iff.rfl

theorem exists_stableInv_eq_iff (x : h.centralizerTorusFirstCohomology γ) :
    (∃ γ' ∈ h.unitaryGroup, StablyConjugate (γ : V ≃ₗ[E] V) γ' ∧ h.stableInv γ γ' = x) ↔
      h.InKernel γ x := by
  induction x using QuotientGroup.induction_on with
  | H c =>
  rw [inKernel_mk]
  constructor
  · rintro ⟨_, hU, ⟨g, rfl⟩, hinv⟩
    rw [stableInv_conj _ _ _ hU, invOf] at hinv
    have H0 : Isometric (h.twistOf γ (h.normOf γ g hU)) h :=
      ⟨g, fun x y => by rw [twistOf_apply, val_normOf, toSesq_apply_apply]⟩
    exact (h.twistOf_isometric_of_mk_eq γ hinv).symm.trans H0
  · rintro ⟨e, he⟩
    have hee : h.adjointEquiv e * e = (c : TorusE (γ : V ≃ₗ[E] V)).val :=
      (h.forall_toSesq_eq_iff e _).1 fun x y => (he x y).trans (twistOf_apply _ _ _ _ _)
    have hU : e * γ * e⁻¹ ∈ h.unitaryGroup := by
      rw [h.conj_mem_unitaryGroup_iff γ.2, hee]
      exact (c : TorusE (γ : V ≃ₗ[E] V)).val_mem
    refine ⟨_, hU, ⟨e, rfl⟩, ?_⟩
    rw [stableInv_conj _ _ _ hU, invOf]
    congr 1
    exact Subtype.ext (TorusE.ext hee)

end HermitianForm

end GroundTheory.Automorphic
