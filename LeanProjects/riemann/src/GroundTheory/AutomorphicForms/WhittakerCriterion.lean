import Mathlib
import GroundTheory.AutomorphicForms.HeckeAlgebra
import GroundTheory.AutomorphicForms.SmoothRepContragredient
import GroundTheory.AutomorphicForms.SmoothRepSchur

noncomputable section

namespace GroundTheory.Automorphic

namespace Whittaker

open Set Filter Topology MeasureTheory

section Translations

variable {X : Type*} [TopologicalSpace X]

def compHomeoL (e : X ≃ₜ X) :
    locallyConstantCompactSupport X ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport X ℂ ℂ where
  toFun f := ⟨(f : X → ℂ) ∘ e, mem_locallyConstantCompactSupport.2
    ⟨f.2.1.comp_continuous e.continuous, f.2.2.comp_homeomorph e⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_compHomeoL (e : X ≃ₜ X) (f : locallyConstantCompactSupport X ℂ ℂ) :
    ((compHomeoL e f : locallyConstantCompactSupport X ℂ ℂ) : X → ℂ) = (f : X → ℂ) ∘ e := rfl

theorem compHomeoL_symm_apply (e : X ≃ₜ X) (f : locallyConstantCompactSupport X ℂ ℂ) :
    compHomeoL e (compHomeoL e.symm f) = f :=
  Subtype.ext (funext fun x => by simp)

theorem compHomeoL_apply_symm (e : X ≃ₜ X) (f : locallyConstantCompactSupport X ℂ ℂ) :
    compHomeoL e.symm (compHomeoL e f) = f :=
  Subtype.ext (funext fun x => by simp)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def biTranslL (a b : G) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport G ℂ ℂ :=
  compHomeoL ((Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight b))

@[simp]
theorem coe_biTranslL (a b : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ((biTranslL a b f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) =
      fun x => (f : G → ℂ) (a⁻¹ * x * b) := rfl

def rtransL (g : G) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport G ℂ ℂ :=
  compHomeoL (Homeomorph.mulRight g)

@[simp]
theorem coe_rtransL (g : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ((rtransL g f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) = fun x => (f : G → ℂ) (x * g) :=
  rfl

def ltransL (a : G) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport G ℂ ℂ :=
  compHomeoL (Homeomorph.mulLeft a⁻¹)

@[simp]
theorem coe_ltransL (a : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ((ltransL a f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) = fun x => (f : G → ℂ) (a⁻¹ * x) :=
  rfl

theorem biTranslL_eq (a b : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    biTranslL a b f = ltransL a (rtransL b f) :=
  Subtype.ext (funext fun x => by simp [mul_assoc])

end Translations

section Distributions

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def BiEquivariantSigmaInvariant (H : Subgroup G) (χ : H → ℂ) (σ : G ≃ₜ G) : Prop :=
  ∀ D : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ),
    (∀ (f : locallyConstantCompactSupport G ℂ ℂ) (h₁ h₂ : H),
      D (biTranslL (h₁ : G) (h₂ : G) f) = χ h₁ * (χ h₂)⁻¹ * D f) →
    ∀ f, D (compHomeoL σ f) = D f

omit [IsTopologicalGroup G] in

theorem map_inv_of_antiHom (σ : G ≃ₜ G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (x : G) :
    σ x⁻¹ = (σ x)⁻¹ := by
  have h1 : σ 1 = 1 := by
    have := hσ 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  rw [eq_inv_iff_mul_eq_one, ← hσ, mul_inv_cancel, h1]

theorem BiEquivariantSigmaInvariant.inv {H : Subgroup G} {χ : H → ℂ} {σ : G ≃ₜ G}
    (hσ : ∀ x y, σ (x * y) = σ y * σ x) (h : BiEquivariantSigmaInvariant H χ σ) :
    BiEquivariantSigmaInvariant H (fun g => (χ g)⁻¹) σ := by
  intro D hD f
  set ι : G ≃ₜ G := Homeomorph.inv G
  set D' : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) := D ∘ₗ compHomeoL ι
  have hD' : ∀ (f : locallyConstantCompactSupport G ℂ ℂ) (h₁ h₂ : H),
      D' (biTranslL (h₁ : G) (h₂ : G) f) = χ h₁ * (χ h₂)⁻¹ * D' f := by
    intro f h₁ h₂
    have e : compHomeoL ι (biTranslL (h₁ : G) (h₂ : G) f) =
        biTranslL (h₂ : G) (h₁ : G) (compHomeoL ι f) :=
      Subtype.ext (funext fun x => by simp [ι, mul_assoc])
    simp only [D', LinearMap.comp_apply, e, hD]
    rw [inv_inv]
    ring
  have key := h D' hD'
  have e : compHomeoL ι (compHomeoL σ f) = compHomeoL σ (compHomeoL ι f) :=
    Subtype.ext (funext fun x => by simp [ι, map_inv_of_antiHom σ hσ])
  have hιι : ∀ g : locallyConstantCompactSupport G ℂ ℂ, compHomeoL ι (compHomeoL ι g) = g :=
    fun g => Subtype.ext (funext fun x => by simp [ι])
  calc D (compHomeoL σ f) = D' (compHomeoL ι (compHomeoL σ f)) := by
        simp only [D', LinearMap.comp_apply, hιι]
    _ = D' (compHomeoL σ (compHomeoL ι f)) := by rw [e]
    _ = D' (compHomeoL ι f) := key _
    _ = D f := by simp only [D', LinearMap.comp_apply, hιι]

end Distributions

section Hecke

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeAct_apply_act [μ.IsMulRightInvariant] {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V}
    (hv : v ∈ smoothVectors ρ) (g : G) :
    heckeAct μ ρ f (ρ g v) = heckeAct μ ρ (fun x => f (x * g⁻¹)) v := by
  have hf' : (fun x => f (x * g⁻¹)) ∈ locallyConstantCompactSupport G ℂ ℂ :=
    (rtransL g⁻¹ ⟨f, hf⟩).2
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ hf (smooth_apply_mem ρ hv g), dual_heckeAct μ hf' hv,
    ← integral_mul_right_eq_self (fun x => f (x * g⁻¹) * φ (ρ x v)) g]
  simp only [mul_inv_cancel_right, map_mul, Module.End.mul_apply]

def normInd (K : Subgroup G) : G → ℂ :=
  (K : Set G).indicator fun _ => ((μ.real (K : Set G))⁻¹ : ℂ)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [BorelSpace G] [μ.IsHaarMeasure] in
theorem normInd_mem {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    normInd μ K ∈ locallyConstantCompactSupport G ℂ ℂ :=
  indicator_mem_locallyConstantCompactSupport hKc hKo _

omit [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in

theorem heckeAct_normInd {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    {v : V} (hv : v ∈ fixedVectors ρ K) : heckeAct μ ρ (normInd μ K) v = v := by
  have hvs : v ∈ smoothVectors ρ := mem_smoothVectors_of_mem_fixedVectors hKo hv
  have hK0 : μ.real (K : Set G) ≠ 0 := by
    rw [measureReal_ne_zero_iff hKc.measure_lt_top.ne]
    exact (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ (normInd_mem μ hKc hKo) hvs]
  have hpt : ∀ g, normInd μ K g * φ (ρ g v) =
      (K : Set G).indicator (fun _ => ((μ.real (K : Set G))⁻¹ : ℂ) * φ v) g := by
    intro g
    by_cases hg : g ∈ (K : Set G)
    · rw [normInd, Set.indicator_of_mem hg, Set.indicator_of_mem hg, mem_fixedVectors.1 hv g hg]
    · rw [normInd, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_indicator_const _ hKo.measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hK0, Complex.ofReal_one, one_mul]

variable (hρ : IsSmooth ρ)
include hρ

def heckeLin (f : locallyConstantCompactSupport G ℂ ℂ) : V →ₗ[ℂ] V where
  toFun v := heckeAct μ ρ f v
  map_add' v w := heckeAct_add_right f.2 (hρ v) (hρ w)
  map_smul' c v := heckeAct_smul_right f.2 c (hρ v)

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem heckeLin_apply (f : locallyConstantCompactSupport G ℂ ℂ) (v : V) :
    heckeLin μ hρ f v = heckeAct μ ρ f v := rfl

theorem comp_heckeLin_mem [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ℓ ∘ₗ heckeLin μ hρ f ∈ smoothVectors (Representation.dual ρ) := by
  obtain ⟨K, -, hK⟩ := exists_forall_mul_right f.2
  refine mem_smoothVectors_of_mem_fixedVectors (H := (K : Subgroup G)) K.isOpen
    (mem_fixedVectors_dual.2 fun k hk v => ?_)
  simp only [LinearMap.comp_apply, heckeLin_apply]
  rw [heckeAct_apply_act μ f.2 (hρ v) k]
  congr 2
  funext x
  exact hK x k⁻¹ (inv_mem hk)

def coeffL [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] smoothVectors (Representation.dual ρ) where
  toFun f := ⟨ℓ ∘ₗ heckeLin μ hρ f, comp_heckeLin_mem μ hρ ℓ f⟩
  map_add' f g := Subtype.ext <| LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, heckeLin_apply, Submodule.coe_add, LinearMap.add_apply]
    rw [heckeAct_add_left f.2 g.2 (hρ v), map_add]
  map_smul' c f := Subtype.ext <| LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, heckeLin_apply, SetLike.val_smul, LinearMap.smul_apply,
      RingHom.id_apply]
    rw [heckeAct_smul_left c f.2 (hρ v), map_smul]

theorem coeffL_apply [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (f : locallyConstantCompactSupport G ℂ ℂ) (v : V) :
    ((coeffL μ hρ ℓ f : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
      ℓ (heckeAct μ ρ f v) := rfl

theorem coeffL_rtransL [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (g : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (rtransL g f) = contragredient ρ g (coeffL μ hρ ℓ f) := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  rw [coeffL_apply, contragredient_apply_apply, coeffL_apply,
    heckeAct_apply_act μ f.2 (hρ v) g⁻¹]
  congr 2
  funext x
  simp

theorem coeffL_ltransL [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (a : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (ltransL a f) = coeffL μ hρ (ℓ ∘ₗ ρ a) f := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  rw [coeffL_apply, coeffL_apply, LinearMap.comp_apply, heckeAct_ltrans a f.2 (hρ v)]
  rfl

def convS (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) : locallyConstantCompactSupport G ℂ ℂ :=
  ⟨groupConv μ f₁ f₂, groupConv_mem μ f₁.2 f₂.2⟩

theorem coeffL_convS [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (convS μ f₁ f₂) =
      coeffL μ hρ ((coeffL μ hρ ℓ f₁ : smoothVectors (Representation.dual ρ)) :
        Module.Dual ℂ V) f₂ := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  rw [coeffL_apply, coeffL_apply, coeffL_apply, convS, heckeAct_groupConv f₁.2 f₂.2 (hρ v)]

theorem coeffL_normInd_apply [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {v : V} (hv : v ∈ fixedVectors ρ K) :
    ((coeffL μ hρ ℓ ⟨normInd μ K, normInd_mem μ hKc hKo⟩ : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) v = ℓ v := by
  rw [coeffL_apply]
  exact congrArg ℓ (heckeAct_normInd μ hKc hKo hv)

end Hecke

section Equivariant

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

def equivariantFunctionals (ρ : Representation ℂ G V) {H : Subgroup G} (χ : H → ℂ) :
    Submodule ℂ (Module.Dual ℂ V) where
  carrier := {ℓ | ∀ h : H, ∀ v, ℓ (ρ h v) = χ h * ℓ v}
  add_mem' {a b} ha hb h v := by
    simp only [Set.mem_ofPred_eq, LinearMap.add_apply] at ha hb ⊢
    rw [ha h v, hb h v, mul_add]
  zero_mem' h v := by simp
  smul_mem' c ℓ hℓ h v := by
    simp only [Set.mem_ofPred_eq, LinearMap.smul_apply, smul_eq_mul] at hℓ ⊢
    rw [hℓ h v]
    ring

theorem mem_equivariantFunctionals {ρ : Representation ℂ G V} {H : Subgroup G} {χ : H → ℂ}
    {ℓ : Module.Dual ℂ V} :
    ℓ ∈ equivariantFunctionals ρ χ ↔ ∀ h : H, ∀ v, ℓ (ρ h v) = χ h * ℓ v :=
  Iff.rfl

end Equivariant

section Sigma

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [μ.IsHaarMeasure] in

theorem compHomeoL_convS [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant] (σ : G ≃ₜ G)
    (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    compHomeoL σ (convS μ f₁ f₂) = convS μ (compHomeoL σ f₂) (compHomeoL σ f₁) := by
  refine Subtype.ext (funext fun x => ?_)
  change groupConv μ f₁ f₂ (σ x) = groupConv μ ((f₂ : G → ℂ) ∘ σ) ((f₁ : G → ℂ) ∘ σ) x
  simp only [groupConv, Function.comp_apply]
  have eR : ∫ y, (f₂ : G → ℂ) (σ y) * (f₁ : G → ℂ) (σ (y⁻¹ * x)) ∂μ =
      ∫ z, (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹) ∂μ := by
    have h := integral_map_equiv (μ := μ) σ.toMeasurableEquiv
      (fun z => (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹))
    simp only [Homeomorph.toMeasurableEquiv_coe, hσμ] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hσ, map_inv_of_antiHom σ hσ]
  have eL : ∫ y, (f₁ : G → ℂ) y * (f₂ : G → ℂ) (y⁻¹ * σ x) ∂μ =
      ∫ z, (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹) ∂μ := by
    rw [← integral_inv_eq_self (fun z => (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹)) μ,
      ← integral_mul_left_eq_self (fun y => (f₁ : G → ℂ) y * (f₂ : G → ℂ) (y⁻¹ * σ x)) (σ x)]
    congr 1
    funext y
    simp only [inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    ring
  rw [eL, eR]

end Sigma

section Distribution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)

theorem coeffL_smul_left (c : ℂ) (ℓ : Module.Dual ℂ V) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ (c • ℓ) f = c • coeffL μ hρ ℓ f :=
  Subtype.ext (LinearMap.ext fun v => by
    simp only [coeffL_apply, SetLike.val_smul, LinearMap.smul_apply])

theorem coeffL_zero_left (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ (0 : Module.Dual ℂ V) f = 0 :=
  Subtype.ext (LinearMap.ext fun v => by simp [coeffL_apply])

theorem coeffL_biTranslL {H : Subgroup G} {χ : H → ℂ} {ℓ : Module.Dual ℂ V}
    (hℓ : ℓ ∈ equivariantFunctionals ρ χ) (h₁ h₂ : H) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (biTranslL (h₁ : G) (h₂ : G) f) =
      χ h₁ • contragredient ρ h₂ (coeffL μ hρ ℓ f) := by
  have e : ℓ ∘ₗ ρ h₁ = χ h₁ • ℓ := LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    exact hℓ h₁ v
  rw [biTranslL_eq, coeffL_ltransL, e, coeffL_smul_left, coeffL_rtransL]

def coeffDist (ℓ : Module.Dual ℂ V) (ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) :
    Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) :=
  ℓt ∘ₗ coeffL μ hρ ℓ

theorem coeffDist_biTranslL {H : Subgroup G} {χ : H → ℂ} {ℓ : Module.Dual ℂ V}
    (hℓ : ℓ ∈ equivariantFunctionals ρ χ)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun h => (χ h)⁻¹))
    (f : locallyConstantCompactSupport G ℂ ℂ) (h₁ h₂ : H) :
    coeffDist μ hρ ℓ ℓt (biTranslL (h₁ : G) (h₂ : G) f) = χ h₁ * (χ h₂)⁻¹ * coeffDist μ hρ ℓ ℓt f := by
  simp only [coeffDist, LinearMap.comp_apply]
  rw [coeffL_biTranslL μ hρ hℓ, map_smul, hℓt h₂, smul_eq_mul, mul_assoc]

end Distribution

section Contragredient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

def annihilatorSubrep (W : Subrepresentation (contragredient ρ)) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) v = 0}
      add_mem' := fun {a b} ha hb => by
        show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) (a + b) = 0
        intro ξ hξ
        rw [map_add, ha ξ hξ, hb ξ hξ, add_zero]
      zero_mem' := by
        show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) 0 = 0
        intro ξ _
        exact map_zero _
      smul_mem' := fun c v hv => by
        show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) (c • v) = 0
        intro ξ hξ
        rw [map_smul, hv ξ hξ, smul_zero] }
  apply_mem_toSubmodule g v hv := by
    show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) (ρ g v) = 0
    intro ξ hξ
    have := hv _ (W.apply_mem_toSubmodule g⁻¹ hξ)
    rwa [contragredient_apply_apply, inv_inv] at this

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem mem_annihilatorSubrep {W : Subrepresentation (contragredient ρ)} {v : V} :
    v ∈ annihilatorSubrep W ↔ ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) v = 0 :=
  Iff.rfl

theorem exists_ne_zero_contragredient (h : IsAdmissible ρ) {v : V} (hv : v ≠ 0) :
    ∃ ξ : smoothVectors (Representation.dual ρ), (ξ : Module.Dual ℂ V) v ≠ 0 := by
  obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
  have hv' : (⟨v, hvK⟩ : fixedVectors ρ K) ≠ 0 := fun e => hv (congrArg Subtype.val e)
  obtain ⟨φ, hφ⟩ := not_forall.1
    (mt (Module.forall_dual_apply_eq_zero_iff ℂ (⟨v, hvK⟩ : fixedVectors ρ K)).1 hv')
  obtain ⟨ξ, hξ⟩ := (restrictFixed_bijective h.1 hKc hKo).2 φ
  refine ⟨(ξ : smoothVectors (Representation.dual ρ)), fun e => hφ ?_⟩
  rw [← hξ, restrictFixed_apply]
  exact e

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem isSmooth_subrep (hρ : IsSmooth ρ) (W : Subrepresentation ρ) :
    IsSmooth (V := W.toSubmodule) W.toRepresentation := fun w => by
  have : (stabilizerOf (V := W.toSubmodule) W.toRepresentation w : Set G) =
      stabilizerOf ρ (w : V) := by
    ext g
    simp only [SetLike.mem_coe, mem_stabilizerOf, Subtype.ext_iff]
    rfl
  rw [this]
  exact hρ _

theorem fixedProj_mem_subrep (hρ : IsSmooth ρ) (W : Subrepresentation ρ) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {x : V} (hx : x ∈ W) :
    ((fixedProj ρ hρ hKc hKo x : fixedVectors ρ K) : V) ∈ W := by
  let ι : Representation.IntertwiningMap (V := W.toSubmodule) W.toRepresentation ρ :=
    ⟨W.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  have key := fixedProj_map hKc hKo (isSmooth_subrep hρ W) hρ ι ⟨x, hx⟩
  have e : ((fixedProj ρ hρ hKc hKo x : fixedVectors ρ K) : V) =
      (((fixedProj (V := W.toSubmodule) W.toRepresentation (isSmooth_subrep hρ W) hKc hKo ⟨x, hx⟩ :
        fixedVectors _ K) : W.toSubmodule) : V) :=
    congrArg Subtype.val key
  rw [e]
  exact Subtype.property _

theorem forall_mem_apply_eq_zero {W : Subrepresentation (contragredient ρ)} {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {u : V} (hu : u ∈ fixedVectors ρ K)
    (hW : ∀ η ∈ W, η ∈ fixedVectors (contragredient ρ) K → (η : Module.Dual ℂ V) u = 0) :
    ∀ ζ ∈ W, (ζ : Module.Dual ℂ V) u = 0 := by
  intro ζ hζ
  have hsm := isSmooth_contragredient ρ
  let E : smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ :=
    LinearMap.applyₗ (R := ℂ) u ∘ₗ (smoothVectors (Representation.dual ρ)).subtype
  have hE : ∀ k ∈ K, ∀ η, E (contragredient ρ k η) = E η := fun k hk η => by
    change ((contragredient ρ k η : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) u = (η : Module.Dual ℂ V) u
    rw [contragredient_apply_apply, mem_fixedVectors.1 hu k⁻¹ (inv_mem hk)]
  have e1 : (ζ : Module.Dual ℂ V) u =
      (((fixedProj (contragredient ρ) hsm hKc hKo ζ : fixedVectors _ K) :
        smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) u := by
    have := coinvariantsKer_le_ker_of_invariant hE (sub_fixedProj_mem hsm hKc hKo ζ)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  rw [e1]
  exact hW _ (fixedProj_mem_subrep hsm W hKc hKo hζ) (fixedProj (contragredient ρ) hsm hKc hKo ζ).2

theorem eq_top_of_annihilator_eq_bot (h : IsAdmissible ρ) {W : Subrepresentation (contragredient ρ)}
    (hA : annihilatorSubrep W = ⊥) : W = ⊤ := by
  have hsm := isSmooth_contragredient ρ
  refine Subrepresentation.ext (eq_top_iff.2 fun ξ _ => ?_)
  obtain ⟨K, hKc, hKo, hξK⟩ := (isSmooth_iff_forall_exists _).1 hsm ξ
  have hfin : FiniteDimensional ℂ (fixedVectors ρ K) := h.2 K hKc hKo
  have hfinD : FiniteDimensional ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
    (Module.finite_dual_iff ℂ).2 hfin
  let S : Submodule ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
    (W.toSubmodule.comap (fixedVectors (contragredient ρ) K).subtype).map (restrictFixed ρ K)
  have hSfin : FiniteDimensional ℂ S := FiniteDimensional.finiteDimensional_submodule S
  have hS : S = ⊤ := by
    by_contra hS
    have hco : S.dualCoannihilator ≠ ⊥ := by
      intro e
      apply hS
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S), e,
        Submodule.dualAnnihilator_bot]
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hco
    have hann : (u : V) ∈ annihilatorSubrep W := by
      refine forall_mem_apply_eq_zero hKc hKo u.2 fun η hη hηK => ?_
      have hmem : restrictFixed ρ K ⟨η, hηK⟩ ∈ S := Submodule.mem_map_of_mem hη
      exact (Submodule.mem_dualCoannihilator _).1 hu _ hmem
    rw [hA] at hann
    exact hu0 (Subtype.ext ((Submodule.mem_bot ℂ).1 hann))
  have hmem : restrictFixed ρ K ⟨ξ, hξK⟩ ∈ S := by
    rw [hS]
    exact Submodule.mem_top
  obtain ⟨η, hη, hηξ⟩ := Submodule.mem_map.1 hmem
  have e := (restrictFixed_bijective h.1 hKc hKo).1 hηξ
  have : (η : smoothVectors (Representation.dual ρ)) = ξ := congrArg Subtype.val e
  rw [← this]
  exact hη

theorem isIrreducible_contragredient (h : IsAdmissible ρ) [ρ.IsIrreducible] :
    (contragredient ρ).IsIrreducible := by
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ : smoothVectors (Representation.dual ρ), ξ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
    obtain ⟨ξ, hξ⟩ := exists_ne_zero_contragredient h hv
    exact ⟨ξ, fun e => hξ (by rw [e]; rfl)⟩
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => hξ₀ ?_⟩⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have : ξ₀ ∈ (⊤ : Subrepresentation (contragredient ρ)) := Submodule.mem_top
    rw [← e] at this
    exact (Submodule.mem_bot ℂ).1 this
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  rcases eq_bot_or_eq_top (annihilatorSubrep W) with hA | hA
  · exact eq_top_of_annihilator_eq_bot h hA
  · exfalso
    apply hW
    refine Subrepresentation.ext (eq_bot_iff.2 fun ξ hξ => ?_)
    rw [Submodule.mem_bot]
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : v ∈ annihilatorSubrep W := by
      rw [hA]
      exact Submodule.mem_top
    exact hv ξ hξ

end Contragredient

section Surjective

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem coeffL_surjective (h : IsAdmissible ρ) [ρ.IsIrreducible] {ℓ : Module.Dual ℂ V}
    (hℓ : ℓ ≠ 0) : Function.Surjective (coeffL μ h.1 ℓ) := by
  have := isIrreducible_contragredient h
  let R : Subrepresentation (contragredient ρ) :=
    ⟨LinearMap.range (coeffL μ h.1 ℓ), fun g ξ hξ => by
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hξ
      rw [← coeffL_rtransL]
      exact LinearMap.mem_range_self _ _⟩
  rcases eq_bot_or_eq_top R with hR | hR
  · exfalso
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := not_forall.1 fun e => hℓ (LinearMap.ext e)
    obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
    have hmem : coeffL μ h.1 ℓ ⟨normInd μ K, normInd_mem μ hKc hKo⟩ ∈ R :=
      LinearMap.mem_range_self _ _
    rw [hR] at hmem
    have h0 := (Submodule.mem_bot ℂ).1 hmem
    apply hv
    rw [← coeffL_normInd_apply μ h.1 ℓ hKc hKo hvK, h0]
    rfl
  · intro ξ
    have : ξ ∈ R := by
      rw [hR]
      exact Submodule.mem_top
    exact LinearMap.mem_range.1 this

end Surjective

section Criterion

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [μ.IsMulRightInvariant] in

theorem apply_heckeAct_normInd (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {ξ : smoothVectors (Representation.dual ρ)}
    (hξ : ξ ∈ fixedVectors (contragredient ρ) K) (v : V) :
    (ξ : Module.Dual ℂ V) (heckeAct μ ρ (normInd μ K) v) = (ξ : Module.Dual ℂ V) v := by
  have hK0 : μ.real (K : Set G) ≠ 0 := by
    rw [measureReal_ne_zero_iff hKc.measure_lt_top.ne]
    exact (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  rw [dual_heckeAct μ (normInd_mem μ hKc hKo) (hρ v)]
  have hpt : ∀ g, normInd μ K g * (ξ : Module.Dual ℂ V) (ρ g v) =
      (K : Set G).indicator
        (fun _ => ((μ.real (K : Set G))⁻¹ : ℂ) * (ξ : Module.Dual ℂ V) v) g := by
    intro g
    by_cases hg : g ∈ (K : Set G)
    · rw [normInd, Set.indicator_of_mem hg, Set.indicator_of_mem hg,
        mem_fixedVectors_contragredient.1 hξ g hg v]
    · rw [normInd, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_indicator_const _ hKo.measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hK0, Complex.ofReal_one, one_mul]

def coeffKer (hρ : IsSmooth ρ) (ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) :
    Submodule ℂ (locallyConstantCompactSupport G ℂ ℂ) where
  carrier := {k | ∀ ξ : smoothVectors (Representation.dual ρ),
    ℓt (coeffL μ hρ (ξ : Module.Dual ℂ V) k) = 0}
  add_mem' {a b} ha hb ξ := by
    rw [map_add, map_add, ha ξ, hb ξ, add_zero]
  zero_mem' ξ := by rw [map_zero, map_zero]
  smul_mem' c k hk ξ := by
    rw [map_smul, map_smul, hk ξ, smul_zero]

theorem mem_coeffKer (hρ : IsSmooth ρ) {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    {k : locallyConstantCompactSupport G ℂ ℂ} :
    k ∈ coeffKer μ hρ ℓt ↔ ∀ ξ : smoothVectors (Representation.dual ρ),
      ℓt (coeffL μ hρ (ξ : Module.Dual ℂ V) k) = 0 :=
  Iff.rfl

theorem ltransL_mem_coeffKer (hρ : IsSmooth ρ)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))} (a : G)
    {k : locallyConstantCompactSupport G ℂ ℂ} (hk : k ∈ coeffKer μ hρ ℓt) :
    ltransL a k ∈ coeffKer μ hρ ℓt := by
  intro ξ
  rw [coeffL_ltransL]
  have e : (ξ : Module.Dual ℂ V) ∘ₗ ρ a =
      ((contragredient ρ a⁻¹ ξ : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) :=
    LinearMap.ext fun v => by rw [contragredient_apply_apply, inv_inv]; rfl
  rw [e]
  exact hk _

theorem mem_ker_coeffL (hρ : IsSmooth ρ) {ℓ : Module.Dual ℂ V}
    {f : locallyConstantCompactSupport G ℂ ℂ} :
    f ∈ LinearMap.ker (coeffL μ hρ ℓ) ↔ coeffL μ hρ ℓ f = 0 :=
  LinearMap.mem_ker

theorem ker_coeffL_eq (h : IsAdmissible ρ) [ρ.IsIrreducible] {ℓ : Module.Dual ℂ V}
    {L : Submodule ℂ (locallyConstantCompactSupport G ℂ ℂ)}
    (hker : LinearMap.ker (coeffL μ h.1 ℓ) ≤ L) (hL : ∀ g, ∀ f ∈ L, rtransL g f ∈ L)
    (hLtop : L ≠ ⊤) : LinearMap.ker (coeffL μ h.1 ℓ) = L := by
  have := isIrreducible_contragredient h
  let M : Subrepresentation (contragredient ρ) :=
    ⟨L.map (coeffL μ h.1 ℓ), fun g ξ hξ => by
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hξ
      rw [← coeffL_rtransL]
      exact Submodule.mem_map_of_mem (hL g f hf)⟩
  refine le_antisymm hker ?_
  rcases eq_bot_or_eq_top M with hM | hM
  · intro f hf
    have : coeffL μ h.1 ℓ f ∈ M := Submodule.mem_map_of_mem hf
    rw [hM] at this
    exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this)
  · exfalso
    apply hLtop
    refine eq_top_iff.2 fun f _ => ?_
    have : coeffL μ h.1 ℓ f ∈ M := by
      rw [hM]
      exact Submodule.mem_top
    obtain ⟨f', hf', e⟩ := Submodule.mem_map.1 this
    have hd : f - f' ∈ L := hker (LinearMap.mem_ker.2 (by rw [map_sub, e, sub_self]))
    have := L.add_mem hd hf'
    rwa [sub_add_cancel] at this

variable [μ.IsInvInvariant] {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}

theorem ker_coeffL_eq_comap (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible]
    {ℓ : Module.Dual ℂ V} (hℓ : ℓ ∈ equivariantFunctionals ρ χ) (hℓ0 : ℓ ≠ 0)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) (hℓt0 : ℓt ≠ 0) :
    LinearMap.ker (coeffL μ h.1 ℓ) = (coeffKer μ h.1 ℓt).comap (compHomeoL σ) := by
  have hB := hGK (coeffDist μ h.1 ℓ ℓt) (coeffDist_biTranslL μ h.1 hℓ hℓt)
  refine ker_coeffL_eq μ h ?_ ?_ ?_
  ·
    intro f₁ hf₁
    rw [LinearMap.mem_ker] at hf₁
    show compHomeoL σ f₁ ∈ coeffKer μ h.1 ℓt
    intro ξ
    obtain ⟨k, rfl⟩ := coeffL_surjective μ h hℓ0 ξ
    set f₂ := compHomeoL σ.symm k
    have hk : k = compHomeoL σ f₂ := (compHomeoL_symm_apply σ k).symm
    rw [← coeffL_convS, hk, ← compHomeoL_convS μ σ hσ hσμ]
    have := hB (convS μ f₁ f₂)
    simp only [coeffDist, LinearMap.comp_apply] at this
    rw [this, coeffL_convS, hf₁]
    simp [coeffL_zero_left]
  ·
    intro g f hf
    show compHomeoL σ (rtransL g f) ∈ coeffKer μ h.1 ℓt
    have e : compHomeoL σ (rtransL g f) = ltransL (σ.symm g)⁻¹ (compHomeoL σ f) :=
      Subtype.ext (funext fun x => by
        simp only [coe_compHomeoL, coe_rtransL, coe_ltransL, Function.comp_apply, inv_inv, hσ,
          Homeomorph.apply_symm_apply])
    rw [e]
    exact ltransL_mem_coeffKer μ h.1 _ hf
  ·
    intro htop
    obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, ℓt ξ ≠ 0 := not_forall.1 fun e => hℓt0 (LinearMap.ext e)
    obtain ⟨K, hKc, hKo, hξK⟩ := (isSmooth_iff_forall_exists _).1 (isSmooth_contragredient ρ) ξ₀
    let k₀ : locallyConstantCompactSupport G ℂ ℂ := ⟨normInd μ K, normInd_mem μ hKc hKo⟩
    have hmem : compHomeoL σ.symm k₀ ∈ (coeffKer μ h.1 ℓt).comap (compHomeoL σ) := by
      rw [htop]
      exact Submodule.mem_top
    have h0 := (Submodule.mem_comap.1 hmem) ξ₀
    rw [compHomeoL_symm_apply] at h0
    have e : coeffL μ h.1 (ξ₀ : Module.Dual ℂ V) k₀ = ξ₀ :=
      Subtype.ext (LinearMap.ext fun v => apply_heckeAct_normInd μ h.1 hKc hKo hξK v)
    rw [e] at h0
    exact hξ₀ h0

theorem exists_smul_eq (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) [TopologicalSpace.SeparableSpace G]
    (h : IsAdmissible ρ) [ρ.IsIrreducible]
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) (hℓt0 : ℓt ≠ 0)
    {ℓ₁ ℓ₂ : Module.Dual ℂ V} (h₁ : ℓ₁ ∈ equivariantFunctionals ρ χ) (h₁0 : ℓ₁ ≠ 0)
    (h₂ : ℓ₂ ∈ equivariantFunctionals ρ χ) : ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by
  by_cases h₂0 : ℓ₂ = 0
  · exact ⟨0, by rw [h₂0, zero_smul]⟩
  have := isIrreducible_contragredient h
  set A₁ := coeffL μ h.1 ℓ₁
  set A₂ := coeffL μ h.1 ℓ₂
  have hs₁ : Function.Surjective A₁ := coeffL_surjective μ h h₁0
  have hker : LinearMap.ker A₁ ≤ LinearMap.ker A₂ := by
    rw [ker_coeffL_eq_comap μ hσ hσμ hGK h h₁ h₁0 hℓt hℓt0,
      ker_coeffL_eq_comap μ hσ hσμ hGK h h₂ h₂0 hℓt hℓt0]
  let e := A₁.quotKerEquivOfSurjective hs₁
  let T : smoothVectors (Representation.dual ρ) →ₗ[ℂ] smoothVectors (Representation.dual ρ) :=
    (LinearMap.ker A₁).liftQ A₂ hker ∘ₗ e.symm.toLinearMap
  have hT : ∀ f, T (A₁ f) = A₂ f := fun f => by
    have : e.symm (A₁ f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hTi : ∀ (g : G) (ξ : smoothVectors (Representation.dual ρ)),
      T (contragredient ρ g ξ) = contragredient ρ g (T ξ) := fun g ξ => by
    obtain ⟨f, rfl⟩ := hs₁ ξ
    rw [← coeffL_rtransL, hT, hT, coeffL_rtransL]
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth
    (isSmooth_contragredient ρ)).2 (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ T hTi)
  have hTc : ∀ ξ, T ξ = c • ξ := fun ξ =>
    (congrArg (fun F : Representation.IntertwiningMap (contragredient ρ) (contragredient ρ) =>
      F ξ) hc).symm
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
  let k : locallyConstantCompactSupport G ℂ ℂ := ⟨normInd μ K, normInd_mem μ hKc hKo⟩
  have e₂ := coeffL_normInd_apply μ h.1 ℓ₂ hKc hKo hvK
  have e₁ := coeffL_normInd_apply μ h.1 ℓ₁ hKc hKo hvK
  rw [LinearMap.smul_apply, ← e₁, ← e₂]
  change ((A₂ k : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
    c • ((A₁ k : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v
  rw [← hT, hTc]
  rfl

theorem rank_equivariantFunctionals_le_one (hσ : ∀ x y, σ (x * y) = σ y * σ x)
    (hσμ : μ.map σ = μ) (hGK : BiEquivariantSigmaInvariant H χ σ)
    [TopologicalSpace.SeparableSpace G] (h : IsAdmissible ρ) [ρ.IsIrreducible]
    (hne : equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals ρ χ) ≤ 1 := by
  obtain ⟨ℓt, hℓt, hℓt0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [rank_le_one_iff]
  by_cases hz : ∀ ℓ ∈ equivariantFunctionals ρ χ, ℓ = 0
  · refine ⟨0, fun ℓ => ⟨0, ?_⟩⟩
    rw [zero_smul]
    exact Subtype.ext (hz ℓ ℓ.2).symm
  · push Not at hz
    obtain ⟨ℓ₁, h₁, h₁0⟩ := hz
    refine ⟨⟨ℓ₁, h₁⟩, fun ℓ => ?_⟩
    obtain ⟨c, hc⟩ := exists_smul_eq μ hσ hσμ hGK h hℓt hℓt0 h₁ h₁0 ℓ.2
    exact ⟨c, Subtype.ext hc.symm⟩

end Criterion

section Unimodular

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

theorem isMulRightInvariant_of_isInvInvariant (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsInvInvariant] : μ.IsMulRightInvariant :=
  by
  have : μ.inv.IsMulRightInvariant := inferInstance
  rwa [Measure.inv_eq_self] at this

end Unimodular

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace.SeparableSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace.SeparableSpace G] [MeasurableSpace G] [BorelSpace G] in

theorem exists_ne_zero_doubleContragredient [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (h : IsAdmissible ρ)
    (hne : equivariantFunctionals ρ χ ≠ ⊥) :
    equivariantFunctionals (contragredient (contragredient ρ)) (fun g => ((χ g)⁻¹)⁻¹) ≠ ⊥ := by
  obtain ⟨ℓ, hℓ, hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let Φ := LinearEquiv.ofBijective (toDoubleContragredient h.1).toLinearMap
    (toDoubleContragredient_bijective h)
  have hΦ : ∀ x, Φ x = toDoubleContragredient h.1 x := fun _ => rfl
  let ℓ' : Module.Dual ℂ (smoothVectors (Representation.dual (contragredient ρ))) :=
    ℓ ∘ₗ Φ.symm.toLinearMap
  have hℓ'Φ : ∀ x, ℓ' (Φ x) = ℓ x := fun x => by
    simp only [ℓ', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  intro hbot
  have hmem : ℓ' ∈ equivariantFunctionals (contragredient (contragredient ρ))
      (fun g => ((χ g)⁻¹)⁻¹) := by
    intro g y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    show ℓ' (contragredient (contragredient ρ) g (Φ x)) = ((χ g)⁻¹)⁻¹ * ℓ' (Φ x)
    have e1 : contragredient (contragredient ρ) g (Φ x) = Φ (ρ g x) := by
      rw [hΦ, hΦ, (toDoubleContragredient h.1).isIntertwining]
    rw [inv_inv, e1, hℓ'Φ, hℓ'Φ]
    exact hℓ g x
  rw [hbot] at hmem
  have h0 : ℓ' = 0 := (Submodule.mem_bot ℂ).1 hmem
  apply hℓ0
  refine LinearMap.ext fun x => ?_
  rw [← hℓ'Φ, h0]
  rfl

theorem rank_mul_rank_le_one (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals ρ χ) *
      Module.rank ℂ (equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) ≤ 1 := by
  have := isMulRightInvariant_of_isInvInvariant μ
  by_cases h₂ : equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹) = ⊥
  · rw [h₂, rank_bot, mul_zero]
    exact zero_le_one
  by_cases h₁ : equivariantFunctionals ρ χ = ⊥
  · rw [h₁, rank_bot, zero_mul]
    exact zero_le_one
  have := isIrreducible_contragredient h
  have r₁ := rank_equivariantFunctionals_le_one μ hσ hσμ hGK h h₂
  have r₂ := rank_equivariantFunctionals_le_one μ hσ hσμ (hGK.inv hσ)
    (isAdmissible_contragredient h) (exists_ne_zero_doubleContragredient h h₁)
  calc Module.rank ℂ (equivariantFunctionals ρ χ) *
        Module.rank ℂ (equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹))
      ≤ 1 * 1 := mul_le_mul' r₁ r₂
    _ = 1 := one_mul 1

theorem rank_le_one_of_ne_bot (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible]
    (hne : equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals ρ χ) ≤ 1 := by
  have := isMulRightInvariant_of_isInvInvariant μ
  exact rank_equivariantFunctionals_le_one μ hσ hσμ hGK h hne

end Main

end Whittaker

end GroundTheory.Automorphic
