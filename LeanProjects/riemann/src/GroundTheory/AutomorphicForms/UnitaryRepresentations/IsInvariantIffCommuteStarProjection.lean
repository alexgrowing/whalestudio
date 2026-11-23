import Mathlib

namespace GroundTheory.Automorphic

open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology

structure UnitaryRep (G : Type*) [Group G] [TopologicalSpace G] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where

  toHom : G →* unitary (H →L[ℂ] H)

  continuous_orbit' : ∀ v : H, Continuous fun g => (toHom g : H →L[ℂ] H) v

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

@[coe] noncomputable def op (π : UnitaryRep G H) (g : G) : H →L[ℂ] H := (π.toHom g : H →L[ℂ] H)

noncomputable instance : CoeFun (UnitaryRep G H) (fun _ => G → H →L[ℂ] H) := ⟨op⟩

variable (π : UnitaryRep G H)

lemma coe_apply (g : G) : π g = (π.toHom g : H →L[ℂ] H) := rfl

lemma continuous_orbit (v : H) : Continuous fun g => π g v := π.continuous_orbit' v

@[simp] lemma map_one : π 1 = 1 := by
  show ((π.toHom 1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1
  simp

@[simp] lemma map_mul (g h : G) : π (g * h) = π g * π h := by
  show ((π.toHom (g * h) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
    (π.toHom g : H →L[ℂ] H) * (π.toHom h : H →L[ℂ] H)
  simp

lemma map_mul_apply (g h : G) (v : H) : π (g * h) v = π g (π h v) := by
  rw [map_mul]; rfl

@[simp] lemma map_one_apply (v : H) : π 1 v = v := by rw [map_one]; rfl

@[simp] lemma norm_map (g : G) (v : H) : ‖π g v‖ = ‖v‖ := Unitary.norm_map _ v

@[simp] lemma inner_map_map (g : G) (v w : H) : ⟪π g v, π g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  Unitary.inner_map_map _ v w

lemma mem_unitary (g : G) : π g ∈ unitary (H →L[ℂ] H) := (π.toHom g).2

@[simp] lemma star_map (g : G) : star (π g) = π g⁻¹ := by
  show star ((π.toHom g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
    ((π.toHom g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  rw [MonoidHom.map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]

@[simp] lemma adjoint_map (g : G) : adjoint (π g) = π g⁻¹ := by
  rw [← star_eq_adjoint, star_map]

@[simp] lemma map_inv_apply_map (g : G) (v : H) : π g⁻¹ (π g v) = v := by
  rw [← map_mul_apply, inv_mul_cancel, map_one_apply]

@[simp] lemma map_apply_map_inv (g : G) (v : H) : π g (π g⁻¹ v) = v := by
  rw [← map_mul_apply, mul_inv_cancel, map_one_apply]

lemma inner_map_left (g : G) (v w : H) : ⟪π g v, w⟫_ℂ = ⟪v, π g⁻¹ w⟫_ℂ := by
  rw [← adjoint_map, adjoint_inner_right]

lemma inner_map_right (g : G) (v w : H) : ⟪v, π g w⟫_ℂ = ⟪π g⁻¹ v, w⟫_ℂ := by
  rw [← adjoint_map, adjoint_inner_left]

lemma norm_map_le (g : G) : ‖π g‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v => by simp

lemma map_injective (g : G) : Function.Injective (π g) := fun v w h => by
  have := congrArg (π g⁻¹) h
  rwa [map_inv_apply_map, map_inv_apply_map] at this

noncomputable def ofLinearIsometryEquiv (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (hρ : ∀ v, Continuous fun g => ρ g v) : UnitaryRep G H where
  toHom := (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := H)).symm.toMonoidHom.comp ρ
  continuous_orbit' v := by simpa using hρ v

@[simp] lemma ofLinearIsometryEquiv_apply (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (hρ : ∀ v, Continuous fun g => ρ g v) (g : G) (v : H) :
    ofLinearIsometryEquiv ρ hρ g v = ρ g v := rfl

theorem continuous_of_weak (ρ : G →* unitary (H →L[ℂ] H))
    (hρ : ∀ v w : H, Continuous fun g => ⟪(ρ g : H →L[ℂ] H) v, w⟫_ℂ) (v : H) :
    Continuous fun g => (ρ g : H →L[ℂ] H) v := by
  rw [continuous_iff_continuousAt]
  intro h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set w := (ρ h : H →L[ℂ] H) v
  have hsq : ∀ g, ‖(ρ g : H →L[ℂ] H) v - w‖ =
      Real.sqrt (2 * ‖v‖ ^ 2 - 2 * RCLike.re ⟪(ρ g : H →L[ℂ] H) v, w⟫_ℂ) := by
    intro g
    rw [← Real.sqrt_sq (norm_nonneg _), @norm_sub_sq ℂ, Unitary.norm_map, Unitary.norm_map]
    congr 1
    ring
  have hc : Continuous fun g =>
      Real.sqrt (2 * ‖v‖ ^ 2 - 2 * RCLike.re ⟪(ρ g : H →L[ℂ] H) v, w⟫_ℂ) :=
    (continuous_const.sub (continuous_const.mul (RCLike.continuous_re.comp (hρ v w)))).sqrt
  have h0 : Real.sqrt (2 * ‖v‖ ^ 2 - 2 * RCLike.re ⟪(ρ h : H →L[ℂ] H) v, w⟫_ℂ) = 0 := by
    rw [← hsq, sub_self, norm_zero]
  simp_rw [hsq]
  rw [← h0]
  exact hc.continuousAt

theorem continuous_of_continuousAt_one [IsTopologicalGroup G] (ρ : G →* unitary (H →L[ℂ] H))
    (hρ : ∀ v : H, ContinuousAt (fun g => (ρ g : H →L[ℂ] H) v) 1) (v : H) :
    Continuous fun g => (ρ g : H →L[ℂ] H) v := by
  rw [continuous_iff_continuousAt]
  intro h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ g, ‖(ρ g : H →L[ℂ] H) v - (ρ h : H →L[ℂ] H) v‖ =
      ‖(ρ (h⁻¹ * g) : H →L[ℂ] H) v - v‖ := by
    intro g
    have e : ρ g = ρ h * ρ (h⁻¹ * g) := by rw [← MonoidHom.map_mul, mul_inv_cancel_left]
    have : (ρ g : H →L[ℂ] H) v - (ρ h : H →L[ℂ] H) v =
        (ρ h : H →L[ℂ] H) ((ρ (h⁻¹ * g) : H →L[ℂ] H) v - v) := by
      rw [map_sub, e]
      rfl
    rw [this, Unitary.norm_map]
  simp_rw [key]
  have ht : Tendsto (fun g => h⁻¹ * g) (𝓝 h) (𝓝 1) := by
    have := (continuous_const_mul h⁻¹).tendsto h
    rwa [inv_mul_cancel] at this
  have h1 := Filter.Tendsto.comp (hρ v) ht
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1
  simpa [Function.comp_def] using h1

theorem continuous_action : Continuous fun p : G × H => π p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨h, w⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ p : G × H, ‖π p.1 p.2 - π h w‖ ≤ ‖p.2 - w‖ + ‖π p.1 w - π h w‖ := by
    intro p
    calc ‖π p.1 p.2 - π h w‖ = ‖π p.1 (p.2 - w) + (π p.1 w - π h w)‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖π p.1 (p.2 - w)‖ + ‖π p.1 w - π h w‖ := norm_add_le _ _
      _ = ‖p.2 - w‖ + ‖π p.1 w - π h w‖ := by rw [norm_map]
  refine squeeze_zero (fun _ => norm_nonneg _) hle ?_
  rw [← add_zero (0 : ℝ)]
  refine Tendsto.add ?_ ?_
  · have : Tendsto (fun p : G × H => p.2) (𝓝 (h, w)) (𝓝 w) := continuous_snd.tendsto _
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  · have : Tendsto (fun p : G × H => π p.1 w) (𝓝 (h, w)) (𝓝 (π h w)) :=
      ((π.continuous_orbit w).comp continuous_fst).tendsto _
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this

lemma continuous_inner_orbit (v w : H) : Continuous fun g => ⟪π g v, w⟫_ℂ :=
  (π.continuous_orbit v).inner continuous_const

def IsInvariant (V : Submodule ℂ H) : Prop := ∀ (g : G) (v : H), v ∈ V → π g v ∈ V

variable {π}

lemma isInvariant_bot : π.IsInvariant ⊥ := fun g v hv => by
  rw [Submodule.mem_bot] at hv ⊢; simp [hv]

lemma isInvariant_top : π.IsInvariant ⊤ := fun _ _ _ => Submodule.mem_top

theorem IsInvariant.orthogonal {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant Vᗮ := by
  intro g v hv w hw
  rw [inner_map_right]
  exact hv _ (hV _ _ hw)

theorem IsInvariant.topologicalClosure {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant V.topologicalClosure := by
  intro g v hv
  have hsub : Set.MapsTo (π g) (V : Set H) (V.topologicalClosure : Set H) :=
    fun x hx => V.le_topologicalClosure (hV g x hx)
  have hv' : v ∈ closure (V : Set H) := by
    rwa [← Submodule.topologicalClosure_coe]
  have := hsub.closure (π g).continuous hv'
  rwa [V.isClosed_topologicalClosure.closure_eq] at this

theorem isInvariant_iff_commute_starProjection (V : Submodule ℂ H) [V.HasOrthogonalProjection] :
    π.IsInvariant V ↔ ∀ g, Commute (π g) V.starProjection := by
  constructor
  · intro hV g
    ext v
    have hdec : v = V.starProjection v + (v - V.starProjection v) := by abel
    have hq : v - V.starProjection v ∈ Vᗮ := V.sub_starProjection_mem_orthogonal v
    have hp : V.starProjection v ∈ V := V.starProjection_apply_mem v
    have e1 : V.starProjection (π g v) = π g (V.starProjection v) := by
      conv_lhs => rw [hdec, map_add, map_add,
        Submodule.starProjection_eq_self_iff.mpr (hV g _ hp),
        (V.starProjection_apply_eq_zero_iff).mpr (hV.orthogonal g _ hq), add_zero]
    exact e1.symm
  · intro h g v hv
    rw [← Submodule.starProjection_eq_self_iff] at hv ⊢
    have : π g (V.starProjection v) = V.starProjection (π g v) :=
      congrArg (fun T : H →L[ℂ] H => T v) (h g)
    rw [← this, hv]

variable (π) in

def intertwiners (σ : UnitaryRep G K) : Submodule ℂ (H →L[ℂ] K) where
  carrier := {T | ∀ (g : G) (v : H), T (π g v) = σ g (T v)}
  add_mem' {S T} hS hT g v := by simp [hS g v, hT g v]
  zero_mem' g v := by simp
  smul_mem' c T hT g v := by simp [hT g v]

variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}

lemma mem_intertwiners {T : H →L[ℂ] K} :
    T ∈ π.intertwiners σ ↔ ∀ (g : G) (v : H), T (π g v) = σ g (T v) := Iff.rfl

lemma mem_intertwiners_iff_comp {T : H →L[ℂ] K} :
    T ∈ π.intertwiners σ ↔ ∀ g : G, T ∘L π g = σ g ∘L T := by
  simp only [mem_intertwiners, ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply]

lemma one_mem_intertwiners : (1 : H →L[ℂ] H) ∈ π.intertwiners π := fun _ _ => rfl

lemma comp_mem_intertwiners {S : K →L[ℂ] L} {T : H →L[ℂ] K} (hS : S ∈ σ.intertwiners τ)
    (hT : T ∈ π.intertwiners σ) : S ∘L T ∈ π.intertwiners τ := fun g v => by
  simp [hT g v, hS g (T v)]

lemma mul_mem_intertwiners {S T : H →L[ℂ] H} (hS : S ∈ π.intertwiners π)
    (hT : T ∈ π.intertwiners π) : S * T ∈ π.intertwiners π := comp_mem_intertwiners hS hT

theorem adjoint_mem_intertwiners {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    adjoint T ∈ σ.intertwiners π := by
  intro g w
  apply ext_inner_left ℂ
  intro v
  rw [adjoint_inner_right, inner_map_right π, adjoint_inner_right, hT, inner_map_left σ, inv_inv]

lemma star_mem_intertwiners {T : H →L[ℂ] H} (hT : T ∈ π.intertwiners π) :
    star T ∈ π.intertwiners π := by
  rw [star_eq_adjoint]; exact adjoint_mem_intertwiners hT

lemma commute_of_mem_intertwiners {T : H →L[ℂ] H} (hT : T ∈ π.intertwiners π) (g : G) :
    Commute T (π g) := by
  ext v; exact hT g v

lemma mem_intertwiners_self_iff {T : H →L[ℂ] H} :
    T ∈ π.intertwiners π ↔ ∀ g, Commute T (π g) := by
  refine ⟨commute_of_mem_intertwiners, fun h g v => ?_⟩
  exact congrArg (fun S : H →L[ℂ] H => S v) (h g)

lemma isInvariant_range {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    σ.IsInvariant (LinearMap.range (T : H →ₗ[ℂ] K)) := by
  rintro g _ ⟨v, rfl⟩
  exact ⟨π g v, hT g v⟩

lemma isInvariant_ker {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    π.IsInvariant (LinearMap.ker (T : H →ₗ[ℂ] K)) := by
  intro g v hv
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
  rw [hT, hv, map_zero]

variable (π σ) in

structure Equiv where

  toLinearIsometryEquiv : H ≃ₗᵢ[ℂ] K

  map_apply' : ∀ (g : G) (v : H), toLinearIsometryEquiv (π g v) = σ g (toLinearIsometryEquiv v)

variable (π σ) in

def IsEquivalent : Prop := Nonempty (π.Equiv σ)

namespace Equiv

def refl (π : UnitaryRep G H) : π.Equiv π := ⟨LinearIsometryEquiv.refl ℂ H, fun _ _ => rfl⟩

def symm (e : π.Equiv σ) : σ.Equiv π where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.symm
  map_apply' g w := by
    apply e.toLinearIsometryEquiv.injective
    rw [LinearIsometryEquiv.apply_symm_apply, e.map_apply', LinearIsometryEquiv.apply_symm_apply]

def trans (e : π.Equiv σ) (f : σ.Equiv τ) : π.Equiv τ where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.trans f.toLinearIsometryEquiv
  map_apply' g v := by simp [e.map_apply', f.map_apply']

lemma mem_intertwiners (e : π.Equiv σ) :
    (e.toLinearIsometryEquiv : H →L[ℂ] K) ∈ π.intertwiners σ := e.map_apply'

end Equiv

lemma IsEquivalent.refl (π : UnitaryRep G H) : π.IsEquivalent π := ⟨Equiv.refl π⟩

lemma IsEquivalent.symm (h : π.IsEquivalent σ) : σ.IsEquivalent π := ⟨h.some.symm⟩

lemma IsEquivalent.trans (h : π.IsEquivalent σ) (h' : σ.IsEquivalent τ) : π.IsEquivalent τ :=
  ⟨h.some.trans h'.some⟩

variable (π) in

def IsIrreducible : Prop :=
  Nontrivial H ∧ ∀ V : Submodule ℂ H, IsClosed (V : Set H) → π.IsInvariant V → V = ⊥ ∨ V = ⊤

theorem IsIrreducible.of_equiv (hπ : π.IsIrreducible) (e : π.Equiv σ) : σ.IsIrreducible := by
  obtain ⟨hnt, hπ⟩ := hπ
  refine ⟨e.toLinearIsometryEquiv.toEquiv.nontrivial_congr.mp hnt, fun W hW hWinv => ?_⟩
  let E : H →L[ℂ] K := e.toLinearIsometryEquiv
  have hcl : IsClosed ((W.comap (E : H →ₗ[ℂ] K) : Submodule ℂ H) : Set H) :=
    hW.preimage E.continuous
  have hinv : π.IsInvariant (W.comap (E : H →ₗ[ℂ] K)) := by
    intro g v hv
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe] at hv ⊢
    rw [show E (π g v) = σ g (E v) from e.map_apply' g v]
    exact hWinv g _ hv
  have hsurj : Function.Surjective E := e.toLinearIsometryEquiv.surjective
  rcases hπ _ hcl hinv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := hsurj w
    have : v ∈ W.comap (E : H →ₗ[ℂ] K) := hw
    rw [h, Submodule.mem_bot] at this
    simp [this]
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hsurj w
    have : v ∈ W.comap (E : H →ₗ[ℂ] K) := by rw [h]; exact Submodule.mem_top
    exact this

theorem IsEquivalent.isIrreducible_iff (h : π.IsEquivalent σ) :
    π.IsIrreducible ↔ σ.IsIrreducible :=
  ⟨fun hπ => hπ.of_equiv h.some, fun hσ => hσ.of_equiv h.some.symm⟩

section restrict

variable (π) (V : Submodule ℂ H) [CompleteSpace V] (hV : π.IsInvariant V)

noncomputable def restrictAux (g : G) : V ≃ₗᵢ[ℂ] V where
  toFun v := ⟨π g v, hV g v v.2⟩
  invFun v := ⟨π g⁻¹ v, hV _ v v.2⟩
  map_add' v w := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)
  left_inv v := Subtype.ext (by simp)
  right_inv v := Subtype.ext (by simp)
  norm_map' v := by simp [Submodule.coe_norm]

noncomputable def restrict : UnitaryRep G V :=
  ofLinearIsometryEquiv
    { toFun := restrictAux π V hV
      map_one' := by ext v; simp [restrictAux]
      map_mul' := fun g h =>
        LinearIsometryEquiv.ext fun v => Subtype.ext (map_mul_apply π g h v) }
    (fun v => (π.continuous_orbit v).subtype_mk _)

@[simp] lemma coe_restrict_apply (g : G) (v : V) :
    ((π.restrict V hV g v : V) : H) = π g v := rfl

lemma subtypeL_mem_intertwiners : V.subtypeL ∈ (π.restrict V hV).intertwiners π :=
  fun _ _ => rfl

end restrict

end UnitaryRep

end GroundTheory.Automorphic
