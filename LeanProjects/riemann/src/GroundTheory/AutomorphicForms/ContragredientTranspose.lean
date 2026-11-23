import Mathlib
import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan
import GroundTheory.AutomorphicForms.ContragredientTranspose.Character
import GroundTheory.AutomorphicForms.WhittakerLocal
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.MapThetaTInvariant

namespace GroundTheory.Automorphic.ContragredientTranspose

open MeasureTheory Measure GroundTheory.Automorphic.Whittaker

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def subrepCompOrderIso {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (α : G ≃* G) :
    Subrepresentation (ρ.comp α.toMonoidHom) ≃o Subrepresentation ρ where
  toFun W := ⟨W.toSubmodule, fun g v hv => by
    have := W.apply_mem_toSubmodule (α.symm g) hv
    simpa using this⟩
  invFun W := ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (α g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (α : G ≃* G) :
    Representation.IsIrreducible (ρ.comp α.toMonoidHom) :=
  (OrderIso.isSimpleOrder_iff (subrepCompOrderIso ρ α)).2 inferInstance

theorem map_thetaT_eq [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ.map (thetaT : GL (Fin n) F ≃* GL (Fin n) F) = μ :=
  _root_.GroundTheory.Variant₂.N1.map_thetaT_eq_self μ

theorem nonempty_equiv_contragredient {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Nonempty ((contragredient π).Equiv
      (π.comp (thetaT : GL (Fin n) F ≃* GL (Fin n) F).toMonoidHom)) := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  set μ : Measure (GL (Fin n) F) := haar
  have : μ.IsMulRightInvariant := Measures.isMulRightInvariant_GL F n μ
  have : μ.IsInvInvariant := ⟨Measures.inv_eq_self_GL F n μ⟩
  have hc : Continuous (thetaT : GL (Fin n) F ≃* GL (Fin n) F) := continuous_thetaT
  have hc' : Continuous (thetaT : GL (Fin n) F ≃* GL (Fin n) F).symm := continuous_thetaT
  have := isIrreducible_contragredient hπ
  have := isIrreducible_comp π (thetaT : GL (Fin n) F ≃* GL (Fin n) F)
  refine nonempty_equiv_of_distChar_eq (μ := μ) (isAdmissible_contragredient hπ)
    (isAdmissible_comp _ hc hc' hπ) ?_
  refine LinearMap.ext fun f => ?_
  rw [distChar_contragredient, distChar_comp μ _ hc hc' (map_thetaT_eq μ) hπ]
  have e : compHomeoL (mulEquivHomeo (thetaT : GL (Fin n) F ≃* GL (Fin n) F) hc hc').symm f =
      compHomeoL transposeHomeo (compHomeoL (Homeomorph.inv (GL (Fin n) F)) f) :=
    Subtype.ext (funext fun x => rfl)
  rw [e, distribution_transpose_invariant (distChar μ π hπ) (fun g f => distChar_biTranslL μ hπ g f)]

noncomputable def longestWeyl : GL (Fin n) F := permGL F (Fin.revPerm (n := n))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem longestWeyl_mul_self : (longestWeyl : GL (Fin n) F) * longestWeyl = 1 := by
  rw [longestWeyl, ← map_mul]
  have : (Fin.revPerm (n := n)) * Fin.revPerm = 1 := Equiv.ext fun i => by simp
  rw [this, map_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem thetaT_eq_longestWeyl (g : GL (Fin n) F) :
    thetaT g = longestWeyl * theta g * longestWeyl := by
  have hs : sigma g = longestWeyl * transposeGL g * longestWeyl :=
    Units.ext (by rw [coe_sigma, sigmaMat_eq, Units.val_mul, Units.val_mul, coe_transposeGL]; rfl)
  have hw : (longestWeyl : GL (Fin n) F)⁻¹ = longestWeyl :=
    inv_eq_of_mul_eq_one_right longestWeyl_mul_self
  rw [theta, hs, thetaT_apply]
  simp only [_root_.mul_inv_rev, hw, mul_assoc, longestWeyl_mul_self, mul_one]
  rw [← mul_assoc, longestWeyl_mul_self, one_mul]

theorem rank_whittaker_le_one (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  by_cases h0 : equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F)) = ⊥
  · rw [h0, rank_bot]
    exact zero_le_one
  refine rank_whittaker_le_one_of_contragredient ψ₀ hψ hψ₁ π hπ ?_
  obtain ⟨ℓ, hℓ, hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨E⟩ := nonempty_equiv_contragredient π hπ
  set w₀ : GL (Fin n) F := longestWeyl
  let ℓ' : Module.Dual ℂ (smoothVectors (Representation.dual π)) :=
    ℓ ∘ₗ π w₀ ∘ₗ E.toLinearEquiv.toLinearMap
  have hℓ' : ∀ x, ℓ' x = ℓ (π w₀ (E.toLinearEquiv x)) := fun _ => rfl
  have hmem : ℓ' ∈ equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) := by
    intro u x
    rw [hℓ', hℓ', Representation.Equiv.toLinearEquiv_apply, E.toIntertwiningMap.isIntertwining,
      ← Representation.Equiv.toLinearEquiv_apply]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, thetaT_eq_longestWeyl]
    have e : w₀ * (longestWeyl * theta (u : GL (Fin n) F) * longestWeyl) =
        theta (u : GL (Fin n) F) * w₀ := by
      simp only [w₀, ← mul_assoc, longestWeyl_mul_self, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    have := hℓ ⟨theta (u : GL (Fin n) F), theta_mem_unipotent u.2⟩ (π w₀ (E.toLinearEquiv x))
    simp only at this
    rw [this, psiN_theta ψ₀ u.2]
  intro hbot
  rw [hbot] at hmem
  have h0' : ℓ' = 0 := (Submodule.mem_bot ℂ).1 hmem
  apply hℓ0
  refine LinearMap.ext fun v => ?_
  have := congrArg (fun φ : Module.Dual ℂ (smoothVectors (Representation.dual π)) =>
    φ (E.toLinearEquiv.symm (π w₀ v))) h0'
  simp only [hℓ', LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at this
  rw [← Module.End.mul_apply, ← map_mul, longestWeyl_mul_self, map_one, Module.End.one_apply]
    at this
  rw [this, LinearMap.zero_apply]

end GroundTheory.Automorphic.ContragredientTranspose
