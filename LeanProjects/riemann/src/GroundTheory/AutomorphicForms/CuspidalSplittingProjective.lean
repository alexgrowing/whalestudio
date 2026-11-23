import Mathlib
import GroundTheory.AutomorphicForms.CuspidalSplittingPositivity
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin n) F) V}
  {ρ : Representation ℂ (GL (Fin n) F) U} {σ : Representation ℂ (GL (Fin n) F) W}
  {ω : GL (Fin n) F → ℂ}

theorem exists_coeffSum_eq_smul_ne_zero [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) :
    ∃ K : Subgroup (GL (Fin n) F), IsCompact (K : Set (GL (Fin n) F)) ∧
      IsOpen (K : Set (GL (Fin n) F)) ∧ ∃ f : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, f (π k x) = f x) ∧
        ∃ v ∈ fixedVectors π K, ∃ c : ℂ, c ≠ 0 ∧ ∀ w, coeffSum π π K f v w = c • w := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, w₀, hw₀⟩ := exists_coeffSum_ne_zero hπ hsc hωπ
  obtain ⟨c, hc⟩ := exists_coeffSum_eq_smul hπ hsc hKo hωπ hf hv
  refine ⟨K, hKc, hKo, f, hf, v, hv, c, fun h0 => hw₀ ?_, hc⟩
  rw [hc, h0, zero_smul]

theorem isSmooth_of_surjective (hρ : IsSmooth ρ) (p : Representation.IntertwiningMap ρ σ)
    (hp : Surjective p) : IsSmooth σ := by
  intro y
  obtain ⟨u, rfl⟩ := hp y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ u)
  rw [mem_stabilizerOf] at hg ⊢
  rw [← Representation.IntertwiningMap.isIntertwining, hg]

theorem exists_lift_of_isSupercuspidal [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ)
    (hωρ : HasCentralChar ρ ω) (p : Representation.IntertwiningMap ρ σ) (hp : Surjective p)
    (φ : Representation.IntertwiningMap π σ) :
    ∃ s : Representation.IntertwiningMap π ρ, p.comp s = φ := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, c, hc0, hc⟩ := exists_coeffSum_eq_smul_ne_zero hπ hsc hωπ
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1 :=
    fun z hz => hωπ.inv_mul hu₀ hz
  have hσ := isSmooth_of_surjective hρ p hp
  have hφv : φ v ∈ fixedVectors σ K := map_mem_fixedVectors π φ hv
  obtain ⟨u, hu⟩ := fixedMap_surjective hρ hσ hKc hKo hp ⟨φ v, hφv⟩
  have hpu : p (u : U) = φ v := congrArg Subtype.val hu
  refine ⟨c⁻¹ • coeffMap hπ hsc hKo hωπ hωρ hω hf u.2, ?_⟩
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  change p (c⁻¹ • coeffSum π ρ K f (u : U) w) = φ w
  rw [map_smul, map_coeffSum hπ hsc hKo hf, hpu, ← map_coeffSum hπ hsc hKo hf, hc, map_smul,
    smul_smul, inv_mul_cancel₀ hc0, one_smul]

section Injective

variable (σ π) in

def pairingSum (K : Subgroup (GL (Fin n) F)) (ψ : Module.Dual ℂ W) (v : V) (b : W)
    (ũ : smoothVectors (Representation.dual π)) : ℂ :=
  quotSum (centerSup K) fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)

variable {K : Subgroup (GL (Fin n) F)} {ψ : Module.Dual ℂ W} {v : V}

theorem finite_support_pairingSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K =>
      ψ (σ q.out⁻¹ b) * (ũ : Module.Dual ℂ V) (π q.out v) :=
  finite_support_centerSup (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) hKo
    (isCompactModCenter_matrixCoeff hπ hsc v ũ.2) fun g h0 => by
      change (ũ : Module.Dual ℂ V) (π g v) = 0 at h0
      simp only [h0, mul_zero]

theorem pairingSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x) (hv : v ∈ fixedVectors π K) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ∀ g, ∀ h ∈ centerSup K, ψ (σ (g * h)⁻¹ b) * (ũ : Module.Dual ℂ V) (π (g * h) v) =
      ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) := by
  refine rightInv_centerSup
    (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : σ (g * z)⁻¹ b = ω z⁻¹ • σ g⁻¹ b := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωσ _ (inv_mem hz)]
    have e2 : π (g * z) v = ω z • π g v := by
      rw [map_mul, Module.End.mul_apply, hωπ z hz, map_smul]
    simp only [e1, e2, map_smul, smul_eq_mul]
    linear_combination ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) * hω z hz
  · have e1 : σ (g * k)⁻¹ b = σ k⁻¹ (σ g⁻¹ b) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    simp only [e1, hψ _ (inv_mem hk), map_mul, Module.End.mul_apply, hv k hk]

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
  (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
  (hv : v ∈ fixedVectors π K)

include hπ hsc hωπ hωσ hω hKo hψ hv

omit hπ hsc hKo in

theorem pairingSum_act (h : GL (Fin n) F) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) := by
  unfold pairingSum
  rw [← quotSum_mul_left (pairingSum_summand_rightInv hωπ hωσ hω hψ hv (σ h b) ũ) h]
  refine quotSum_congr fun g => ?_
  rw [contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul, Module.End.mul_apply,
    ← Module.End.mul_apply (σ h⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_mul, Module.End.mul_apply]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_add (b : W) (ũ₁ ũ₂ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (ũ₁ + ũ₂) = pairingSum π σ K ψ v b ũ₁ + pairingSum π σ K ψ v b ũ₂ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b ũ₁)
    (finite_support_pairingSum hπ hsc hKo b ũ₂)]
  refine finsum_congr fun q => ?_
  simp only [Submodule.coe_add, LinearMap.add_apply, mul_add]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul (b : W) (c : ℂ) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (c • ũ) = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit hωπ hωσ hω hψ hv in
theorem pairingSum_add_left (b₁ b₂ : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (b₁ + b₂) ũ = pairingSum π σ K ψ v b₁ ũ + pairingSum π σ K ψ v b₂ ũ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b₁ ũ)
    (finite_support_pairingSum hπ hsc hKo b₂ ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_add, add_mul]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul_left (c : ℂ) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (c • b) ũ = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_smul, smul_eq_mul]
  ring

omit hωπ hωσ hω hψ hv in

def pairingForm (b : W) : Module.Dual ℂ (smoothVectors (Representation.dual π)) where
  toFun := pairingSum π σ K ψ v b
  map_add' := pairingSum_add hπ hsc hKo b
  map_smul' c ũ := pairingSum_smul hπ hsc hKo b c ũ

theorem pairingForm_mem (hσ : IsSmooth σ) (b : W) :
    pairingForm (σ := σ) hπ hsc hKo (K := K) (ψ := ψ) (v := v) b ∈
      smoothVectors (Representation.dual (contragredient π)) := by
  rw [mem_smoothVectors]
  refine Subgroup.isOpen_mono (fun h hh => ?_) (hσ b)
  rw [mem_stabilizerOf] at hh ⊢
  refine LinearMap.ext fun ũ => ?_
  rw [dual_apply_apply]
  change pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) = pairingSum π σ K ψ v b ũ
  rw [← pairingSum_act hωπ hωσ hω hψ hv, hh]

omit hπ hsc hωπ hωσ hω hKo hψ hv in

def pairingMap (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
    (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) :
    Representation.IntertwiningMap σ (contragredient (contragredient π)) where
  toFun b := ⟨pairingForm (σ := σ) hπ hsc hKo b, pairingForm_mem hπ hsc hωπ hωσ hω hKo hψ hv hσ b⟩
  map_add' b₁ b₂ := Subtype.ext (LinearMap.ext fun ũ => pairingSum_add_left hπ hsc hKo b₁ b₂ ũ)
  map_smul' c b := Subtype.ext (LinearMap.ext fun ũ => pairingSum_smul_left hπ hsc hKo c b ũ)
  isIntertwining' h := LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun ũ => by
    change pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ)
    exact pairingSum_act hωπ hωσ hω hψ hv h b ũ)

omit hπ hsc hωπ hωσ hω hKo hψ hv in
theorem pairingMap_apply_apply (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ((pairingMap hπ hsc hωπ hωσ hω hKo hψ hv hσ b :
      smoothVectors (Representation.dual (contragredient π))) :
        Module.Dual ℂ (smoothVectors (Representation.dual π))) ũ = pairingSum π σ K ψ v b ũ := rfl

end Injective

theorem exists_extend_of_isSupercuspidal [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hωσ : HasCentralChar σ ω) (i : Representation.IntertwiningMap ρ σ) (hi : Injective i)
    (φ : Representation.IntertwiningMap ρ π) :
    ∃ Φ : Representation.IntertwiningMap σ π, Φ.comp i = φ := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, c, hc0, hc⟩ := exists_coeffSum_eq_smul_ne_zero hπ hsc hωπ
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1 :=
    fun z hz => hωπ.inv_mul hu₀ hz

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective i.toLinearMap
    (LinearMap.ker_eq_bot.2 hi)
  let ψ : Module.Dual ℂ W := (f ∘ₗ φ.toLinearMap ∘ₗ l) ∘ₗ (fixedVectors σ K).subtype ∘ₗ
    fixedProj σ hσ hKc hKo
  have hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x := fun k hk x => by
    simp only [ψ, LinearMap.comp_apply, fixedProj_apply_act hσ hKc hKo hk]
  have hψi : ∀ u, ψ (i u) = f (φ u) := by
    have h := eq_of_invariant_of_eqOn hρ hKc hKo (f := ψ ∘ₗ i.toLinearMap)
      (g := f ∘ₗ φ.toLinearMap)
      (fun k hk u => by
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining, hψ k hk])
      (fun k hk u => by
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining, hf k hk])
      (fun u hu => by
        have hiu : i u ∈ fixedVectors σ K := map_mem_fixedVectors ρ i hu
        have hl' : l (i u) = u := LinearMap.congr_fun hl u
        simp only [ψ, LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Submodule.subtype_apply, fixedProj_apply_of_mem hσ hKc hKo hiu, hl'])
    exact fun u => LinearMap.congr_fun h u

  have hπa := isAdmissible_of_isIrreducible hπ
  let e := (toDoubleContragredient hπa.1).ofBijective (toDoubleContragredient_bijective hπa)
  let Φ₀ := pairingMap hπ hsc hωπ hωσ hω hKo hψ hv hσ
  refine ⟨c⁻¹ • (e.symm.toIntertwiningMap.comp Φ₀), ?_⟩
  have key : ∀ u, Φ₀ (i u) = c • toDoubleContragredient hπa.1 (φ u) := fun u =>
    Subtype.ext (LinearMap.ext fun ũ => by
      rw [pairingMap_apply_apply]
      change pairingSum π σ K ψ v (i u) ũ = c * (ũ : Module.Dual ℂ V) (φ u)
      unfold pairingSum
      calc quotSum (centerSup K) (fun g => ψ (σ g⁻¹ (i u)) * (ũ : Module.Dual ℂ V) (π g v))
          = quotSum (centerSup K) (fun g => (ũ : Module.Dual ℂ V) (f (π g⁻¹ (φ u)) • π g v)) :=
            quotSum_congr fun g => by
              rw [← Representation.IntertwiningMap.isIntertwining, hψi,
                Representation.IntertwiningMap.isIntertwining, map_smul, smul_eq_mul]
        _ = (ũ : Module.Dual ℂ V) (coeffSum π π K f v (φ u)) :=
            (linearMap_finsum _ (finite_support_coeffSum hπ hsc hKo hf (φ u))).symm
        _ = c * (ũ : Module.Dual ℂ V) (φ u) := by rw [hc, map_smul, smul_eq_mul])
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_)
  change c⁻¹ • e.symm (Φ₀ (i u)) = φ u
  rw [key, map_smul]
  change c⁻¹ • c • e.symm (e (φ u)) = φ u
  rw [Representation.Equiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end Parabolic

end GroundTheory.Automorphic
