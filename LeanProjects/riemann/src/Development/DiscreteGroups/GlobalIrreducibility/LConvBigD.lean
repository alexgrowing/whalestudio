import Development.DiscreteGroups.GlobalIrreducibility.LConvBigC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem small_fix (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) (v₁ : V₁) (v₂ : V₂) (i j : Fin (m + 1)) (h : i ≠ j) :
    {t : k | π₁ (tv i j h (-t)) v₁ = v₁ ∧ π₂ (tv i j h (-t)) v₂ = v₂} ∈ 𝓝 (0 : k) := by
  have hc : Continuous fun t : k => tv i j h (-t) := (continuous_tv i j h).comp continuous_neg
  refine IsOpen.mem_nhds (((hs₁ v₁).preimage hc).inter ((hs₂ v₂).preimage hc)) ?_
  simp [tv_zero]

theorem last_ne_zero (hm : 0 < m) : Fin.last m ≠ (0 : Fin (m + 1)) := fun e => by
  have := congrArg Fin.val e
  simp at this
  omega

theorem transvection_apply_same (i j : Fin (m + 1)) (h : i ≠ j) (t : k) : Matrix.transvection i j t i j = t := by
  simp [Matrix.transvection, Matrix.one_apply_ne h]

theorem centralChar_eq (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω₁ ω₂ : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (h0 : l₁ v₁ ≠ 0) : ω₁ = ω₂ := by
  have hc : l₁ v₁ = l₂ v₂ := by
    have := hX 1
    rwa [corner_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
  have hL := last_ne_zero hm
  have hO := small_fix hs₁ hs₂ v₁ v₂ _ _ hL
  have key : ∀ t : k, ∀ ht : t ≠ 0, t ∈ {t : k | π₁ (tv _ _ hL (-t)) v₁ = v₁ ∧ π₂ (tv _ _ hL (-t)) v₂ = v₂} →
      ω₁ (Units.mk0 t ht) = ω₂ (Units.mk0 t ht) := by
    intro t ht hmem
    have hent : (((tv _ _ hL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 =
        (Units.mk0 t ht : k) := by
      rw [val_tv_inv, neg_neg, transvection_apply_same _ _ hL, Units.val_mk0]
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX _ _ hent
    rw [hmem.1, hmem.2, ← hc] at this
    exact Units.ext (mul_right_cancel₀ h0 this)
  refine MonoidHom.ext fun a => ?_
  obtain ⟨t, ht, htO, hatO⟩ := exists_small hO (a : k)
  have hat : (a : k) * t ≠ 0 := mul_ne_zero a.ne_zero ht
  have e : Units.mk0 ((a : k) * t) hat = a * Units.mk0 t ht := Units.ext (by simp)
  have h1 := key _ hat hatO
  rw [e, map_mul, map_mul, key _ ht htO] at h1
  exact mul_right_cancel h1

theorem agree_all (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω) (h₂ : HasCentralChar π₂ ω) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  have step : ∀ g : GL (Fin (m + 1)) k,
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 ≠ 0 →
      l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
    intro g hg
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX g (Units.mk0 _ hg) rfl
    exact mul_left_cancel₀ (ω (Units.mk0 _ hg)).ne_zero this
  by_cases hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 0
  swap
  · exact step g hg
  obtain ⟨j, hj⟩ : ∃ j, ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) j 0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h1 := congrFun (congrFun g.mul_inv 0) 0
    rw [Matrix.mul_apply] at h1
    simp [hall] at h1
  have hjL : Fin.last m ≠ j := fun e => hj (e ▸ hg)
  obtain ⟨t, ht, htO, -⟩ := exists_small (small_fix hs₁ hs₂ v₁ v₂ _ _ hjL) 1
  have hent : (((g * tv _ _ hjL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      (Fin.last m) 0 ≠ 0 := by
    rw [mul_inv_rev, Units.val_mul, val_tv_inv, neg_neg, Matrix.transvection_mul_apply_same, hg, zero_add]
    exact mul_ne_zero ht hj
  have := step _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, htO.1, htO.2] at this

end DiscreteGroups.sglob.LConv

end
