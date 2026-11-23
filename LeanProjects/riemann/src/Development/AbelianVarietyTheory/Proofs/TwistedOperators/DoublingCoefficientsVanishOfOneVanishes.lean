import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible MeasureTheory

namespace GlobalTheory.DoublingVanish

theorem exists_eigen_form {E H : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : E →ₗ[ℂ] H) (hj : Function.Injective j)
    (β : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (v : E) (hv : v ≠ 0) :
    ∃ (c : ℂ) (y : E), y ≠ 0 ∧ ∀ w, β y w = c * inner ℂ (j w) (j y) := by
  classical
  have : Nontrivial E := nontrivial_of_ne v 0 hv
  let Φ : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun y w => inner ℂ (j w) (j y))
    (fun y₁ y₂ w => by simp only [map_add, inner_add_right])
    (fun c y w => by simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul])
    (fun y w₁ w₂ => by simp only [map_add, inner_add_left])
    (fun c y w => by simp only [map_smul, inner_smul_left, smul_eq_mul])
  have hΦ : ∀ y w, Φ y w = inner ℂ (j w) (j y) := fun y w => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : inner ℂ (j y) (j y) = (0 : ℂ) := by rw [← hΦ, hy, LinearMap.zero_apply]
    rw [inner_self_eq_zero] at h1
    exact hj (by rw [h1, map_zero])
  have hsurj : Function.Surjective Φ := by
    intro f
    let K := LinearMap.range j
    have : FiniteDimensional ℂ K := LinearMap.finiteDimensional_range j
    have : CompleteSpace K := FiniteDimensional.complete ℂ K
    let e : E ≃ₗ[ℂ] K := LinearEquiv.ofInjective j hj
    have he : ∀ x, ((e x : K) : H) = j x := fun x => rfl
    let ℓ : K →ₗ[ℂ] ℂ :=
      { toFun := fun x => star (f (e.symm x))
        map_add' := fun x y => by simp only [map_add, star_add]
        map_smul' := fun c x => by
          show star (f (e.symm (c • x))) = c * star (f (e.symm x))
          rw [map_smul, map_smulₛₗ, smul_eq_mul, star_mul', starRingEnd_apply, star_star] }
    let z : K := (InnerProductSpace.toDual ℂ K).symm (LinearMap.toContinuousLinearMap ℓ)
    have hz : ∀ x : K, inner ℂ z x = star (f (e.symm x)) := fun x =>
      InnerProductSpace.toDual_symm_apply
    have h1 : ((z : K) : H) = j (e.symm z) := by rw [← he, LinearEquiv.apply_symm_apply]
    refine ⟨e.symm z, ?_⟩
    ext w
    rw [hΦ, ← h1, ← he w, ← Submodule.coe_inner, ← inner_conj_symm, hz,
      LinearEquiv.symm_apply_apply, starRingEnd_apply, star_star]
  let Ψ : E ≃ₗ[ℂ] (E →ₗ⋆[ℂ] ℂ) := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let A : E →ₗ[ℂ] E := Ψ.symm.toLinearMap ∘ₗ β
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  refine ⟨c, y, hy.2, fun w => ?_⟩
  have h1 : A y = c • y := hy.apply_eq_smul
  have h2 : β y = Φ (A y) := by
    show β y = Ψ (Ψ.symm (β y))
    rw [LinearEquiv.apply_symm_apply]
  rw [h2, h1, map_smul, LinearMap.smul_apply, hΦ, smul_eq_mul]

variable {p q : ℕ} {T : GrpData p q}

theorem inner_map (σ : URep T) (k : T.G) (a b : σ.H) : inner ℂ (σ.π k a) (σ.π k b) = inner ℂ a b := by
  let L : σ.H →ₗᵢ[ℂ] σ.H := { toLinearMap := (σ.π k).toLinearMap, norm_map' := σ.isom k }
  exact L.inner_map_map a b

theorem pi_mul (σ : URep T) (g h : T.G) (a : σ.H) : σ.π (g * h) a = σ.π g (σ.π h a) := by
  rw [map_mul]
  rfl

theorem inner_left (σ : URep T) (k g : T.G) (a b : σ.H) :
    inner ℂ (σ.π k a) (σ.π g b) = inner ℂ a (σ.π (k⁻¹ * g) b) := by
  rw [← inner_map σ k a (σ.π (k⁻¹ * g) b), ← pi_mul, mul_inv_cancel_left]

theorem integrable_mul (σ : URep T) (a b : σ.H) {f : T.G → ℂ} (hf : Integrable f T.haar) :
    Integrable (fun g => inner ℂ a (σ.π g b) * star (f g)) T.haar := by
  refine Integrable.mono' (hf.norm.const_mul (‖a‖ * ‖b‖)) ?_ ?_
  · exact ((continuous_const.inner (σ.cont b)).aestronglyMeasurable).mul
      (continuous_star.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  · refine ae_of_all _ fun g => ?_
    rw [norm_mul, norm_star]
    have h1 : ‖inner ℂ a (σ.π g b)‖ ≤ ‖a‖ * ‖b‖ := by
      calc ‖inner ℂ a (σ.π g b)‖ ≤ ‖a‖ * ‖σ.π g b‖ := norm_inner_le_norm _ _
        _ = ‖a‖ * ‖b‖ := by rw [σ.isom]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

theorem vanish : ∀ (p q : ℕ) (T : GrpData p q) (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), Function.Injective j₂ → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') → (∀ U : Submodule ℂ E, (∀ k ∈ T.Kset, ∀ w ∈ U, ∀ w' : E, π₂.π k (j₂ w) = j₂ w' → w' ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ v : E, v ≠ 0 → MeasureTheory.Integrable (fun g => inner ℂ (j₂ v) (π₂.π g (j₂ v))) T.haar → (∀ z : π₁.H, ∫ g, inner ℂ z (π₁.π g (j₁ v)) * star (inner ℂ (j₂ v) (π₂.π g (j₂ v))) ∂T.haar = 0) → (∀ x y u w : E, MeasureTheory.Integrable (fun g => inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w)))) T.haar ∧ ∫ g, inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar = 0) := by
  intro p q T π₁ π₂ E iE mE fE j₁ j₂ hj₂ hK hirr v hv hint h0
  have : T.haar.IsMulRightInvariant := (GlobalTheory.HolDS.haar_unimodular p q T).1
  choose! act hact using hK
  have hj1a : ∀ k ∈ T.Kset, ∀ w, j₁ (act k w) = π₁.π k (j₁ w) := fun k hk w => ((hact k hk w).1).symm
  have hj2a : ∀ k ∈ T.Kset, ∀ w, j₂ (act k w) = π₂.π k (j₂ w) := fun k hk w => ((hact k hk w).2).symm
  have hback : ∀ (σ : URep T) (g : T.G) (x : σ.H), σ.π g (σ.π g⁻¹ x) = x := by
    intro σ g x
    rw [← pi_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  have hback2 : ∀ (σ : URep T) (g : T.G) (x : σ.H), σ.π g⁻¹ (σ.π g x) = x := by
    intro σ g x
    rw [← pi_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]

  have htop : ∀ U : Submodule ℂ E, (∀ k ∈ T.Kset, ∀ w ∈ U, act k w ∈ U) →
      ∀ x : E, x ≠ 0 → x ∈ U → ∀ w, w ∈ U := by
    intro U hU x hx hxU w
    rcases hirr U (fun k hk w hw w' hw' => by
        have : w' = act k w := hj₂ (by rw [← hw', hj2a k hk])
        rw [this]
        exact hU k hk w hw) with h | h
    · rw [h, Submodule.mem_bot] at hxU
      exact absurd hxU hx
    · rw [h]
      exact Submodule.mem_top

  have coef1 : ∀ u, Integrable (fun g => inner ℂ (j₂ u) (π₂.π g (j₂ v))) T.haar := by
    let U0 : Submodule ℂ E :=
      { carrier := {u | Integrable (fun g => inner ℂ (j₂ u) (π₂.π g (j₂ v))) T.haar}
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_ofPred_eq, map_add, inner_add_left] at hx hy ⊢
          exact hx.add hy
        zero_mem' := by simp
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_ofPred_eq, map_smul, inner_smul_left] at hx ⊢
          exact hx.const_mul _ }
    intro u
    have hu : u ∈ U0 := by
      refine htop U0 (fun k hk w hw => ?_) v hv hint u
      have hw' : Integrable (fun g => inner ℂ (j₂ w) (π₂.π g (j₂ v))) T.haar := hw
      show Integrable (fun g => inner ℂ (j₂ (act k w)) (π₂.π g (j₂ v))) T.haar
      simp only [hj2a k hk, inner_left]
      exact hw'.comp_mul_left k⁻¹
    exact hu

  have coefI : ∀ u w, Integrable (fun g => inner ℂ (j₂ u) (π₂.π g (j₂ w))) T.haar := by
    let U1 : Submodule ℂ E :=
      { carrier := {w | ∀ u, Integrable (fun g => inner ℂ (j₂ u) (π₂.π g (j₂ w))) T.haar}
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_ofPred_eq] at hx hy ⊢
          intro u
          simp only [map_add, inner_add_right]
          exact (hx u).add (hy u)
        zero_mem' := by simp
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          intro u
          simp only [map_smul, inner_smul_right]
          exact (hx u).const_mul _ }
    intro u w
    have hw : w ∈ U1 := by
      refine htop U1 (fun k hk x hx => ?_) v hv coef1 w
      have hx' : ∀ u', Integrable (fun g => inner ℂ (j₂ u') (π₂.π g (j₂ x))) T.haar := hx
      show ∀ u', Integrable (fun g => inner ℂ (j₂ u') (π₂.π g (j₂ (act k x)))) T.haar
      intro u'
      simp only [hj2a k hk, ← pi_mul]
      exact (hx' u').comp_mul_right k
    exact (hw : ∀ u', Integrable (fun g => inner ℂ (j₂ u') (π₂.π g (j₂ w))) T.haar) u
  have prodI : ∀ (a b : π₁.H) (u w : E),
      Integrable (fun g => inner ℂ a (π₁.π g b) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w)))) T.haar :=
    fun a b u w => integrable_mul π₁ a b (coefI u w)

  have leftI : ∀ (k : T.G) (a b : π₁.H) (c : π₂.H) (w : E),
      ∫ g, inner ℂ (π₁.π k a) (π₁.π g b) * star (inner ℂ (π₂.π k c) (π₂.π g (j₂ w))) ∂T.haar =
      ∫ g, inner ℂ a (π₁.π g b) * star (inner ℂ c (π₂.π g (j₂ w))) ∂T.haar := by
    intro k a b c w
    simp only [inner_left]
    exact integral_mul_left_eq_self
      (fun g => inner ℂ a (π₁.π g b) * star (inner ℂ c (π₂.π g (j₂ w)))) k⁻¹
  have rightI : ∀ k ∈ T.Kset, ∀ (a : π₁.H) (c : π₂.H) (y w : E),
      ∫ g, inner ℂ a (π₁.π g (j₁ (act k y))) * star (inner ℂ c (π₂.π g (j₂ (act k w)))) ∂T.haar =
      ∫ g, inner ℂ a (π₁.π g (j₁ y)) * star (inner ℂ c (π₂.π g (j₂ w))) ∂T.haar := by
    intro k hk a c y w
    simp only [hj1a k hk, hj2a k hk, ← pi_mul]
    exact integral_mul_right_eq_self
      (fun g => inner ℂ a (π₁.π g (j₁ y)) * star (inner ℂ c (π₂.π g (j₂ w)))) k

  have stepA : ∀ (a : π₁.H) (u : E),
      ∫ g, inner ℂ a (π₁.π g (j₁ v)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ v))) ∂T.haar = 0 := by
    let SA : Submodule ℂ E :=
      { carrier := {u | ∀ a : π₁.H,
          ∫ g, inner ℂ a (π₁.π g (j₁ v)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ v))) ∂T.haar = 0}
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_ofPred_eq] at hx hy ⊢
          intro a
          simp only [map_add, inner_add_left, star_add, mul_add]
          rw [integral_add (prodI a (j₁ v) x v) (prodI a (j₁ v) y v), hx a, hy a, add_zero]
        zero_mem' := by
          simp only [Set.mem_ofPred_eq]
          intro a
          simp
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          intro a
          simp only [map_smul, inner_smul_left, star_mul', starRingEnd_apply, star_star,
            mul_left_comm _ c]
          rw [integral_const_mul, hx a, mul_zero] }
    intro a u
    have hu : ∀ a' : π₁.H,
        ∫ g, inner ℂ a' (π₁.π g (j₁ v)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ v))) ∂T.haar = 0 := by
      refine htop SA (fun k hk w hw => ?_) v hv h0 u
      have hw' : ∀ a' : π₁.H,
          ∫ g, inner ℂ a' (π₁.π g (j₁ v)) * star (inner ℂ (j₂ w) (π₂.π g (j₂ v))) ∂T.haar = 0 := hw
      show ∀ a' : π₁.H,
          ∫ g, inner ℂ a' (π₁.π g (j₁ v)) * star (inner ℂ (j₂ (act k w)) (π₂.π g (j₂ v))) ∂T.haar = 0
      intro a'
      have e1 := leftI k (π₁.π k⁻¹ a') (j₁ v) (j₂ w) v
      rw [hback π₁ k a'] at e1
      rw [hj2a k hk, e1]
      exact hw' _
    exact hu a

  have stepB : ∀ (a : π₁.H) (u y w : E),
      ∫ g, inner ℂ a (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar = 0 := by
    intro a u
    let β : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun y w => ∫ g, inner ℂ a (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar)
      (fun y₁ y₂ w => by
        simp only [map_add, inner_add_right, add_mul]
        exact integral_add (prodI a (j₁ y₁) u w) (prodI a (j₁ y₂) u w))
      (fun c y w => by
        simp only [map_smul, inner_smul_right, mul_assoc, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _)
      (fun y w₁ w₂ => by
        simp only [map_add, inner_add_right, star_add, mul_add]
        exact integral_add (prodI a (j₁ y) u w₁) (prodI a (j₁ y) u w₂))
      (fun c y w => by
        simp only [map_smul, inner_smul_right, star_mul', mul_left_comm _ (star c), smul_eq_mul,
          starRingEnd_apply]
        exact integral_const_mul (star c) _)
    have hβ : ∀ y w, β y w =
        ∫ g, inner ℂ a (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar :=
      fun y w => rfl
    obtain ⟨c, y₀, hy₀, hc⟩ := exists_eigen_form j₂ hj₂ β v hv
    let U : Submodule ℂ E :=
      { carrier := {y | ∀ w, β y w = c * inner ℂ (j₂ w) (j₂ y)}
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_ofPred_eq] at hx hy ⊢
          intro w
          rw [map_add β x y, LinearMap.add_apply, hx w, hy w, map_add j₂ x y, inner_add_right, mul_add]
        zero_mem' := by
          simp only [Set.mem_ofPred_eq]
          intro w
          rw [map_zero β, LinearMap.zero_apply, map_zero j₂, inner_zero_right, mul_zero]
        smul_mem' := by
          intro d x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          intro w
          rw [map_smul β d x, LinearMap.smul_apply, hx w, map_smul j₂ d x, inner_smul_right,
            smul_eq_mul, mul_left_comm] }
    have hsurj : ∀ k ∈ T.Kset, ∀ w'', ∃ w, act k w = w'' := by
      intro k hk
      let Ak : E →ₗ[ℂ] E :=
        { toFun := act k
          map_add' := fun x y => hj₂ (by simp only [hj2a k hk, map_add])
          map_smul' := fun d x => hj₂ (by simp only [hj2a k hk, map_smul, RingHom.id_apply]) }
      have hAk : Function.Injective Ak := by
        intro x y hxy
        apply hj₂
        have h1 : π₂.π k (j₂ x) = π₂.π k (j₂ y) := by
          rw [← hj2a k hk, ← hj2a k hk]
          exact congrArg j₂ hxy
        have h2 := congrArg (π₂.π k⁻¹) h1
        rwa [hback2, hback2] at h2
      exact LinearMap.injective_iff_surjective.mp hAk
    have hU : ∀ k ∈ T.Kset, ∀ y ∈ U, act k y ∈ U := by
      intro k hk y hy
      have hy' : ∀ w, β y w = c * inner ℂ (j₂ w) (j₂ y) := hy
      show ∀ w, β (act k y) w = c * inner ℂ (j₂ w) (j₂ (act k y))
      intro w''
      obtain ⟨w, rfl⟩ := hsurj k hk w''
      rw [hβ, rightI k hk, ← hβ, hy' w, hj2a k hk, hj2a k hk, inner_map]
    have hall : ∀ y, y ∈ U := htop U hU y₀ hy₀ hc
    have hvv : β v v = c * inner ℂ (j₂ v) (j₂ v) :=
      (hall v : ∀ w, β v w = c * inner ℂ (j₂ w) (j₂ v)) v
    rw [hβ, stepA a u] at hvv
    have hne : inner ℂ (j₂ v) (j₂ v) ≠ (0 : ℂ) := by
      rw [Ne, inner_self_eq_zero]
      intro h
      exact hv (hj₂ (by rw [h, map_zero]))
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp hvv.symm with h | h
      · exact h
      · exact absurd h hne
    intro y w
    rw [← hβ, (hall y : ∀ w, β y w = c * inner ℂ (j₂ w) (j₂ y)) w, hc0, zero_mul]
  intro x y u w
  exact ⟨prodI (j₁ x) (j₁ y) u w, stepB (j₁ x) u y w⟩

end GlobalTheory.DoublingVanish
