import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RealOfFixedByConjugations
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGFree
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGLam
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGTheta
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGStd
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGSemi

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

section

variable {Z O L : Type} [CommRing Z] [CommRing O] [AddCommGroup L] [Module O L]

theorem padic_act {N : ℕ} (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x)) (a : O)
    (u : Z ⊗[ℤ] L) :
    φ (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) =
      ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    rw [LinearMap.baseChange_tmul]
    exact hφ z a x
  | add u v hu hv => simp only [map_add, hu, hv, smul_add]

private theorem baseChange_antisymm_of_self_eq_zero (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z u v = - B.baseChange Z v u := by
  have hs : ∀ x y, B x y = - B y x := by
    intro x y
    have h := hB (x + y)
    simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hs x y, neg_smul, mul_comm]
    | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw, neg_add]
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu', neg_add]

theorem padic_alt (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u : Z ⊗[ℤ] L) :
    B.baseChange Z u u = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x => rw [LinearMap.BilinForm.baseChange_tmul, hB, zero_smul]
  | add u v hu hv =>
    simp only [map_add, LinearMap.add_apply, hu, hv]
    rw [baseChange_antisymm_of_self_eq_zero B hB u v]
    abel

theorem padic_adj (bar : O ≃+* O) (B : LinearMap.BilinForm ℤ L) (hB : ∀ (a : O) x y, B (a • x) y = B x (bar a • y))
    (a : O) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) v =
      B.baseChange Z u (LinearMap.baseChange Z (LinearMap.lsmul O L (bar a)).toAddMonoidHom.toIntLinearMap v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply,
        LinearMap.BilinForm.baseChange_tmul]
      rw [hB]
    | add v w hv hw => simp only [map_add, hv, hw]
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']

theorem padic_form {N : ℕ} (bar : O ≃+* O) (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x))
    (B : LinearMap.BilinForm ℤ L) (h1 : ∀ x, B x x = 0) (h2 : Function.Bijective (B.baseChange Z))
    (h3 : ∀ (a : O) x y, B (a • x) y = B x (bar a • y)) :
    ∃ ψ : LinearMap.BilinForm Z (Fin N → Z ⊗[ℤ] O), (∀ u v, ψ (φ u) (φ v) = B.baseChange Z u v) ∧
      (∀ x, ψ x x = 0) ∧ Function.Bijective ψ ∧ ∀ (a : Z ⊗[ℤ] O) x y, ψ (a • x) y =
        ψ x (Algebra.TensorProduct.map (AlgHom.id Z Z) bar.toRingHom.toIntAlgHom a • y) := by
  refine ⟨(B.baseChange Z).compl₁₂ φ.symm.toLinearMap φ.symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp
  · intro x
    simp [padic_alt B h1]
  · constructor
    · intro x y hxy
      apply φ.symm.injective
      apply h2.1
      refine LinearMap.ext fun w => ?_
      have := LinearMap.congr_fun hxy (φ w)
      simpa using this
    · intro f
      obtain ⟨u, hu⟩ := h2.2 (f.comp φ.toLinearMap)
      refine ⟨φ u, LinearMap.ext fun y => ?_⟩
      have := LinearMap.congr_fun hu (φ.symm y)
      simpa using this
  · intro a x y
    obtain ⟨u, rfl⟩ := φ.surjective x
    obtain ⟨v, rfl⟩ := φ.surjective y
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul z c =>
      have hz : ∀ (c' : O) (w : Z ⊗[ℤ] L), (z ⊗ₜ[ℤ] c' : Z ⊗[ℤ] O) • φ w =
          z • φ (LinearMap.baseChange Z (LinearMap.lsmul O L c').toAddMonoidHom.toIntLinearMap w) := by
        intro c' w
        rw [padic_act φ hφ c' w, ← smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul]
      have e1 : (AlgHom.id Z Z) z = z := rfl
      have e2 : bar.toRingHom.toIntAlgHom c = bar c := rfl
      rw [e1, e2, hz, hz]
      simp only [LinearMap.map_smul, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.smul_apply, padic_adj bar B h3]
    | add a a' ha ha' => simp only [add_smul, map_add, LinearMap.add_apply, ha, ha']

end

theorem padic_unit (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] (d : R)
    (h : IsCoprime d (p : R)) : IsUnit d := by
  obtain ⟨a, b, hab⟩ := h
  have hp : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hN : (⊤ : Submodule ℤ_[p] R) ≤ (Ideal.span {a * d}).restrictScalars ℤ_[p] := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[p])
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro x _
    have hx : x = a * d * x + (p : ℤ_[p]) • (b * x) := by
      rw [Algebra.smul_def, map_natCast]
      linear_combination (-x) * hab
    rw [hx]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Submodule.smul_mem_smul hp Submodule.mem_top)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hN Submodule.mem_top : (1 : R) ∈ _)
  have hu : IsUnit (a * d) := IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)
  exact isUnit_of_mul_isUnit_right hu

theorem padic_freeZ (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L] [Module (𝓞 E) L]
    [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Finite ℤ L ∧ Module.Free ℤ L := by
  have h1 : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have h2 : Module.Flat ℤ L := Module.Flat.trans ℤ (𝓞 E) L
  exact ⟨h1, inferInstance⟩

theorem tw_g_padic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v := by
  intro E _ _ _ bar hbar hunr p _ L L' _ _ _ _ _ _ _ _ B B' hrk h1 h2 h3 k1 k2 k3
  obtain ⟨_, _⟩ := padic_freeZ E L
  obtain ⟨_, _⟩ := padic_freeZ E L'
  obtain ⟨φ, hφ⟩ := tw_g_free E p L
  have hL' := tw_g_free E p L'
  rw [← hrk] at hL'
  obtain ⟨φ', hφ'⟩ := hL'
  obtain ⟨ψ, hψ, a1, a2, a3⟩ := padic_form bar φ hφ B h1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L B h2) h3
  obtain ⟨ψ', hψ', b1, b2, b3⟩ := padic_form bar φ' hφ' B' k1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L' B' k2) k3
  obtain ⟨lam, l1, l2⟩ := tw_g_lam E bar hbar hunr p
  obtain ⟨θ, hθ⟩ := tw_g_theta E bar hbar hunr p Fact.out
  have hbb : ∀ a, bar (bar a) = a := fun a => RingOfIntegers.ext (by
    rw [hbar, hbar, IsCMField.complexConj_apply_apply])
  have hσ : ∀ r : ℤ_[p] ⊗[ℤ] 𝓞 E, Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom
      (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = r := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact congrArg (z ⊗ₜ[ℤ] ·) (hbb a)
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hu : ∃ t : ℤ_[p] ⊗[ℤ] 𝓞 E,
      IsUnit (t - Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom t) := by
    refine ⟨1 ⊗ₜ θ, padic_unit p _ _ ?_⟩
    have := hθ.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := 𝓞 E)).toRingHom
    rw [map_natCast, map_sub] at this
    exact this
  obtain ⟨e, he⟩ := tw_g_std ℤ_[p] _ _ hσ lam l1 l2 _ (tw_g_semi p _ _ hσ hu _) ψ ψ' a1 a2 a3 b1 b2 b3
  refine ⟨φ ≪≫ₗ e.restrictScalars ℤ_[p] ≪≫ₗ φ'.symm, fun a x => ?_, fun u v => ?_⟩
  · apply φ'.injective
    rw [padic_act φ' hφ']
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    rw [hφ, map_smul]
  · rw [← hψ', ← hψ]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    exact he _ _

end PositivityTheory.UnitarySelfGeneration
