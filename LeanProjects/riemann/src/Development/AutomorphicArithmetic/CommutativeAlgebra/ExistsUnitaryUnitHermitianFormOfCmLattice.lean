import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData
import Development.AutomorphicArithmetic.RealSpanData.JSpan

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem exists_den {Λ : Type} [AddCommGroup Λ] (t : ℚ ⊗[ℤ] Λ) :
    ∃ (n : ℤ) (z : Λ), n ≠ 0 ∧ n • t = (1 : ℚ) ⊗ₜ[ℤ] z := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q z =>
    refine ⟨(q.den : ℤ), q.num • z, by exact_mod_cast q.den_nz, ?_⟩
    have h : ((q.den : ℤ)) • q = q.num • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast, _root_.mul_one]
      exact Rat.den_mul_eq_num q
    rw [TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨n, z, hn, h⟩ := ha
    obtain ⟨m, w, hm, h'⟩ := hb
    refine ⟨n * m, m • z + n • w, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← h, ← h',
      smul_smul, smul_smul, mul_comm m n]

private theorem sep_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) (a : ℚ ⊗[ℤ] Λ) (h : ∀ w, B.baseChange ℚ a w = 0) : a = 0 := by
  obtain ⟨n, z, hn, e⟩ := exists_den a
  have hz : z = 0 := by
    apply hB
    intro w
    have h2 : B.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] z) ((1 : ℚ) ⊗ₜ[ℤ] w) = 0 := by
      rw [← e, map_zsmul, LinearMap.smul_apply, h, smul_zero]
    simpa [LinearMap.BilinForm.baseChange_tmul] using h2
  rw [hz, TensorProduct.tmul_zero] at e
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [← Int.cast_smul_eq_zsmul ℚ] at e
  exact (smul_eq_zero.1 e).resolve_left hn'

private theorem adj_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (f g : Λ →ₗ[ℤ] Λ)
    (h : ∀ x y, B (f x) y = B x (g y)) (u w : ℚ ⊗[ℤ] Λ) :
    B.baseChange ℚ (f.baseChange ℚ u) w = B.baseChange ℚ u (g.baseChange ℚ w) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r y => simp [LinearMap.BilinForm.baseChange_tmul, h]

private theorem anti_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (h : ∀ x, B x x = 0)
    (u w : ℚ ⊗[ℤ] Λ) : B.baseChange ℚ u w = - B.baseChange ℚ w u := by
  have anti : ∀ x y, B x y = - B y x := fun x y => by
    have := h (x + y)
    simp only [map_add, LinearMap.add_apply, h, zero_add, add_zero] at this
    linarith
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
    | tmul r y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [anti x y]
      rw [mul_comm q r, neg_smul]

private theorem exists_rep {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E F : LinearMap.BilinForm ℚ V) (hE : ∀ a, (∀ w, E a w = 0) → a = 0) :
    ∃ b : Module.End ℚ V, ∀ u w, F u w = 2 * E (b u) w := by
  have inj : Function.Injective (E : V →ₗ[ℚ] Module.Dual ℚ V) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact hE a fun w => by rw [ha]; rfl
  let Φ : V ≃ₗ[ℚ] Module.Dual ℚ V :=
    LinearMap.linearEquivOfInjective (E : V →ₗ[ℚ] Module.Dual ℚ V) inj (Subspace.dual_finrank_eq).symm
  refine ⟨(1 / 2 : ℚ) • (Φ.symm.toLinearMap ∘ₗ (F : V →ₗ[ℚ] Module.Dual ℚ V)), fun u w => ?_⟩
  have h : E (Φ.symm (F u)) = F u := Φ.apply_symm_apply (F u)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, h, smul_eq_mul]
  ring

theorem UpperTheory.exists_unitary_unit_hermitian_form_of_cm_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (Y : PLat D.O D.inv) (j : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D), (∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), j ((DistribMulAction.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (j u)) → ∃ β : G.Cˣ, sh G β = β ∧ ∀ u w : ℚ ⊗[ℤ] Y.La, Y.EF.baseChange ℚ u w = 2 * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j u)) (j w) := by
  intro p _ D G L Y j hj
  haveI := D.finLa
  set E := D.EF.baseChange ℚ with hEdef
  have sepE : ∀ a, (∀ w, E a w = 0) → a = 0 := fun a h =>
    sep_bc D.EF (fun x hx => D.nondeg (by rw [map_zero]; ext y; simpa using hx y)) a h
  have sepY : ∀ a, (∀ w, Y.EF.baseChange ℚ a w = 0) → a = 0 := fun a h => sep_bc Y.EF Y.nondeg a h
  have eqE : ∀ a a', (∀ w, E a w = E a' w) → a = a' := fun a a' h => by
    rw [← sub_eq_zero]
    exact sepE _ fun w => by rw [map_sub, LinearMap.sub_apply, h, sub_self]
  let F : LinearMap.BilinForm ℚ (VQ D) :=
    ((Y.EF.baseChange ℚ).compl₁₂ j.symm.toLinearMap j.symm.toLinearMap)
  have hF : ∀ u w, F u w = Y.EF.baseChange ℚ (j.symm u) (j.symm w) := fun u w => rfl
  obtain ⟨b, hb⟩ := exists_rep E F sepE
  have hinj : Function.Injective b := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have : j.symm u = 0 := sepY _ fun w => by
      have h := hb u (j w)
      rw [hu, map_zero, LinearMap.zero_apply, MulZeroClass.mul_zero, hF, j.symm_apply_apply] at h
      exact h
    simpa using this
  have comm : ∀ c : D.O, b * actQ D c = actQ D c * b := by
    intro c
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    have hc : j.symm (actQ D c u) = (DistribMulAction.toLinearMap ℤ Y.La c).baseChange ℚ (j.symm u) := by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have hc' : ∀ w, j.symm (actQ D (D.inv c) w) = (DistribMulAction.toLinearMap ℤ Y.La (D.inv c)).baseChange ℚ (j.symm w) := fun w => by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have h1 : F (actQ D c u) w = F u (actQ D (D.inv c) w) := by
      rw [hF, hF, hc, hc']
      exact adj_bc Y.EF _ _ (fun x y => Y.adj c x y) _ _
    have h2 : E (actQ D c (b u)) w = E (b u) (actQ D (D.inv c) w) :=
      adj_bc D.EF _ _ (fun x y => D.adj c x y) _ _
    have h3 := hb (actQ D c u) w
    have h4 := hb u (actQ D (D.inv c) w)
    simp only [Module.End.mul_apply]
    rw [h2]
    linarith
  have hsym : ∀ u w, E (b u) w = E u (b w) := by
    intro u w
    have h1 := hb u w
    have h2 := hb w u
    have h3 : F u w = - F w u := by
      rw [hF, hF]
      exact anti_bc Y.EF Y.alt _ _
    have h4 : E (b w) u = - E u (b w) := anti_bc D.EF D.alt _ _
    linarith
  obtain ⟨b₀, hb₀⟩ := (L.rep_range b).2 comm
  let e : VQ D ≃ₗ[ℚ] VQ D := LinearEquiv.ofInjectiveEndo b hinj
  have he : ∀ u, b (e.symm u) = u := fun u => e.apply_symm_apply u
  have he' : ∀ u, e.symm (b u) = u := fun u => e.symm_apply_apply u
  have comm' : ∀ c : D.O, (e.symm.toLinearMap : Module.End ℚ (VQ D)) * actQ D c = actQ D c * e.symm.toLinearMap := by
    intro c
    refine LinearMap.ext fun u => hinj ?_
    have h := LinearMap.congr_fun (comm c) (e.symm u)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, he] at h ⊢
    exact h.symm
  obtain ⟨b₁, hb₁⟩ := (L.rep_range _).2 comm'
  have h01 : b₀ * b₁ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he u
  have h10 : b₁ * b₀ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he' u
  have hadj : ∀ x v w, E (L.rep x v) w = E v (L.rep (sh G x) w) := L.adj
  have shsh : sh G (sh G b₀) = b₀ := G.star_star b₀
  have shmul : ∀ x y, sh G (x * y) = sh G y * sh G x := fun x y => by
    unfold sh
    rw [map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by
    unfold sh
    rw [map_one, MulOpposite.unop_one]
  have hs : sh G b₀ = b₀ := by
    apply L.rep_inj
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    rw [hadj, shsh, hb₀, hsym]
  have hs1 : sh G b₁ = b₁ := by
    have h : sh G b₁ * b₀ = 1 := by
      have h' := shmul b₀ b₁
      rw [h01, shone, hs] at h'
      exact h'.symm
    calc sh G b₁ = sh G b₁ * (b₀ * b₁) := by rw [h01, _root_.mul_one]
      _ = (sh G b₁ * b₀) * b₁ := (_root_.mul_assoc _ _ _).symm
      _ = b₁ := by rw [h, _root_.one_mul]
  refine ⟨⟨b₁, b₀, h10, h01⟩, hs1, fun u w => ?_⟩
  have h := hb (j u) (j w)
  rw [hF, j.symm_apply_apply, j.symm_apply_apply] at h
  rw [h]
  show _ = 2 * E (L.rep b₀ (j u)) (j w)
  rw [hb₀]
