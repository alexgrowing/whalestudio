import Mathlib
import GroundTheory.AutomorphicForms.HermitianOrthogonal

noncomputable section

namespace GroundTheory.Automorphic

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]

theorem bijective_of_injective_sesq [FiniteDimensional E V]
    (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (hB : Function.Injective B) : Function.Bijective B := by
  set b := Module.finBasis E V
  set G := gram B b
  let sx : (Fin (finrank E V) → E) → V := fun c => b.equivFun.symm (fun i => conj F E (c i))
  have key : ∀ c j, B (sx c) (b j) = Matrix.vecMul c G j := by
    intro c j
    simp only [sx, Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ₂, conjHom_apply,
      conj_conj, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.vecMul,
      dotProduct, G, gram_apply]
  have hinj : Function.Injective (Matrix.vecMulLinear G) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : B (sx c) = 0 := b.ext fun j => by
      rw [key, LinearMap.zero_apply]
      exact congrFun hc j
    have h2 : sx c = 0 := hB (by rw [h1, map_zero])
    funext i
    have h3 := congrArg (fun v => b.equivFun v i) h2
    simp only [sx, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] at h3
    rw [← conj_conj (F := F) (c i), h3, map_zero, Pi.zero_apply]
  refine ⟨hB, fun f => ?_⟩
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.1 hinj (fun j => f (b j))
  refine ⟨sx c, b.ext fun j => ?_⟩
  rw [key]
  exact congrFun hc j

namespace HermitianForm

theorem toSesq_self_ne_zero_of_eq (h : HermitianForm F E V) {v : V} {a : Fˣ}
    (hv : h.toSesq v v = algebraMap F E a) : h.toSesq v v ≠ 0 := by
  rw [hv]; simp

theorem exists_isometric_prod_ofUnit (h : HermitianForm F E V) {v : V} {a : Fˣ}
    (hv : h.toSesq v v = algebraMap F E a) :
    ∃ (W : Submodule E V) (h₀ : HermitianForm F E W),
      Isometric ((ofUnit (E := E) a).prod h₀) h ∧
        (FiniteDimensional E V → finrank E W + 1 = finrank E V) := by
  have hv0 := h.toSesq_self_ne_zero_of_eq hv
  have hne : v ≠ 0 := by rintro rfl; simp at hv0
  have hW := h.isOrthoCompl_span_singleton hv0
  set L := Submodule.span E {v}
  set K := LinearMap.ker (h.toSesq v)
  have iso1 : Isometric (ofUnit (E := E) a) (h.restrict L K hW) := by
    refine ⟨LinearEquiv.toSpanNonzeroSingleton E V v hne, fun x y => ?_⟩
    show h.toSesq (x • v) (y • v) = conj F E x * algebraMap F E a * y
    rw [h.toSesq_smul_left, h.toSesq_smul_right, hv]
    ring
  refine ⟨K, h.restrict K L hW.symm, (iso1.prod (Isometric.refl _)).trans
    (h.isometric_prod_restrict L K hW), fun hfin => ?_⟩
  have := ((iso1.prod (Isometric.refl (h.restrict K L hW.symm))).trans
    (h.isometric_prod_restrict L K hW)).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega

def quasiReflection (h : HermitianForm F E V) (w : V) (c : E) : V →ₗ[E] V :=
  LinearMap.id - (c • h.toSesq w).smulRight w

theorem quasiReflection_apply (h : HermitianForm F E V) (w : V) (c : E) (z : V) :
    h.quasiReflection w c z = z - (c * h.toSesq w z) • w := by
  simp [quasiReflection]

theorem toSesq_quasiReflection (h : HermitianForm F E V) {w : V} {c : E}
    (hc : c + conj F E c = c * conj F E c * h.toSesq w w) (z z' : V) :
    h.toSesq (h.quasiReflection w c z) (h.quasiReflection w c z') = h.toSesq z z' := by
  simp only [quasiReflection_apply, map_sub, LinearMap.sub_apply, h.toSesq_smul_left,
    h.toSesq_smul_right, map_mul, h.conj_toSesq]
  linear_combination (-(h.toSesq z w * h.toSesq w z')) * hc

def equivOfIsometry [FiniteDimensional E V] (h : HermitianForm F E V) (f : V →ₗ[E] V)
    (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) : V ≃ₗ[E] V :=
  LinearEquiv.ofInjectiveEndo f (by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply h.eq_zero_of_forall
    intro y
    rw [← hf, hx, map_zero, LinearMap.zero_apply])

@[simp]
theorem equivOfIsometry_apply [FiniteDimensional E V] (h : HermitianForm F E V) (f : V →ₗ[E] V)
    (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) (x : V) :
    h.equivOfIsometry f hf x = f x := rfl

theorem exists_isometry_apply_eq_of_ne [FiniteDimensional E V] (h : HermitianForm F E V)
    {x y : V} (hxy : h.toSesq x x = h.toSesq y y) (hd : h.toSesq x x - h.toSesq y x ≠ 0) :
    ∃ g : V ≃ₗ[E] V, (∀ z z', h.toSesq (g z) (g z') = h.toSesq z z') ∧ g x = y := by
  set d := h.toSesq x x - h.toSesq y x with hd_def
  have hcd : conj F E d = h.toSesq x x - h.toSesq x y := by
    rw [hd_def, map_sub, h.conj_toSesq_self, h.conj_toSesq]
  have hcd0 : conj F E d ≠ 0 := by
    intro h0; apply hd; rw [← conj_conj (F := F) d, h0, map_zero]
  have hww : d + conj F E d = h.toSesq (x - y) (x - y) := by
    rw [hcd, hd_def]
    simp only [map_sub, LinearMap.sub_apply]
    rw [← hxy]
    ring
  have hc : d⁻¹ + conj F E d⁻¹ = d⁻¹ * conj F E d⁻¹ * h.toSesq (x - y) (x - y) := by
    rw [map_inv₀, ← hww]
    field_simp
    ring
  refine ⟨h.equivOfIsometry _ (h.toSesq_quasiReflection hc), h.toSesq_quasiReflection hc, ?_⟩
  rw [equivOfIsometry_apply, quasiReflection_apply]
  have : h.toSesq (x - y) x = d := by rw [map_sub, LinearMap.sub_apply]
  rw [this, inv_mul_cancel₀ hd, one_smul]
  abel

theorem exists_isometry_apply_eq [Algebra.IsSeparable F E] [FiniteDimensional E V]
    (h : HermitianForm F E V) {x y : V} (hxy : h.toSesq x x = h.toSesq y y)
    (hx : h.toSesq x x ≠ 0) :
    ∃ g : V ≃ₗ[E] V, (∀ z z', h.toSesq (g z) (g z') = h.toSesq z z') ∧ g x = y := by
  by_cases hd : h.toSesq x x - h.toSesq y x ≠ 0
  · exact h.exists_isometry_apply_eq_of_ne hxy hd
  push Not at hd
  obtain ⟨l, hl, hl1⟩ := exists_mul_conj_eq_one_ne_one (F := F) (E := E)
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl
  have hcl : conj F E l ≠ 1 := by
    intro h1; apply hl1; rw [← conj_conj (F := F) l, h1, map_one]
  have hxy' : h.toSesq x x = h.toSesq (l • y) (l • y) := by
    rw [h.toSesq_smul_left, h.toSesq_smul_right, ← hxy, ← mul_assoc, mul_comm (conj F E l), hl,
      one_mul]
  have hd' : h.toSesq x x - h.toSesq (l • y) x ≠ 0 := by
    rw [h.toSesq_smul_left, ← sub_eq_zero.1 hd]
    have : h.toSesq x x - conj F E l * h.toSesq x x = (1 - conj F E l) * h.toSesq x x := by ring
    rw [this]
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hcl)) hx
  obtain ⟨g, hg, hgx⟩ := h.exists_isometry_apply_eq_of_ne hxy' hd'
  refine ⟨g.trans (LinearEquiv.smulOfNeZero E V l⁻¹ (inv_ne_zero hl0)), fun z z' => ?_, ?_⟩
  · simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, h.toSesq_smul_left,
      h.toSesq_smul_right, hg, map_inv₀]
    rw [← mul_assoc, ← mul_inv, mul_comm (conj F E l), hl, inv_one, one_mul]
  · simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, hgx, smul_smul,
      inv_mul_cancel₀ hl0, one_smul]

theorem isometric_of_prod_ofUnit [Algebra.IsSeparable F E] [FiniteDimensional E V₂]
    (h₁ : HermitianForm F E V₁) (h₂ : HermitianForm F E V₂) (a : Fˣ)
    (H : Isometric (h₁.prod (ofUnit (E := E) a)) (h₂.prod (ofUnit (E := E) a))) :
    Isometric h₁ h₂ := by
  obtain ⟨φ, hφ⟩ := H
  set hT := h₂.prod (ofUnit (E := E) a)
  set hS := h₁.prod (ofUnit (E := E) a)
  have hTe : ∀ (p : V₂) (t : E), hT.toSesq (0, 1) (p, t) = algebraMap F E a * t := by
    intro p t
    rw [prod_apply, ofUnit_apply, map_zero, LinearMap.zero_apply, map_one, zero_add, one_mul]
  have hSe : ∀ (p : V₁) (t : E), hS.toSesq (0, 1) (p, t) = algebraMap F E a * t := by
    intro p t
    rw [prod_apply, ofUnit_apply, map_zero, LinearMap.zero_apply, map_one, zero_add, one_mul]
  have ha : algebraMap F E (a : F) ≠ 0 := by simp
  have hu : hT.toSesq (φ (0, 1)) (φ (0, 1)) = hT.toSesq (0, 1) (0, 1) := by
    rw [hφ, hSe, hTe]
  have hu0 : hT.toSesq (φ (0, 1)) (φ (0, 1)) ≠ 0 := by rw [hu, hTe, mul_one]; exact ha
  obtain ⟨τ, hτ, hτu⟩ := hT.exists_isometry_apply_eq hu hu0
  set ψ := φ.trans τ with hψ_def
  have hψ : ∀ z z', hT.toSesq (ψ z) (ψ z') = hS.toSesq z z' := by
    intro z z'; simp only [hψ_def, LinearEquiv.trans_apply, hτ, hφ]
  have hψ1 : ψ (0, 1) = (0, 1) := by simp only [hψ_def, LinearEquiv.trans_apply, hτu]
  have hA : ∀ x : V₁, (ψ (x, 0)).2 = 0 := by
    intro x
    have h1 := hψ (0, 1) (x, 0)
    rw [hψ1, hSe, mul_zero] at h1
    have h2 : algebraMap F E a * (ψ (x, 0)).2 = 0 := by
      rw [← hTe (ψ (x, 0)).1 (ψ (x, 0)).2]; exact h1
    exact (mul_eq_zero.1 h2).resolve_left ha
  have hB : ∀ y : V₂, (ψ.symm (y, 0)).2 = 0 := by
    intro y
    have h1 := hψ (0, 1) (ψ.symm (y, 0))
    rw [hψ1, LinearEquiv.apply_symm_apply, hTe, mul_zero] at h1
    have h2 : algebraMap F E a * (ψ.symm (y, 0)).2 = 0 := by
      rw [← hSe (ψ.symm (y, 0)).1 (ψ.symm (y, 0)).2]; exact h1.symm
    exact (mul_eq_zero.1 h2).resolve_left ha
  have hA' : ∀ x : V₁, ψ (x, 0) = ((ψ (x, 0)).1, 0) := fun x => Prod.ext rfl (hA x)
  have hB' : ∀ y : V₂, ψ.symm (y, 0) = ((ψ.symm (y, 0)).1, 0) := fun y => Prod.ext rfl (hB y)
  let f : V₁ →ₗ[E] V₂ := LinearMap.fst E V₂ E ∘ₗ (ψ : V₁ × E →ₗ[E] V₂ × E) ∘ₗ LinearMap.inl E V₁ E
  let g : V₂ →ₗ[E] V₁ :=
    LinearMap.fst E V₁ E ∘ₗ (ψ.symm : V₂ × E →ₗ[E] V₁ × E) ∘ₗ LinearMap.inl E V₂ E
  have hfg : ∀ y, f (g y) = y := by
    intro y
    simp only [f, g, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
      LinearEquiv.coe_coe]
    rw [← hB', LinearEquiv.apply_symm_apply]
  have hgf : ∀ x, g (f x) = x := by
    intro x
    simp only [f, g, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
      LinearEquiv.coe_coe]
    rw [← hA', LinearEquiv.symm_apply_apply]
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf), fun x y => ?_⟩
  simp only [LinearEquiv.ofLinear_apply, f, LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.fst_apply, LinearEquiv.coe_coe]
  have h1 := hψ (x, 0) (y, 0)
  rw [hA' x, hA' y, prod_apply, prod_apply] at h1
  have z1 : (ofUnit (E := E) a).toSesq (0 : E) 0 = 0 := by
    rw [ofUnit_apply, map_zero, zero_mul, zero_mul]
  change h₂.toSesq _ _ + (ofUnit (E := E) a).toSesq 0 0 =
    h₁.toSesq x y + (ofUnit (E := E) a).toSesq 0 0 at h1
  rw [z1, add_zero, add_zero] at h1
  exact h1

theorem isometric_of_prod_isometric_prod [Algebra.IsSeparable F E] [FiniteDimensional E V₂]
    [FiniteDimensional E V] (h₁ : HermitianForm F E V₁) (h₂ : HermitianForm F E V₂)
    (h : HermitianForm F E V) (H : Isometric (h₁.prod h) (h₂.prod h)) : Isometric h₁ h₂ := by
  suffices key : ∀ n : ℕ, ∀ (U : Type _) [AddCommGroup U] [Module E U] [FiniteDimensional E U],
      finrank E U = n → ∀ k : HermitianForm F E U, Isometric (h₁.prod k) (h₂.prod k) →
        Isometric h₁ h₂ from key _ V rfl h H
  intro n
  induction n with
  | zero =>
    intro U _ _ _ hU k Hk
    have : Subsingleton U := Module.finrank_zero_iff.1 hU
    letI : Unique U := uniqueOfSubsingleton 0
    have e1 : Isometric (h₁.prod k) h₁ := ⟨LinearEquiv.prodUnique, fun p q => by
      rw [prod_apply, Subsingleton.elim p.2 0, map_zero, LinearMap.zero_apply, add_zero]; rfl⟩
    have e2 : Isometric (h₂.prod k) h₂ := ⟨LinearEquiv.prodUnique, fun p q => by
      rw [prod_apply, Subsingleton.elim p.2 0, map_zero, LinearMap.zero_apply, add_zero]; rfl⟩
    exact (e1.symm.trans Hk).trans e2
  | succ n ih =>
    intro U _ _ _ hU k Hk
    have : Nontrivial U := Module.nontrivial_of_finrank_eq_succ hU
    obtain ⟨v, hv⟩ := k.exists_apply_self_ne_zero
    obtain ⟨c, hc⟩ := k.toSesq_self_mem_range v
    have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact hv hc.symm
    obtain ⟨W, k₀, hk, hW⟩ := k.exists_isometric_prod_ofUnit (a := Units.mk0 c hc0) hc.symm
    have hWn : finrank E W = n := by have := hW inferInstance; omega
    have step1 : Isometric (h₁.prod k) ((h₁.prod k₀).prod (ofUnit (E := E) (Units.mk0 c hc0))) :=
      ((Isometric.refl h₁).prod (hk.symm.trans (isometric_prod_comm _ _))).trans
        (isometric_prod_assoc _ _ _).symm
    have step2 : Isometric (h₂.prod k) ((h₂.prod k₀).prod (ofUnit (E := E) (Units.mk0 c hc0))) :=
      ((Isometric.refl h₂).prod (hk.symm.trans (isometric_prod_comm _ _))).trans
        (isometric_prod_assoc _ _ _).symm
    have H2 := isometric_of_prod_ofUnit _ _ _ ((step1.symm.trans Hk).trans step2)
    exact ih W hWn k₀ H2

def orthogonal (h : HermitianForm F E V) (U : Submodule E V) : Submodule E V where
  carrier := {y | ∀ x ∈ U, h.toSesq x y = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := map_zero _
  smul_mem' c y hy x hx := by rw [h.toSesq_smul_right, hy x hx, mul_zero]

theorem mem_orthogonal (h : HermitianForm F E V) (U : Submodule E V) (y : V) :
    y ∈ h.orthogonal U ↔ ∀ x ∈ U, h.toSesq x y = 0 := Iff.rfl

theorem isOrthoCompl_orthogonal [FiniteDimensional E V] (h : HermitianForm F E V)
    (U : Submodule E V) (hU : ∀ u ∈ U, (∀ u' ∈ U, h.toSesq u u' = 0) → u = 0) :
    h.IsOrthoCompl U (h.orthogonal U) := by
  have hinj : Function.Injective (h.toSesq.domRestrict₁₂ U U) := by
    intro a b hab
    have hab' : a - b = 0 := by
      apply Subtype.ext
      apply hU _ (a - b).2
      intro u' hu'
      have h1 := LinearMap.congr_fun hab ⟨u', hu'⟩
      simp only [LinearMap.domRestrict₁₂_apply] at h1
      rw [Submodule.coe_sub, map_sub, LinearMap.sub_apply, h1, sub_self]
    exact sub_eq_zero.1 hab'
  have hbij := bijective_of_injective_sesq _ hinj
  refine ⟨?_, fun x hx y hy => hy x hx⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (Submodule.mem_bot E).2
      (hU x hx1 fun u' hu' => h.toSesq_eq_zero_comm.1 (hx2 u' hu'))
  · rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu⟩ := hbij.2 ((h.toSesq v).domRestrict U)
    rw [Submodule.mem_sup]
    refine ⟨u, u.2, v - u, fun x hx => ?_, by abel⟩
    have h1 := LinearMap.congr_fun hu ⟨x, hx⟩
    simp only [LinearMap.domRestrict₁₂_apply, LinearMap.domRestrict_apply] at h1
    rw [h.toSesq_eq_zero_comm, map_sub, LinearMap.sub_apply, h1, sub_self]

theorem toSesq_prodEquivOfIsCompl (h : HermitianForm F E V) {W W' : Submodule E V}
    (hW : h.IsOrthoCompl W W') (p q : W × W') :
    h.toSesq (Submodule.prodEquivOfIsCompl W W' hW.1 p)
      (Submodule.prodEquivOfIsCompl W W' hW.1 q) =
      h.toSesq p.1 q.1 + h.toSesq p.2 q.2 := by
  rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add, map_add,
    LinearMap.add_apply, LinearMap.add_apply, hW.2 _ p.1.2 _ q.2.2,
    h.toSesq_eq_zero_comm.1 (hW.2 _ q.1.2 _ p.2.2)]
  ring

theorem exists_extend_of_isOrthoCompl [Algebra.IsSeparable F E] [FiniteDimensional E V]
    (h : HermitianForm F E V) {U₁ U₁' U₂ U₂' : Submodule E V} (h1 : h.IsOrthoCompl U₁ U₁')
    (h2 : h.IsOrthoCompl U₂ U₂') (φ : U₁ ≃ₗ[E] U₂)
    (hφ : ∀ x y : U₁, h.toSesq (φ x) (φ y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U₁, g x = φ x := by
  have I1 := h.isometric_prod_restrict U₁ U₁' h1
  have I2 := h.isometric_prod_restrict U₂ U₂' h2
  have Iφ : Isometric (h.restrict U₁ U₁' h1) (h.restrict U₂ U₂' h2) := ⟨φ, hφ⟩
  have I3 : Isometric ((h.restrict U₁' U₁ h1.symm).prod (h.restrict U₂ U₂' h2))
      ((h.restrict U₂' U₂ h2.symm).prod (h.restrict U₂ U₂' h2)) :=
    (((Isometric.refl _).prod Iφ.symm).trans (isometric_prod_comm _ _)).trans
      (I1.trans (I2.symm.trans (isometric_prod_comm _ _)))
  obtain ⟨ψ, hψ⟩ := isometric_of_prod_isometric_prod _ _ _ I3
  have hψ' : ∀ a b : U₁', h.toSesq (ψ a : V) (ψ b) = h.toSesq a b := fun a b => hψ a b
  set e₁ := Submodule.prodEquivOfIsCompl U₁ U₁' h1.1
  set e₂ := Submodule.prodEquivOfIsCompl U₂ U₂' h2.1
  refine ⟨(e₁.symm.trans (φ.prodCongr ψ)).trans e₂, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨p, rfl⟩ := e₁.surjective x
    obtain ⟨q, rfl⟩ := e₁.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply]
    rw [toSesq_prodEquivOfIsCompl h h2, toSesq_prodEquivOfIsCompl h h1, hφ, hψ']
  · simp only [LinearEquiv.trans_apply, e₁, e₂, Submodule.prodEquivOfIsCompl_symm_apply_left,
      LinearEquiv.prodCongr_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_zero, add_zero]

theorem exists_extend_of_nondegenerate [Algebra.IsSeparable F E] [FiniteDimensional E V]
    (h : HermitianForm F E V) {U₁ U₂ : Submodule E V}
    (hU : ∀ u ∈ U₁, (∀ u' ∈ U₁, h.toSesq u u' = 0) → u = 0) (φ : U₁ ≃ₗ[E] U₂)
    (hφ : ∀ x y : U₁, h.toSesq (φ x) (φ y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U₁, g x = φ x := by
  have hU₂ : ∀ u ∈ U₂, (∀ u' ∈ U₂, h.toSesq u u' = 0) → u = 0 := by
    intro u hu H
    have h1 : ((φ.symm ⟨u, hu⟩ : U₁) : V) = 0 := by
      apply hU _ (φ.symm ⟨u, hu⟩).2
      intro u' hu'
      rw [← hφ (φ.symm ⟨u, hu⟩) ⟨u', hu'⟩, LinearEquiv.apply_symm_apply]
      exact H _ (φ ⟨u', hu'⟩).2
    have h2 : φ.symm ⟨u, hu⟩ = 0 := Subtype.ext h1
    have h3 : (⟨u, hu⟩ : U₂) = 0 := by rw [← φ.apply_symm_apply ⟨u, hu⟩, h2, map_zero]
    exact congrArg Subtype.val h3
  exact h.exists_extend_of_isOrthoCompl (h.isOrthoCompl_orthogonal U₁ hU)
    (h.isOrthoCompl_orthogonal U₂ hU₂) φ hφ

end HermitianForm

end GroundTheory.Automorphic

end
