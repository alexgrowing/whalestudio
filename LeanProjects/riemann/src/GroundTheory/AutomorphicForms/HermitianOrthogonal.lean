import Mathlib
import GroundTheory.AutomorphicForms.HermitianSpaces

noncomputable section

namespace GroundTheory.Automorphic

open Module

section Conj

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

instance finiteDimensional_of_isQuadraticExtension : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)

theorem conjHom_apply (x : E) : conjHom F E x = conj F E x :=
  rfl

theorem exists_trace_eq_one [Algebra.IsSeparable F E] : ∃ c : E, Algebra.trace F E c = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace F E x ≠ 0 := by
    by_contra H
    push Not at H
    exact Algebra.trace_ne_zero F E (LinearMap.ext H)
  refine ⟨(Algebra.trace F E x)⁻¹ • x, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]

theorem exists_not_mem_range : ∃ ζ : E, ζ ∉ Set.range (algebraMap F E) := by
  by_contra H
  push Not at H
  have hbij : Function.Bijective (Algebra.linearMap F E) :=
    ⟨(algebraMap F E).injective, fun y => H y⟩
  have h1 := (LinearEquiv.ofBijective _ hbij).finrank_eq
  rw [Module.finrank_self, Algebra.IsQuadraticExtension.finrank_eq_two] at h1
  exact absurd h1 (by norm_num)

theorem conj_eq_self_iff [Algebra.IsSeparable F E] {x : E} :
    conj F E x = x ↔ x ∈ Set.range (algebraMap F E) := by
  refine ⟨fun hx => ?_, fun ⟨c, hc⟩ => hc ▸ conj_algebraMap c⟩
  by_contra hne
  rw [conj_apply] at hx
  have h2 : algebraMap F E (Algebra.trace F E x) = 2 * x := by linear_combination hx
  by_cases h2E : (2 : E) = 0
  · have htx : Algebra.trace F E x = 0 := by
      apply (algebraMap F E).injective
      rw [h2, h2E, zero_mul, map_zero]
    have ht1 : Algebra.trace F E 1 = 0 := by
      have := trace_algebraMap_quadratic (F := F) (E := E) 1
      rw [map_one, mul_one] at this
      rw [this]
      apply (algebraMap F E).injective
      rw [map_ofNat, h2E, map_zero]
    apply Algebra.trace_ne_zero F E
    refine (basisOneOf hne).ext fun i => ?_
    fin_cases i
    · simp [basisOneOf_zero, ht1]
    · simp [basisOneOf_one, htx]
  · apply hne
    refine ⟨2⁻¹ * Algebra.trace F E x, ?_⟩
    rw [map_mul, h2, map_inv₀, map_ofNat, ← mul_assoc, inv_mul_cancel₀ h2E, one_mul]

theorem exists_mul_conj_eq_one_ne_one [Algebra.IsSeparable F E] :
    ∃ l : E, l * conj F E l = 1 ∧ l ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := F) (E := E)
  have hζ0 : ζ ≠ 0 := fun h => hζ ⟨0, by rw [h, map_zero]⟩
  have hc : conj F E ζ ≠ ζ := fun h => hζ (conj_eq_self_iff.1 h)
  have hc0 : conj F E ζ ≠ 0 := by
    intro h
    apply hζ0
    rw [← conj_conj (F := F) ζ, h, map_zero]
  refine ⟨conj F E ζ * ζ⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv₀, conj_conj]
    field_simp
  · intro h
    apply hc
    field_simp at h
    exact h

end Conj

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']

namespace HermitianForm

def Isometric (h : HermitianForm F E V) (h' : HermitianForm F E V') : Prop :=
  ∃ e : V ≃ₗ[E] V', ∀ x y, h'.toSesq (e x) (e y) = h.toSesq x y

theorem conj_toSesq (h : HermitianForm F E V) (x y : V) :
    conj F E (h.toSesq x y) = h.toSesq y x :=
  h.isSymm.eq x y

theorem toSesq_smul_left (h : HermitianForm F E V) (c : E) (x y : V) :
    h.toSesq (c • x) y = conj F E c * h.toSesq x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, conjHom_apply]

theorem toSesq_smul_right (h : HermitianForm F E V) (c : E) (x y : V) :
    h.toSesq x (c • y) = c * h.toSesq x y := by
  rw [map_smul, smul_eq_mul]

theorem eq_zero_of_forall (h : HermitianForm F E V) {x : V} (hx : ∀ y, h.toSesq x y = 0) :
    x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx

theorem toSesq_eq_zero_comm (h : HermitianForm F E V) {x y : V} :
    h.toSesq x y = 0 ↔ h.toSesq y x = 0 := by
  rw [← h.conj_toSesq x y]
  constructor
  · intro hxy; rw [hxy, map_zero]
  · intro hxy
    rw [← conj_conj (F := F) (h.toSesq x y), hxy, map_zero]

theorem conj_toSesq_self (h : HermitianForm F E V) (x : V) :
    conj F E (h.toSesq x x) = h.toSesq x x :=
  h.conj_toSesq x x

theorem toSesq_self_mem_range [Algebra.IsSeparable F E] (h : HermitianForm F E V) (x : V) :
    h.toSesq x x ∈ Set.range (algebraMap F E) :=
  conj_eq_self_iff.1 (h.conj_toSesq_self x)

namespace Isometric

theorem refl (h : HermitianForm F E V) : Isometric h h := ⟨LinearEquiv.refl E V, fun _ _ => rfl⟩

theorem symm {h : HermitianForm F E V} {h' : HermitianForm F E V'} (H : Isometric h h') :
    Isometric h' h := by
  obtain ⟨e, he⟩ := H
  refine ⟨e.symm, fun x y => ?_⟩
  rw [← he, e.apply_symm_apply, e.apply_symm_apply]

theorem trans {h : HermitianForm F E V} {h' : HermitianForm F E V'}
    {h'' : HermitianForm F E V''} (H : Isometric h h') (H' : Isometric h' h'') :
    Isometric h h'' := by
  obtain ⟨e, he⟩ := H
  obtain ⟨e', he'⟩ := H'
  exact ⟨e.trans e', fun x y => by
    show h''.toSesq (e' (e x)) (e' (e y)) = _
    rw [he', he]⟩

theorem finrank_eq {h : HermitianForm F E V} {h' : HermitianForm F E V'} (H : Isometric h h') :
    finrank E V = finrank E V' := by
  obtain ⟨e, -⟩ := H
  exact e.finrank_eq

end Isometric

def prod (h : HermitianForm F E V) (h' : HermitianForm F E V') : HermitianForm F E (V × V') where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun p q => h.toSesq p.1 q.1 + h'.toSesq p.2 q.2)
    (fun p p' q => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun c p q => by
      simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.map_smulₛₗ₂, smul_eq_mul]; ring)
    (fun p q q' => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c p q => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]; ring)
  isSymm := ⟨fun p q => by
    simp only [LinearMap.mk₂'ₛₗ_apply, map_add]
    rw [h.isSymm.eq, h'.isSymm.eq]⟩
  nonsingular := by
    constructor
    · intro p q hpq
      have H : ∀ r : V × V', h.toSesq p.1 r.1 + h'.toSesq p.2 r.2 =
          h.toSesq q.1 r.1 + h'.toSesq q.2 r.2 := fun r => LinearMap.congr_fun hpq r
      have h1 : h.toSesq p.1 = h.toSesq q.1 := LinearMap.ext fun y => by
        simpa using H (y, 0)
      have h2 : h'.toSesq p.2 = h'.toSesq q.2 := LinearMap.ext fun y => by
        simpa using H (0, y)
      exact Prod.ext (h.nonsingular.1 h1) (h'.nonsingular.1 h2)
    · intro f
      obtain ⟨x, hx⟩ := h.nonsingular.2 (f.comp (LinearMap.inl E V V'))
      obtain ⟨x', hx'⟩ := h'.nonsingular.2 (f.comp (LinearMap.inr E V V'))
      refine ⟨(x, x'), LinearMap.ext fun r => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, hx, hx', LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

@[simp]
theorem prod_apply (h : HermitianForm F E V) (h' : HermitianForm F E V') (p q : V × V') :
    (h.prod h').toSesq p q = h.toSesq p.1 q.1 + h'.toSesq p.2 q.2 := rfl

theorem Isometric.prod {h₁ : HermitianForm F E V} {h₂ : HermitianForm F E V'}
    {V₃ V₄ : Type*} [AddCommGroup V₃] [Module E V₃] [AddCommGroup V₄] [Module E V₄]
    {h₃ : HermitianForm F E V₃} {h₄ : HermitianForm F E V₄}
    (H : Isometric h₁ h₂) (H' : Isometric h₃ h₄) : Isometric (h₁.prod h₃) (h₂.prod h₄) := by
  obtain ⟨e, he⟩ := H
  obtain ⟨e', he'⟩ := H'
  exact ⟨e.prodCongr e', fun p q => by
    show h₂.toSesq (e p.1) (e q.1) + h₄.toSesq (e' p.2) (e' q.2) = _
    rw [he, he']
    rfl⟩

theorem isometric_prod_comm (h : HermitianForm F E V) (h' : HermitianForm F E V') :
    Isometric (h.prod h') (h'.prod h) :=
  ⟨LinearEquiv.prodComm E V V', fun p q => by
    show h'.toSesq p.2 q.2 + h.toSesq p.1 q.1 = h.toSesq p.1 q.1 + h'.toSesq p.2 q.2
    rw [add_comm]⟩

theorem isometric_prod_assoc (h : HermitianForm F E V) (h' : HermitianForm F E V')
    (h'' : HermitianForm F E V'') :
    Isometric ((h.prod h').prod h'') (h.prod (h'.prod h'')) :=
  ⟨LinearEquiv.prodAssoc E V V' V'', fun p q => by
    show h.toSesq p.1.1 q.1.1 + (h'.toSesq p.1.2 q.1.2 + h''.toSesq p.2 q.2) =
      (h.toSesq p.1.1 q.1.1 + h'.toSesq p.1.2 q.1.2) + h''.toSesq p.2 q.2
    rw [add_assoc]⟩

def ofUnit (a : Fˣ) : HermitianForm F E E where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => conj F E x * algebraMap F E a * y)
    (fun x x' y => by rw [map_add]; ring)
    (fun c x y => by simp only [map_mul, smul_eq_mul, conjHom_apply]; ring)
    (fun x y y' => by ring)
    (fun c x y => by simp only [smul_eq_mul, RingHom.id_apply]; ring)
  isSymm := ⟨fun x y => by
    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_mul, conj_conj, conj_algebraMap]
    ring⟩
  nonsingular := by
    have ha : algebraMap F E a ≠ 0 := by simp
    constructor
    · intro x y hxy
      have := LinearMap.congr_fun hxy 1
      simp only [LinearMap.mk₂'ₛₗ_apply, mul_one] at this
      have h2 := mul_right_cancel₀ ha this
      rw [← conj_conj (F := F) x, h2, conj_conj]
    · intro f
      refine ⟨conj F E (f 1 * (algebraMap F E a)⁻¹), LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, conj_conj]
      have hf : f y = f 1 * y := by
        rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
      rw [hf]
      field_simp

@[simp]
theorem ofUnit_apply (a : Fˣ) (x y : E) :
    (ofUnit (E := E) a).toSesq x y = conj F E x * algebraMap F E a * y := rfl

def IsOrthoCompl (h : HermitianForm F E V) (W W' : Submodule E V) : Prop :=
  IsCompl W W' ∧ ∀ x ∈ W, ∀ y ∈ W', h.toSesq x y = 0

theorem IsOrthoCompl.symm {h : HermitianForm F E V} {W W' : Submodule E V}
    (hW : h.IsOrthoCompl W W') : h.IsOrthoCompl W' W :=
  ⟨hW.1.symm, fun x hx y hy => h.toSesq_eq_zero_comm.1 (hW.2 y hy x hx)⟩

def restrict (h : HermitianForm F E V) (W W' : Submodule E V) (hW : h.IsOrthoCompl W W') :
    HermitianForm F E W where
  toSesq := h.toSesq.domRestrict₁₂ W W
  isSymm := h.isSymm.domRestrict W
  nonsingular := by
    constructor
    · intro a b hab
      have key : ∀ v : V, h.toSesq (a : V) v = h.toSesq (b : V) v := by
        intro v
        have hv : v ∈ W ⊔ W' := by rw [hW.1.sup_eq_top]; trivial
        obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
        have h1 := LinearMap.congr_fun hab ⟨w, hw⟩
        simp only [LinearMap.domRestrict₁₂_apply] at h1
        rw [map_add, map_add, h1, hW.2 _ a.2 _ hw', hW.2 _ b.2 _ hw']
      exact Subtype.ext (h.nonsingular.1 (LinearMap.ext key))
    · intro f
      obtain ⟨x, hx⟩ := h.nonsingular.2 (f.comp (Submodule.projectionOnto W W' hW.1))
      have hv : x ∈ W ⊔ W' := by rw [hW.1.sup_eq_top]; trivial
      obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
      refine ⟨⟨w, hw⟩, LinearMap.ext fun y => ?_⟩
      have h1 := LinearMap.congr_fun hx (y : V)
      rw [map_add, LinearMap.add_apply, h.toSesq_eq_zero_comm.1 (hW.2 _ y.2 _ hw'), add_zero,
        LinearMap.comp_apply, Submodule.projectionOnto_apply_left] at h1
      exact h1

@[simp]
theorem restrict_apply (h : HermitianForm F E V) (W W' : Submodule E V)
    (hW : h.IsOrthoCompl W W') (x y : W) :
    (h.restrict W W' hW).toSesq x y = h.toSesq x y := rfl

theorem isometric_prod_restrict (h : HermitianForm F E V) (W W' : Submodule E V)
    (hW : h.IsOrthoCompl W W') :
    Isometric ((h.restrict W W' hW).prod (h.restrict W' W hW.symm)) h := by
  refine ⟨Submodule.prodEquivOfIsCompl W W' hW.1, fun p q => ?_⟩
  simp only [Submodule.coe_prodEquivOfIsCompl', prod_apply, restrict_apply, map_add,
    LinearMap.add_apply]
  rw [hW.2 _ p.1.2 _ q.2.2, h.toSesq_eq_zero_comm.1 (hW.2 _ q.1.2 _ p.2.2)]
  ring

theorem isOrthoCompl_span_singleton (h : HermitianForm F E V) {v : V}
    (hv : h.toSesq v v ≠ 0) :
    h.IsOrthoCompl (Submodule.span E {v}) (LinearMap.ker (h.toSesq v)) := by
  refine ⟨?_, ?_⟩
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor
    · rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx1
      have : t * h.toSesq v v = 0 := by
        simpa [LinearMap.mem_ker, h.toSesq_smul_right] using hx2
      rcases mul_eq_zero.1 this with ht | ht
      · simp [ht]
      · exact absurd ht hv
    · rw [eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      refine ⟨(h.toSesq v x * (h.toSesq v v)⁻¹) • v, Submodule.mem_span_singleton.2 ⟨_, rfl⟩,
        x - (h.toSesq v x * (h.toSesq v v)⁻¹) • v, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, h.toSesq_smul_right]
      field_simp
      ring
  · intro x hx y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.mem_ker] at hy
    rw [h.toSesq_smul_left, hy, mul_zero]

section Separable

variable [Algebra.IsSeparable F E]

theorem exists_apply_self_ne_zero (h : HermitianForm F E V) [Nontrivial V] :
    ∃ x, h.toSesq x x ≠ 0 := by
  by_contra H
  push Not at H
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ : ∃ y, h.toSesq x y ≠ 0 := by
    by_contra H'
    push Not at H'
    exact hx (h.eq_zero_of_forall H')
  obtain ⟨c, hc⟩ := exists_trace_eq_one (F := F) (E := E)
  set t := c * (h.toSesq x y)⁻¹ with ht_def
  have ht : t * h.toSesq x y = c := by rw [ht_def]; field_simp
  have key : h.toSesq (x + t • y) (x + t • y) =
      t * h.toSesq x y + conj F E (t * h.toSesq x y) := by
    rw [map_mul, h.conj_toSesq]
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, H]
    ring
  rw [H, ht, add_conj, hc, map_one] at key
  exact one_ne_zero key.symm

end Separable

end HermitianForm

end GroundTheory.Automorphic

end
