import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate

open scoped Matrix

namespace GlobalTheory.LocalQuad.TraceIsometry

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}

theorem finiteDimensional_of_involution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) : FiniteDimensional F E := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : E, ∀ x : E, ∃ s t : F, x = s • (1 : E) + t • δ := by
    by_cases h : ∀ t, c t = t
    · refine ⟨0, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF x).1 (h x)
      exact ⟨s, 0, by simp [Algebra.smul_def, hs]⟩
    · push Not at h
      obtain ⟨u, hu⟩ := h
      have hne : u - c u ≠ 0 := sub_ne_zero.2 hu.symm
      have hne' : c u - u ≠ 0 := sub_ne_zero.2 hu
      refine ⟨u - c u, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF ((x + c x) / 2)).1 (by
        rw [map_div₀, map_add, hc, map_ofNat, add_comm])
      obtain ⟨t, ht⟩ := (hF ((x - c x) / (2 * (u - c u)))).1 (by
        rw [map_div₀, map_sub, hc, map_mul, map_ofNat, map_sub, hc]
        field_simp
        ring)
      refine ⟨s, t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, hs, ht]
      field_simp
      ring
  refine Module.finite_def.2 ⟨{1, δ}, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, t, rfl⟩ := hδ x
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem exists_traceForm (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x) :
    ∃ b : V →ₗ[F] V →ₗ[F] F, ∀ x y, algebraMap F E (b x y) = B x y + B y x := by
  have h : ∀ x y, ∃ s : F, algebraMap F E s = B x y + B y x := fun x y =>
    (hF _).1 (by rw [map_add, hB, hB, add_comm])
  choose b hb using h
  have hi := (algebraMap F E).injective
  have hs : ∀ s : F, c (algebraMap F E s) = algebraMap F E s := fun s => (hF _).2 ⟨s, rfl⟩
  refine ⟨LinearMap.mk₂ F b (fun x x' y => hi ?_) (fun s x y => hi ?_) (fun x y y' => hi ?_)
    (fun s x y => hi ?_), hb⟩
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s x]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s y]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring

theorem trace_eq_of_apply_self_eq {V W : Type*} [AddCommGroup V] [Module E V] [AddCommGroup W]
    [Module E W] {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} {φ : V → W}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hφ : ∀ x, B' (φ x) (φ x) = B x x) (x y : V) :
    B' (φ x) (φ y) + B' (φ y) (φ x) = B x y + B y x := by
  have h := hφ (x + y)
  rw [hadd] at h
  simp only [map_add, LinearMap.add_apply, hφ] at h
  linear_combination h

theorem exists_map_smul_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V W : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
    {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} (hB' : ∀ x y, c (B' x y) = B' y x)
    (φ : V →ₗ[F] W) (hφ : ∀ x, B' (φ x) (φ x) = B x x) {e : V} (he : B e e ≠ 0) :
    ∃ φ' : V →ₗ[F] W, (∀ x, B' (φ' x) (φ' x) = B x x) ∧ ∀ t : E, φ' (t • e) = t • φ e := by
  have := finiteDimensional_of_involution h2 hc hF
  obtain ⟨b, hb⟩ := exists_traceForm hF hB'
  have hi := (algebraMap F E).injective
  have h2F : (2 : F) ≠ 0 := fun h => h2 (by
    rw [← map_ofNat (algebraMap F E) 2, h, map_zero])
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  obtain ⟨γ, hγ, hγe⟩ := GlobalTheory.HermWitt.exists_isometry_comp_eq_of_nondegenerate
    (c := RingHom.id F) h2F (B := b)
    (fun x y => hi (by rw [RingHom.id_apply, hb, hb, add_comm]))
    (g := φ ∘ₗ (LinearMap.toSpanSingleton E V e).restrictScalars F)
    (f := (LinearMap.toSpanSingleton E W (φ e)).restrictScalars F)
    (fun s t => hi (by
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hp, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hφ]))
    (fun s hs => by
      have h := congrArg (algebraMap F E) (hs s)
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hφ, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        map_zero, smul_eq_mul, RingHom.id_apply] at h
      by_contra hne
      exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) (mul_ne_zero hne he))
        (by linear_combination h))
  refine ⟨γ.toLinearMap ∘ₗ φ, fun x => ?_, fun t => hγe t⟩
  have h := congrArg (algebraMap F E) (hγ (φ x) (φ x))
  rw [hb, hb, hφ] at h
  apply mul_left_cancel₀ h2
  change 2 * B' (γ (φ x)) (γ (φ x)) = _
  linear_combination h

universe u v in

theorem exists_linearMap_isometry (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) (d : ℕ) :
    ∀ {V : Type u} {W : Type v} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
      [FiniteDimensional E V] [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
      (B : V →ₗ[E] V →ₛₗ[c] E) (B' : W →ₗ[E] W →ₛₗ[c] E),
      (∀ x y, c (B x y) = B y x) → (∀ x y, c (B' x y) = B' y x) → finrank E V = d →
      ∀ φ : V →ₗ[F] W, (∀ x, B' (φ x) (φ x) = B x x) →
      ∃ ψ : V →ₗ[E] W, ∀ x y, B' (ψ x) (ψ y) = B x y := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V W _ _ _ _ _ _ _ _ _ B B' hB hB' hd φ₀ hφ₀
  obtain rfl | hne := eq_or_ne B 0
  · exact ⟨0, fun x y => by simp⟩
  obtain ⟨e, he⟩ := GlobalTheory.HermDiag.exists_apply_self_ne_zero h2 hB hne
  have hk := GlobalTheory.HermDiag.finrank_ker_flip_add_one he
  obtain ⟨φ, hφ, hφe⟩ := exists_map_smul_eq h2 hc hF hB' φ₀ hφ₀ he
  have hf : B' (φ₀ e) (φ₀ e) = B e e := hφ₀ e
  generalize φ₀ e = f at hφe hf
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  have hker : ∀ x : LinearMap.ker (B.flip e), φ x ∈ LinearMap.ker (B'.flip f) := by
    intro x
    have hx : B x e = 0 := x.2
    have hx' : B e x = 0 := by rw [← hB, hx, map_zero]
    have h := hp x (B' (φ x) f • e)
    rw [hφe] at h
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, hx', smul_eq_mul,
      RingHom.id_apply, ← hB' (φ x) f] at h
    change B' (φ x) f = 0
    by_contra hne
    exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) hne) (by linear_combination h)
  obtain ⟨ψ, hψ⟩ := ih _ (by omega)
    (B.domRestrict₁₂ (LinearMap.ker (B.flip e)) (LinearMap.ker (B.flip e)))
    (B'.domRestrict₁₂ (LinearMap.ker (B'.flip f)) (LinearMap.ker (B'.flip f)))
    (fun y z => hB y z) (fun y z => hB' y z) rfl
    { toFun := fun x => ⟨φ x, hker x⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun s x => Subtype.ext (by simp) }
    (fun x => hφ x)
  replace hψ : ∀ x y : LinearMap.ker (B.flip e), B' (ψ x) (ψ y) = B x y := hψ
  let p : V →ₗ[E] LinearMap.ker (B.flip e) :=
    (LinearMap.id - ((B e e)⁻¹ • B.flip e).smulRight e).codRestrict _ (fun x => by
      have h : (B e e)⁻¹ * B x e * B e e = B x e := by field_simp
      simp [h])
  have hpx : ∀ x, (p x : V) = x - ((B e e)⁻¹ * B x e) • e := fun x => rfl
  refine ⟨(LinearMap.ker (B'.flip f)).subtype ∘ₗ ψ ∘ₗ p + ((B e e)⁻¹ • B.flip e).smulRight f,
    fun x y => ?_⟩
  have h1 : ∀ z, B' (ψ z) f = 0 := fun z => (ψ z).2
  have h3 : ∀ z, B' f (ψ z) = 0 := fun z => by rw [← hB', h1, map_zero]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.flip_apply, map_add,
    LinearMap.map_smulₛₗ, h1, h3, hψ, hpx, hf, map_sub, LinearMap.sub_apply, smul_eq_mul,
    RingHom.id_apply, map_mul, map_inv₀, hB]
  field_simp
  ring

end GlobalTheory.LocalQuad.TraceIsometry

theorem GlobalTheory.LocalQuad.exists_congr_iff_trace_forms_isometric {F E : Type*} [Field F] [Field E]
    [Algebra F E] (h2 : (2 : E) ≠ 0) (c : E →+* E) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {n : Type*} [Fintype n] [DecidableEq n] {G G' : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (hG' : ∀ a b, c (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
      ∃ φ : (n → E) ≃ₗ[F] (n → E),
        ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨(Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP.isUnit)).restrictScalars F,
      fun x => ?_⟩
    rw [GlobalTheory.HermWitt.dotProduct_congr_mulVec]
    rfl
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := TraceIsometry.exists_linearMap_isometry h2 hc hF _
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G')
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG'])
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG])
      rfl φ.toLinearMap
      (fun x => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct]
        exact (hφ x).symm)
    have h : G' = (LinearMap.toMatrix' ψ)ᵀ * G * (LinearMap.toMatrix' ψ).map c := by
      apply (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c).injective
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      rw [← hψ, GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
        GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct, GlobalTheory.HermWitt.dotProduct_congr_mulVec,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    refine ⟨_, fun h0 => hd' ?_, h⟩
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
