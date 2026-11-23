import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open UpperTheory.Gal.LocalSmoothExtension
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Ring

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

private theorem sim_triv (σ : S →+* Sᵐᵒᵖ) (b b' : S) (x x' Y : Sˣ) (t t' T : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b' * (σ x').unop = algebraMap A S t')
    (hb : b' = algebraMap A S T * ((Y : S) * b * (σ Y).unop)) :
    ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop =
      algebraMap A S ((t' * T⁻¹ * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h0 : b = (t : A) • (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ x).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hx, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = ((t⁻¹ : Aˣ) : A) • b := by
    conv_rhs => rw [h0]
    rw [smul_smul, Units.inv_mul, one_smul]
  have h3 : (Y : S) * b * (σ Y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  calc ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop
      = x' * (Y * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ Y).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • (x' * ((Y : S) * b * (σ Y).unop) * (σ x').unop) := by
        rw [h2]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • ((T⁻¹ : Aˣ) : A) • ((x' : S) * b' * (σ x').unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = _ := by
        rw [hx', Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul]
        ring

private theorem sim_conj (σ : S →+* Sᵐᵒᵖ) (b b' : S) (z y : Sˣ) (T : Aˣ) (r : A)
    (hb : b' = algebraMap A S T * ((y : S) * b * (σ y).unop))
    (hz : (z : S) * b' * (σ z).unop = algebraMap A S r * b') :
    ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop = algebraMap A S r * b := by
  have h1 : (σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h3 : (y : S) * b * (σ y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  rw [← Algebra.smul_def] at hz ⊢
  calc ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop
      = ((y⁻¹ : Sˣ) : S) * ((z : S) * ((y : S) * b * (σ y).unop) * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((T⁻¹ : Aˣ) : A) • (((y⁻¹ : Sˣ) : S) * ((z : S) * b' * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = r • (((y⁻¹ : Sˣ) : S) * (((T⁻¹ : Aˣ) : A) • b') * (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [hz]; simp only [mul_smul_comm, smul_mul_assoc]; rw [smul_comm]
    _ = r • ((((y⁻¹ : Sˣ) : S) * y) * b * ((σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop)) := by
        rw [← h3]; simp only [mul_assoc]
    _ = r • b := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Ring

private theorem mem_forms_move {A H V : Type} [Group A] [Group H] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (Γ Γ' : Subgroup A) (ι : Γ →* H) (ι' : Γ' →* H) (K : Subgroup H) (y : A) (d : H)
    (hc : ∀ γ' : Γ', ∃ γ : Γ, (γ' : A) = y * (γ : A) * y⁻¹ ∧ ι' γ' = d * ι γ * d⁻¹)
    {Φ : H → V} (hΦ : Φ ∈ HeckeTraceForms.forms ι K (ξ.comp Γ.subtype)) :
    (fun g => ξ y (Φ (d⁻¹ * g))) ∈ HeckeTraceForms.forms ι' K (ξ.comp Γ'.subtype) := by
  refine ⟨fun γ' g => ?_, fun k hk g => ?_⟩
  · obtain ⟨γ, e1, e2⟩ := hc γ'
    have e3 : d⁻¹ * (ι' γ' * g) = ι γ * (d⁻¹ * g) := by rw [e2]; group
    have e4 : Φ (ι γ * (d⁻¹ * g)) = ξ (γ : A) (Φ (d⁻¹ * g)) := hΦ.1 γ (d⁻¹ * g)
    show ξ y (Φ (d⁻¹ * (ι' γ' * g))) = ξ (γ' : A) (ξ y (Φ (d⁻¹ * g)))
    rw [e3, e4, e1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · show ξ y (Φ (d⁻¹ * (g * k))) = ξ y (Φ (d⁻¹ * g))
    rw [← mul_assoc]
    exact congrArg _ (hΦ.2 k hk _)

variable {p : ℕ} [Fact p.Prime]

private theorem op_move {G : HTGroup p} {A V : Type} [Group A] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (K : Subgroup G.GAf) (f : G.GAf → ℂ) (Φ : G.GAf × Gr G 1 → V) (y : A)
    (d : G.GAf × Gr G 1) :
    op K f (fun g => ξ y (Φ (d⁻¹ * g))) = fun g => ξ y (op K f Φ (d⁻¹ * g)) := by
  funext g
  let L : V ≃+ V :=
    { toFun := ξ y
      invFun := ξ y⁻¹
      left_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      right_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      map_add' := map_add _ }
  show ∑ᶠ h : G.GAf ⧸ K, f h.out • ξ y (Φ (d⁻¹ * (g * (h.out, 1)))) =
    L (∑ᶠ h : G.GAf ⧸ K, f h.out • Φ (d⁻¹ * g * (h.out, 1)))
  rw [AddEquiv.map_finsum]
  refine finsum_congr fun h => ?_
  show _ = ξ y (_ • _)
  rw [map_smul, mul_assoc]

private theorem conj_emb (G : HTGroup p) (B B' : DForm G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : (B'.β : G.C) = algebraMap ℚ G.C s * (y * B.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t)
    (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ) (hx' : Triv G (AfP p) B'.β x' t') :
    ∃ d : G.GAf × Gr G 1, ∀ γ' : grp G B'.β, ∃ γ : grp G B.β,
      (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (γ : G.Cˣ × ℚˣ) * ((y, 1) : G.Cˣ × ℚˣ)⁻¹ ∧
      B'.embAt x' t' hx' γ' = d * B.embAt x t hx γ * d⁻¹ := by
  let Y : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom y
  let T : (AfP p)ˣ := Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs.ne')
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) := by
    show _ = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s)
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  have hb : inC G (AfP p) B'.β = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) *
      ((Y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) B.β * (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop) := by
    rw [hβ, map_mul, map_mul, map_mul, e1, e2]
    rfl
  have hc := sim_triv (starT G.star (AfP p)) _ _ x x' Y t t' T hx hx' hb
  let c : G.GAf := ⟨(x' * Y * x⁻¹, t' * T⁻¹ * t⁻¹), hc⟩
  refine ⟨(c, inclG G 1 (locC G (y, 1))), fun γ' => ?_⟩
  have hz : ((γ'.1.1 : G.Cˣ) : G.C) * B'.β * (G.star ((γ'.1.1 : G.Cˣ) : G.C)).unop =
      algebraMap ℚ G.C (γ'.1.2 : ℚ) * B'.β := γ'.2.1
  have hmem : ((y⁻¹ * γ'.1.1 * y, γ'.1.2) : G.Cˣ × ℚˣ) ∈ grp G B.β :=
    ⟨sim_conj G.star (B.β : G.C) (B'.β : G.C) γ'.1.1 y (Units.mk0 s hs.ne') (γ'.1.2 : ℚ) hβ hz, γ'.2.2⟩
  have hconj : (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (y⁻¹ * γ'.1.1 * y, γ'.1.2) *
      ((y, 1) : G.Cˣ × ℚˣ)⁻¹ := by
    refine Prod.ext ?_ ?_
    · simp [mul_assoc]
    · simp
  refine ⟨⟨_, hmem⟩, hconj, ?_⟩
  refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) ?_
  · show x' * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * x'⁻¹ =
      (x' * Y * x⁻¹) * (x * Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) * x⁻¹) *
        (x' * Y * x⁻¹)⁻¹
    have e3 : Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) =
        Y⁻¹ * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * Y := by
      rw [map_mul, map_mul, map_inv]
    rw [e3]
    group
  · have e3 : ∀ a b : (AfP p)ˣ, b = a * b * a⁻¹ := fun a b => by
      rw [mul_comm a b, mul_inv_cancel_right]
    exact e3 (t' * T⁻¹ * t⁻¹) (Units.map (algebraMap ℚ (AfP p)).toMonoidHom γ'.1.2)
  · have e3 := congrArg ((inclG G 1).comp (locC G)) hconj
    rw [map_mul, map_mul, map_inv] at e3
    exact e3

theorem clsMove : ClsMove := by
  intro p _ G V _ _ ξ K J ψ θ e ⟨B, x, t, hx, Φ, hΦ, h0, he, hψ⟩
  have hrel : DForm.Rel B (Quot.out (Quot.mk _ B : DFCls G)) :=
    (GlobalTheory.LKDef.Regroup.dform_rel_equivalence.eqvGen_iff).1
      (Quot.eqvGen_exact (Quot.out_eq (Quot.mk DForm.Rel B)).symm)
  obtain ⟨y, s, hs, hβ⟩ := hrel
  obtain ⟨d, hd⟩ := conj_emb G B _ y s hs hβ x t hx _ _
    (Quot.out (Quot.mk _ B : DFCls G)).trivAf.choose_spec.choose_spec
  refine ⟨Quot.mk _ B, fun g => ξ (y, 1) (Φ (d⁻¹ * g)),
    mem_forms_move ξ _ _ _ _ _ _ d hd hΦ, fun h => h0 ?_, ?_, fun j => ?_⟩
  · funext g
    have := congrFun h (d * g)
    simp only [inv_mul_cancel_left, Pi.zero_apply] at this
    have h2 := congrArg (ξ ((y, 1) : G.Cˣ × ℚˣ)⁻¹) this
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h2
    exact h2
  · rw [op_move, he]
  · rw [op_move, hψ j]
    funext g
    simp

end UpperTheory.Gal.Spc
