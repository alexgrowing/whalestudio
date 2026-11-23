import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero

open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.HomCalc
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def comp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') : NumD.Hom (g.comp f) N N'' where
  φ := I'.φ.comp I.φ
  h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
  h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
  θ_eq x y u := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.θ_eq x y u)
    have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
    have c : Units.map (g.comp f).toMonoidHom (N.θ x y u) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.θ x y u)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
    linear_combination (norm := abel) a + b
  σ_eq x := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.σ_eq x)
    have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
    have c : Units.map (g.comp f).toMonoidHom (N.σ x) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.σ x)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply, map_inv I.φ] at a b ⊢
    linear_combination (norm := abel) a + b
  lam := I'.lam * Units.map g.toMonoidHom I.lam
  th_eq x := by
    rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq]
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.comp_apply]
    ring
  e := I.e.trans I'.e
  c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
  ψ_eq χ := by
    have c : Units.map (g.comp f).toMonoidHom (N.ψ χ) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.ψ χ)) := rfl
    rw [c, ← I.ψ_eq, map_mul, ← I'.ψ_eq, I.c_eq, AddEquiv.trans_apply, mul_assoc]

theorem comp_rel {I : NumD.Hom f N N'} {I' : NumD.Hom g N' N''} {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b)
    (h' : I'.Rel b c) : (comp I I').Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have u := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (h.2 χ)
  have v := congrArg Additive.ofMul (h'.2 (I.e χ))
  have w : Units.map (g.comp f).toMonoidHom (a.s χ) = Units.map g.toMonoidHom (Units.map f.toMonoidHom (a.s χ)) := rfl
  rw [I.c_eq, h.1] at v
  show c.s (I'.e (I.e χ)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) =
    _ * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _))
  apply Additive.ofMul.injective
  simp only [w, map_mul, ofMul_mul] at u v ⊢
  linear_combination (norm := abel) u + v

def inv {M M' : NumD O} (I : NumD.Iso M' M) : NumD.Hom (RingHom.id O) M M' where
  φ := I.φ.symm.toMonoidHom
  h x := (I.h (I.φ.symm x))⁻¹
  h_one := by rw [map_one, I.h_one, inv_one]
  θ_eq x y u := by
    have a := congrArg Additive.ofMul (I.θ_eq (I.φ.symm x) (I.φ.symm y) (I.φ.symm u))
    show M'.θ (I.φ.symm x) (I.φ.symm y) (I.φ.symm u) * _ * _ * _ = M.θ x y u * _ * _ * _ * _
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  σ_eq x := by
    have a := congrArg Additive.ofMul (I.σ_eq (I.φ.symm x))
    show M'.σ (I.φ.symm x) * _ = M.σ x * _
    apply Additive.ofMul.injective
    simp only [map_inv I.φ.symm, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  lam := I.lam⁻¹
  th_eq x := by
    have a := I.th_eq (I.φ.symm x)
    rw [MulEquiv.apply_symm_apply] at a
    show M'.th (I.φ.symm x) = _ * M.th x
    rw [a, ← mul_inv, Units.inv_mul_cancel_left]
  e := I.e.symm
  c_eq χ := by
    show _ = I.φ.symm _
    rw [MulEquiv.eq_symm_apply, ← I.c_eq, AddEquiv.apply_symm_apply]
  ψ_eq χ := by
    obtain ⟨χ, rfl⟩ := I.e.surjective χ
    show _ = M.ψ _
    rw [AddEquiv.symm_apply_apply, I.c_eq, MulEquiv.symm_apply_apply, ← I.ψ_eq, mul_inv_cancel_right]

theorem inv_rel {M M' : NumD O} {I : NumD.Iso M' M} {a : M'.Gt} {b : M.Gt} (h : I.Rel a b) : (inv I).Rel b a := by
  refine ⟨(I.φ.symm_apply_eq.2 h.1).symm, fun χ => ?_⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  have u := congrArg Additive.ofMul (h.2 χ)
  show a.s (I.e.symm _) * (I.h (I.φ.symm _))⁻¹ = b.s _ * (I.h (I.φ.symm _))⁻¹ * (I.h (I.φ.symm _))⁻¹
  rw [AddEquiv.symm_apply_apply, I.c_eq, h.1, ← map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, MulEquiv.symm_apply_apply] at u ⊢
  linear_combination (norm := abel) -u

end GlobalTheory.HomCalc
end
