import Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut TensorProduct

namespace LateralTheory.E.ColimPf.RigidPf

theorem etale_lift_to_strict_local_ring_unique_on_residue_field : LateralTheory.E.ColimPf.Rigid := by
  intro A B O Ω _ ψ g hg hloc u v huv hψ
  let : Algebra A B := g.hom.toAlgebra
  let : Algebra A O := (g ≫ u).hom.toAlgebra
  have : Algebra.Etale A B := hg
  let u' : B →ₐ[A] O := { u.hom with commutes' := fun _ => rfl }
  have hv : ∀ a, v.hom (g.hom a) = (g ≫ u).hom a := fun a => by rw [huv]; rfl
  let v' : B →ₐ[A] O := { v.hom with commutes' := hv }
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal A B = B ⊗[A] B ∙ e :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg A B)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[B⁄A]
  let w : B ⊗[A] B →ₐ[A] O := Algebra.TensorProduct.productMap u' v'
  have hψu : ∀ b, ψ (v.hom b) = ψ (u.hom b) := fun b => (DFunLike.congr_fun hψ b).symm
  have hpt : ∀ t : B ⊗[A] B, ψ (w t) = ψ (u.hom (Algebra.TensorProduct.lmul' A t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [w, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      change ψ (u.hom x) * ψ (v.hom y) = ψ (u.hom x) * ψ (u.hom y)
      rw [hψu]
    | add x y hx hy => simp only [map_add, hx, hy]
  have he0 : e ∈ KaehlerDifferential.ideal A B := by rw [hsp]; exact Submodule.mem_span_singleton_self e
  have hwe : ψ (w e) = 0 := by
    rw [hpt]
    have : Algebra.TensorProduct.lmul' A e = 0 := he0
    rw [this, map_zero, map_zero]
  have hwe0 : w e = 0 := by
    have hu : IsUnit (1 - w e) := hloc _ (by rw [map_sub, map_one, hwe, sub_zero]; exact one_ne_zero)
    have hid : w e * (1 - w e) = 0 := by
      have := (he.map w).eq
      rw [mul_sub, mul_one, this, sub_self]
    simpa using (hu.mul_left_eq_zero).1 hid
  ext b
  have hb : b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ KaehlerDifferential.ideal A B := by
    rw [KaehlerDifferential.ideal, RingHom.mem_ker, map_sub]
    simp
  rw [hsp] at hb
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hb
  have := congrArg w hr
  rw [smul_eq_mul, map_mul, hwe0, mul_zero, map_sub] at this
  simp only [w, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul] at this
  exact sub_eq_zero.1 this.symm

end LateralTheory.E.ColimPf.RigidPf
