import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_res_apply (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    {U V : T.Opens} (h : U ≤ V) :
    letI := (secAlg A g U).toAlgebra; letI := (secAlg A g V).toAlgebra
    ∀ (ρ : Γ(T, V) →ₐ[A] Γ(T, U)), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom →
    ∀ t : Γ(T, V) ⊗[A] B,
      kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (kappa A B g I V t) := by
  letI := (secAlg A g U).toAlgebra; letI := (secAlg A g V).toAlgebra
  intro ρ hρ t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
    have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := by
      rw [← hρ]; rfl
    rw [hc]
    congr 1
    · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
      rfl
    · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
          (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
          (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
      exact (congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm

theorem kappa_res (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (U V : T.affineOpens) (h : (U : T.Opens) ≤ V) :
    letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra; letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
    ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
      (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤ RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra; letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        change _ = GlobalTheory.HilbAff.secAlg A g U a
        rw [← GlobalTheory.HilbAff.secAlg_res A g h]; rfl }
  refine ⟨ρ, rfl, ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [GlobalTheory.HilbAff.kappa_res_apply A B g I h ρ rfl t, ht, map_zero]

end GlobalTheory.HilbAff
