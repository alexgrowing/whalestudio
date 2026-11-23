import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain

set_option autoImplicit false

noncomputable section

open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings

namespace GlobalTheory.RingChain.FrobTr

theorem isFrobLin_of_modIso : ∀ (p k : ℕ) [Fact p.Prime] (A R : Type) [CommRing A] [CommRing R] [Algebra A R], ModIso R (p : A) → ∀ (M N M' N' : Type) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] (Φ : M →ₛₗ[algebraMap A R] M') (Ψ : N →ₛₗ[algebraMap A R] N'), Function.Bijective Φ → Function.Bijective Ψ → ∀ (ψ : M →+ N) (ψ' : M' →+ N'), (∀ x, Ψ (ψ x) = ψ' (Φ x)) → IsFrobLin R p (p ^ k) ψ' → IsFrobLin A p (p ^ k) ψ := by
  intro p k _ A R _ _ _ hmod M N M' N' _ _ _ _ _ _ _ _ Φ Ψ hΦ hΨ ψ ψ' hc hR f hf
  have hq : p ^ k ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hle : Ideal.span {(p : A)} ≤ (Ideal.span {(p : R)}).comap (algebraMap A R) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  let ι : (A ⧸ Ideal.span {(p : A)}) →+* R ⧸ Ideal.span {(p : R)} := Ideal.quotientMap _ (algebraMap A R) hle
  have hι : ∀ a, ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap A R a) := fun _ => rfl
  have hιb : Function.Bijective ι := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hι, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, ← map_natCast (algebraMap A R)] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hmod.2 a hx
    · intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨a, ha⟩ := hmod.1 r
      refine ⟨Ideal.Quotient.mk _ a, ?_⟩
      rw [hι, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_natCast (algebraMap A R) p, ← neg_sub]
      exact dvd_neg.2 ha
  let ιe := RingEquiv.ofBijective ι hιb
  have hfp : f (p : A) = 0 := by
    rw [hf, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact dvd_pow_self _ hq
  let fb : (A ⧸ Ideal.span {(p : A)}) →+* A ⧸ Ideal.span {(p : A)} := Ideal.Quotient.lift _ f (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha; rw [map_mul, hfp, zero_mul])
  let fR : R →+* R ⧸ Ideal.span {(p : R)} := ι.comp (fb.comp (ιe.symm.toRingHom.comp (Ideal.Quotient.mk _)))
  have hfR : ∀ r, fR r = Ideal.Quotient.mk _ (r ^ p ^ k) := by
    intro r
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ιe.symm (Ideal.Quotient.mk _ r))
    have h1 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (algebraMap A R a) = Ideal.Quotient.mk _ r := by
      rw [← hι]; change ιe (Ideal.Quotient.mk _ a) = _; rw [ha, RingEquiv.apply_symm_apply]
    change ι (fb (ιe.symm (Ideal.Quotient.mk _ r))) = _
    rw [← ha, Ideal.Quotient.lift_mk, hf, hι]
    simp only [map_pow, h1]
  have hfRa : ∀ a, fR (algebraMap A R a) = ι (f a) := by
    intro a; rw [hfR, hf, hι, map_pow (algebraMap A R)]
  obtain ⟨e', he'⟩ := hR fR hfR
  let XA := (ModuleCat.restrictScalars f).obj (ModuleCat.of _ (A ⧸ Ideal.span {(p : A)}))
  let XR := (ModuleCat.restrictScalars fR).obj (ModuleCat.of _ (R ⧸ Ideal.span {(p : R)}))
  let kA : (A ⧸ Ideal.span {(p : A)}) →+ XA := AddMonoidHom.id (A ⧸ Ideal.span {(p : A)})
  let kR : (R ⧸ Ideal.span {(p : R)}) →+ XR := AddMonoidHom.id (R ⧸ Ideal.span {(p : R)})
  let jA : XA →+ (A ⧸ Ideal.span {(p : A)}) := AddMonoidHom.id (A ⧸ Ideal.span {(p : A)})
  let jR : XR →+ (R ⧸ Ideal.span {(p : R)}) := AddMonoidHom.id (R ⧸ Ideal.span {(p : R)})
  have hsA : ∀ (a : A) (b : A ⧸ Ideal.span {(p : A)}), a • kA b = kA (f a * b) := fun _ _ => rfl
  have hsR : ∀ (r : R) (b : R ⧸ Ideal.span {(p : R)}), r • kR b = kR (fR r * b) := fun _ _ => rfl
  let ΦE : M ≃+ M' := AddEquiv.ofBijective Φ.toAddMonoidHom hΦ
  have hΦi : ∀ (c : A) (y : M'), ΦE.symm (algebraMap A R c • y) = c • ΦE.symm y := by
    intro c y
    apply ΦE.injective
    rw [AddEquiv.apply_symm_apply]
    change _ = Φ (c • ΦE.symm y)
    rw [Φ.map_smulₛₗ]
    change _ = algebraMap A R c • ΦE (ΦE.symm y)
    rw [AddEquiv.apply_symm_apply]
  let T : XA ⊗[A] M →+ XR ⊗[R] M' := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b : XA => ((TensorProduct.mk R XR M' (kR (ι (jA b)))).toAddMonoidHom).comp Φ.toAddMonoidHom)
      fun b b' => AddMonoidHom.ext fun x => by
        change kR (ι (jA (b + b'))) ⊗ₜ[R] Φ x = kR (ι (jA b)) ⊗ₜ[R] Φ x + kR (ι (jA b')) ⊗ₜ[R] Φ x
        rw [map_add, map_add, map_add, TensorProduct.add_tmul])
    fun a b x => by
      change kR (ι (f a * jA b)) ⊗ₜ[R] Φ x = kR (ι (jA b)) ⊗ₜ[R] Φ (a • x)
      rw [Φ.map_smulₛₗ, ← TensorProduct.smul_tmul, hsR, hfRa, map_mul]
  have hT : ∀ (b : A ⧸ Ideal.span {(p : A)}) (x : M), T (kA b ⊗ₜ[A] x) = kR (ι b) ⊗ₜ[R] Φ x := fun _ _ => rfl
  let U : XR ⊗[R] M' →+ XA ⊗[A] M := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b : XR =>
        ((TensorProduct.mk A XA M (kA (ιe.symm (jR b)))).toAddMonoidHom).comp ΦE.symm.toAddMonoidHom)
      fun b b' => AddMonoidHom.ext fun x => by
        change kA (ιe.symm (jR (b + b'))) ⊗ₜ[A] ΦE.symm x =
          kA (ιe.symm (jR b)) ⊗ₜ[A] ΦE.symm x + kA (ιe.symm (jR b')) ⊗ₜ[A] ΦE.symm x
        rw [map_add, map_add, map_add, TensorProduct.add_tmul])
    fun s b x' => by
      obtain ⟨t, s', hs'⟩ := hmod.1 s
      have hs : s = algebraMap A R t + algebraMap A R (p : A) * s' := by rw [← hs']; ring
      have e1 : ιe.symm (fR s * jR b) = f t * ιe.symm (jR b) := by
        rw [hs, map_add, map_mul fR, hfRa, hfRa, hfp, map_zero, zero_mul, add_zero, map_mul]
        congr 1
        exact ιe.symm_apply_apply (f t)
      change kA (ιe.symm (fR s * jR b)) ⊗ₜ[A] ΦE.symm x' = kA (ιe.symm (jR b)) ⊗ₜ[A] ΦE.symm (s • x')
      rw [e1, hs, add_smul, mul_smul, map_add, hΦi, hΦi, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
        ← TensorProduct.smul_tmul, hsA, hsA, hfp, zero_mul, map_zero, TensorProduct.zero_tmul, add_zero]
  have hU : ∀ (b : R ⧸ Ideal.span {(p : R)}) (x : M'), U (kR b ⊗ₜ[R] x) = kA (ιe.symm b) ⊗ₜ[A] ΦE.symm x :=
    fun _ _ => rfl
  have UT : ∀ t, U (T t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
    | tmul b x =>
      change U (T (kA (jA b) ⊗ₜ[A] x)) = kA (jA b) ⊗ₜ[A] x
      rw [hT, hU, show ιe.symm (ι (jA b)) = jA b from ιe.symm_apply_apply _,
        show ΦE.symm (Φ x) = x from ΦE.symm_apply_apply x]
  have TU : ∀ t, T (U t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
    | tmul b x =>
      change T (U (kR (jR b) ⊗ₜ[R] x)) = kR (jR b) ⊗ₜ[R] x
      rw [hU, hT, show ι (ιe.symm (jR b)) = jR b from ιe.apply_symm_apply _,
        show Φ (ΦE.symm x) = x from ΦE.apply_symm_apply x]
  let TE : XA ⊗[A] M ≃+ XR ⊗[R] M' :=
    { toFun := T, invFun := U, left_inv := UT, right_inv := TU, map_add' := map_add T }
  let ΨE : N ≃+ N' := AddEquiv.ofBijective Ψ.toAddMonoidHom hΨ
  refine ⟨(TE.trans e').trans ΨE.symm, fun a x => ?_⟩
  change ΨE.symm (e' ((Ideal.Quotient.mk _ (algebraMap A R a) : R ⧸ Ideal.span {(p : R)}) ⊗ₜ[R, fR] Φ x)) = a • ψ x
  rw [he', ← hc, ← Ψ.map_smulₛₗ]
  exact ΨE.symm_apply_apply _

end GlobalTheory.RingChain.FrobTr
