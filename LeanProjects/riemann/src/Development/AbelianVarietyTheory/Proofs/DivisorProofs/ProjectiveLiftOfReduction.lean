import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain

set_option autoImplicit false

open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings

namespace GlobalTheory.RingChain.TwistProj

theorem projective_of_addEquiv {A S T M : Type} [CommRing A] [CommRing S] [AddCommGroup T] [Module S T]
    [Module.Projective S T] [AddCommGroup M] [Module A M] (I : Ideal A) (σ : (A ⧸ I) ≃+* S) (E : M ≃+ T)
    (hE : ∀ (x : A) (m : M), E (x • m) = σ (Ideal.Quotient.mk I x) • E m) :
    Module.Projective (A ⧸ I) ((A ⧸ I) ⊗[A] M) := by
  let u : (A ⧸ I) ⊗[A] M →+ T := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => σ b • E m) fun m m' => by rw [map_add, smul_add])
      fun b b' => AddMonoidHom.ext fun m => by simp [add_smul])
    fun r b m => by
      change σ (r • b) • E m = σ b • E (r • m)
      rw [hE, Algebra.smul_def, map_mul, mul_comm, mul_smul, Ideal.Quotient.algebraMap_eq]
  have hu : ∀ b m, u (b ⊗ₜ m) = σ b • E m := fun _ _ => rfl
  have key : ∀ (b : A ⧸ I) (m : M), (1 : A ⧸ I) ⊗ₜ[A] E.symm (σ b • E m) = b ⊗ₜ m := fun b m => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← hE, AddEquiv.symm_apply_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq]
  have left : ∀ t, (1 : A ⧸ I) ⊗ₜ[A] E.symm (u t) = t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => rw [map_add, map_add, TensorProduct.tmul_add, hs, ht]
    | tmul b m => rw [hu, key]
  have right : ∀ t, u ((1 : A ⧸ I) ⊗ₜ[A] E.symm t) = t := fun t => by
    rw [hu, map_one, one_smul, AddEquiv.apply_symm_apply]
  have lin : ∀ (c : A ⧸ I) t, u (c • t) = σ c • u t := fun c t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => rw [smul_add, map_add, map_add, smul_add, hs, ht]
    | tmul b m => rw [TensorProduct.smul_tmul', hu, hu, smul_eq_mul, map_mul, mul_smul]
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let F : ((A ⧸ I) ⊗[A] M) ≃ₛₗ[(σ : (A ⧸ I) →+* S)] T :=
    { toFun := u, map_add' := map_add u, map_smul' := lin
      invFun := fun t => (1 : A ⧸ I) ⊗ₜ[A] E.symm t, left_inv := left, right_inv := right }
  exact Module.Projective.of_equiv F.symm

theorem projective_extend {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) (P : Type) [AddCommGroup P] [Module R P]
    [Module.Projective R P] : Module.Projective S ((ModuleCat.extendScalars s).obj (ModuleCat.of R P)) := by
  letI := s.toAlgebra
  exact (inferInstance : Module.Projective S (S ⊗[R] P))

theorem projective_of_twist : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (a : A) (g : R), algebraMap A R a = g → ModIso R a → ∀ (s : R →+* R ⧸ Ideal.span {g}) (M M' P : Type) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P] [Module.Projective R P] (Φ : M →ₛₗ[algebraMap A R] M'), Function.Bijective Φ → ∀ (lam : P →+ M') (e : (ModuleCat.extendScalars s).obj (ModuleCat.of R P) ≃+ M'), (∀ (r : R) (y : P), e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {g}) ⊗ₜ[R, s] y) = r • lam y) → Module.Projective (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⊗[A] M) := by
  intro A R _ _ _ a g hg hiso s M M' P _ _ _ _ _ _ _ Φ hΦ lam e he
  subst hg
  let τ : (A ⧸ Ideal.span {a}) →+* R ⧸ Ideal.span {algebraMap A R a} :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap A R)) fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact map_dvd _ (Ideal.mem_span_singleton.1 hx)
  have hτ : ∀ x, τ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A R x) := fun _ => rfl
  have bij : Function.Bijective τ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun b hb => ?_, fun y => ?_⟩
    · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [hτ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hiso.2 x hb
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hx⟩ := hiso.1 r
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [hτ, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hx
  haveI : Module.Projective (R ⧸ Ideal.span {algebraMap A R a})
      ((ModuleCat.extendScalars s).obj (ModuleCat.of R P)) := by
    exact projective_extend s P
  have lin : ∀ (r : R) (t : (ModuleCat.extendScalars s).obj (ModuleCat.of R P)),
      e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {algebraMap A R a}) • t) = r • e t := fun r t => by
    induction t using TensorProduct.induction_on with
    | zero =>
      change e (_ • 0) = r • e 0
      rw [smul_zero, map_zero, smul_zero]
    | add x y hx hy =>
      have h : ∀ x y : (ModuleCat.extendScalars s).obj (ModuleCat.of R P),
          e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {algebraMap A R a}) • x) = r • e x →
          e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {algebraMap A R a}) • y) = r • e y →
          e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {algebraMap A R a}) • (x + y)) = r • e (x + y) :=
        fun x y hx hy => by rw [smul_add, map_add, map_add, smul_add, hx, hy]
      exact h x y hx hy
    | tmul b y =>
      obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {algebraMap A R a}) b
      exact (he (r * r') y).trans (by rw [mul_smul, ← he]; rfl)
  refine projective_of_addEquiv _ (RingEquiv.ofBijective τ bij)
    ((AddEquiv.ofBijective Φ.toAddMonoidHom hΦ).trans e.symm) fun x m => ?_
  change e.symm (Φ (x • m)) = (Ideal.Quotient.mk _ (algebraMap A R x) : R ⧸ Ideal.span {algebraMap A R a}) • e.symm (Φ m)
  rw [AddEquiv.symm_apply_eq, lin, AddEquiv.apply_symm_apply, map_smulₛₗ]

end GlobalTheory.RingChain.TwistProj
