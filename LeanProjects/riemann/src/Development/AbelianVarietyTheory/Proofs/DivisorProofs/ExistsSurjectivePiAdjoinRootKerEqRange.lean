import Mathlib
open Polynomial

namespace GlobalTheory

theorem exists_equiv_pi_adjoinRoot_of_aeval_eq_zero (F : Type) [Field F] (Q : Type) [AddCommGroup Q]
    [Module F Q] [FiniteDimensional F Q] (g : Module.End F Q) (f : F[X]) [Fact (Irreducible f)]
    (h : aeval g f = 0) :
    ∃ (t : ℕ) (e : Q ≃ₗ[F] (Fin t → AdjoinRoot f)),
      (∀ v, e (g v) = AdjoinRoot.root f • e v) ∧ Module.finrank F Q = f.natDegree * t := by
  have hf : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  let φ : AdjoinRoot f →+* Module.End F Q :=
    Ideal.Quotient.lift (Ideal.span {f}) (aeval g : F[X] →ₐ[F] Module.End F Q).toRingHom (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [h])
  have hφ : ∀ p : F[X], φ (AdjoinRoot.mk f p) = aeval g p := fun p => rfl
  letI : Module (AdjoinRoot f) Q := Module.compHom Q φ
  have hs : ∀ (a : AdjoinRoot f) (v : Q), a • v = φ a v := fun _ _ => rfl
  haveI : IsScalarTower F (AdjoinRoot f) Q := ⟨fun c a v => by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hs, hs, AdjoinRoot.smul_mk, hφ, hφ]
    simp⟩
  haveI : Module.Finite (AdjoinRoot f) Q := Module.Finite.of_restrictScalars_finite F _ _
  refine ⟨Module.finrank (AdjoinRoot f) Q,
    (Module.finBasis (AdjoinRoot f) Q).equivFun.restrictScalars F, fun v => ?_, ?_⟩
  · have : g v = AdjoinRoot.root f • v := by
      rw [hs, ← AdjoinRoot.mk_X, hφ]; simp
    rw [this]
    exact map_smul (Module.finBasis (AdjoinRoot f) Q).equivFun _ _
  · rw [← Module.finrank_mul_finrank F (AdjoinRoot f) Q, (AdjoinRoot.powerBasis hf).finrank,
      AdjoinRoot.powerBasis_dim]

theorem exists_surjective_pi_adjoinRoot_ker_eq_range (F : Type) [Field F] (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X])
    [Fact (Irreducible f)] :
    ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧
      (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧
      LinearMap.ker π = LinearMap.range (aeval g f) ∧
      Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by
  set N : Submodule F V := LinearMap.range (aeval g f) with hN
  have hg : N ≤ N.comap g := by
    rintro _ ⟨v, rfl⟩
    refine ⟨g v, ?_⟩
    have h1 : aeval g f * g = g * aeval g f := by
      have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using this
    exact congrArg (fun u : Module.End F V => u v) h1
  let gq : Module.End F (V ⧸ N) := N.mapQ N g hg
  have hq : ∀ v, gq (N.mkQ v) = N.mkQ (g v) := fun v => rfl
  have hp : ∀ (p : F[X]) (v : V), aeval gq p (N.mkQ v) = N.mkQ (aeval g p v) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => intro v; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro v; simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial n a ih =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply, hq, ih]
  have h0 : aeval gq f = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := N.mkQ_surjective x
    rw [hp]
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨v, rfl⟩
  obtain ⟨t, e, he, hd⟩ := exists_equiv_pi_adjoinRoot_of_aeval_eq_zero F (V ⧸ N) gq f h0
  refine ⟨t, e.toLinearMap ∘ₗ N.mkQ, e.surjective.comp N.mkQ_surjective, fun v => ?_, ?_, ?_⟩
  · have := he (N.mkQ v)
    rw [hq] at this
    exact this
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]
  · have h1 := LinearMap.finrank_range_add_finrank_ker (aeval g f)
    have h2 := Submodule.finrank_quotient_add_finrank N
    rw [← hN] at h1
    omega

end GlobalTheory
