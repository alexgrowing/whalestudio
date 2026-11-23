import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRangeOfCompEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedLatticeFiniteProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDescendsAlongFlatExtensionStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published

namespace GlobalTheory.PerfdLat.LatDescent

theorem adic_surj (A : Type) [CommRing A] (f : A) (x : AdicCompletion (Ideal.span {f}) A) :
    ∃ (a : A) (y : AdicCompletion (Ideal.span {f}) A), x = algebraMap A _ a + algebraMap A _ f * y := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.1 1)
  have hx : x - algebraMap A (AdicCompletion (Ideal.span {f}) A) a ∈
      ((Ideal.span {f}) ^ 1).map (algebraMap A (AdicCompletion (Ideal.span {f}) A)) := by
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton f), AdicCompletion.algebraMap_apply]
    simpa [AdicCompletion.eval, sub_eq_zero] using ha.symm
  rw [pow_one, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨a, y, by rw [mul_comm, hy]; ring⟩

theorem adic_inj (A : Type) [CommRing A] (f a : A) (y : AdicCompletion (Ideal.span {f}) A)
    (h : algebraMap A _ a = algebraMap A _ f * y) : ∃ b, a = f * b := by
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {f}) 1) h
  have hf : Ideal.Quotient.mk (Ideal.span {f} ^ 1) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [pow_one]; exact Ideal.mem_span_singleton_self f)
  rw [map_mul, AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, hf, zero_mul,
    Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton'] at h1
  obtain ⟨b, hb⟩ := h1
  exact ⟨b, by rw [← hb, mul_comm]⟩

theorem finite_of_semilinearEquiv {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (φ : M ≃ₛₗ[σ] N) [Module.Finite R M] : Module.Finite S N := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine ⟨⟨s.image φ, ?_⟩⟩
  have h := Submodule.map_span (φ : M →ₛₗ[σ] N) (s : Set M)
  have h' : LinearMap.range (φ : M →ₛₗ[σ] N) = ⊤ := LinearMap.range_eq_top.2 φ.surjective
  rw [hs, Submodule.map_top, h'] at h
  rw [Finset.coe_image]
  exact h.symm

theorem preimage_finite_projective : ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (A : Type) [CommRing A] [IsDomain A]
    [CharZero A] (S : CycPerfd p) [Algebra A S.R] (e : AdicCompletion (Ideal.span {(p : A)}) A ≃+* S.R),
    (∀ a, e (algebraMap A _ a) = algebraMap A S.R a) → ∀ (G : PDivGroup p S.R) (c : ConstTate (eps S) G) (n : ℕ)
    (L : Submodule A (Fin G.height → A)), (∀ x, x ∈ L ↔ piMap (algebraMap A S.R) _ x ∈ H D c n) →
    Module.Finite A L ∧ Module.Projective A L ∧ (∀ x : Fin G.height → A, (p : A) • x ∈ L) ∧
    Submodule.span S.R (piMap (algebraMap A S.R) (Fin G.height) '' (L : Set (Fin G.height → A))) = H D c n := by
  intro p _ D A _ _ _ S _ e he G c n L hL
  have hpH : ∀ z : Fin G.height → S.R, (p : S.R) • z ∈ H D c n := fun z => by
    obtain ⟨u, hu⟩ := zeta_one_sub_one_dvd S
    apply base_le_H D c n
    rw [mem_base]
    exact ⟨u • z, by rw [smul_smul, ← hu]⟩
  have hpL : ∀ x : Fin G.height → A, (p : A) • x ∈ L := fun x => by
    rw [hL]
    have h1 : piMap (algebraMap A S.R) _ ((p : A) • x) = (p : S.R) • piMap (algebraMap A S.R) _ x := by
      ext j; simp
    rw [h1]; exact hpH _
  have hdense : ∀ r : S.R, ∃ (a : A) (s : S.R), r = algebraMap A S.R a + (p : S.R) * s := fun r => by
    obtain ⟨a, y, hy⟩ := adic_surj A (p : A) (e.symm r)
    refine ⟨a, e y, ?_⟩
    have h1 := congrArg e hy
    rw [e.apply_symm_apply, map_add, map_mul, he, he, map_natCast] at h1
    exact h1
  have hspan : Submodule.span S.R (piMap (algebraMap A S.R) (Fin G.height) '' (L : Set (Fin G.height → A))) =
      H D c n := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact (hL x).1 hx
    · intro z hz
      choose a s hs using fun j => hdense (z j)
      have ha : (a : Fin G.height → A) ∈ L := by
        rw [hL]
        have h1 : piMap (algebraMap A S.R) _ a = z - (p : S.R) • s := by
          ext j; simp [hs j]
        rw [h1]; exact Submodule.sub_mem _ hz (hpH s)
      have hz' : z = piMap (algebraMap A S.R) _ a +
          ∑ j, s j • piMap (algebraMap A S.R) _ ((p : A) • Pi.single j 1) := by
        ext i
        simp [hs i, Finset.sum_apply, Pi.single_apply, mul_comm]
      rw [hz']
      exact Submodule.add_mem _ (Submodule.subset_span ⟨a, ha, rfl⟩)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hpL _, rfl⟩))
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hAreg : IsSMulRegular A (p : A) := fun a b h => mul_left_cancel₀ hp0 h
  have hLreg : IsSMulRegular L (p : A) := fun x y h =>
    Subtype.ext (funext fun j => mul_left_cancel₀ hp0 (congrFun (congrArg Subtype.val h) j))
  obtain ⟨hfl, hpl⟩ := GlobalTheory.T.localized_lattice_finite_projective A (p : A) G.height L hpL
  let B := AdicCompletion (Ideal.span {(p : A)}) A
  let N : Submodule B (Fin G.height → B) := Submodule.comap (piMap (e : B →+* S.R) (Fin G.height)) (H D c n)
  have hBreg : IsSMulRegular B (algebraMap A B (p : A)) := fun x y hxy => e.injective (S.reg (by
    have h1 := congrArg e hxy
    simp only [smul_eq_mul, map_mul, he, map_natCast] at h1
    exact h1))
  have hN : ∀ y, algebraMap A B (p : A) • y ∈ N := fun y => by
    show piMap (e : B →+* S.R) _ _ ∈ H D c n
    rw [map_smulₛₗ]
    simpa [he] using hpH (piMap (e : B →+* S.R) _ y)
  have hL' : ∀ x, x ∈ L ↔ piMap (algebraMap A B) _ x ∈ N := fun x => by
    rw [hL]
    show _ ↔ piMap (e : B →+* S.R) _ _ ∈ H D c n
    have h1 : piMap (e : B →+* S.R) _ (piMap (algebraMap A B) _ x) = piMap (algebraMap A S.R) _ x := by
      ext j; exact he (x j)
    rw [h1]
  obtain ⟨eqv⟩ := GlobalTheory.T.baseChange_preimage_equiv_of_mod_regular_iso A B (p : A) G.height N L hBreg (adic_surj A (p : A)) (adic_inj A (p : A)) hN hL'
  haveI i1 : RingHomInvPair (e : B →+* S.R) (e.symm : S.R →+* B) := RingHomInvPair.of_ringEquiv e
  haveI i2 : RingHomInvPair (e.symm : S.R →+* B) (e : B →+* S.R) := RingHomInvPair.symm _ _
  let φ : N ≃ₛₗ[(e : B →+* S.R)] H D c n :=
    { toFun := fun y => ⟨piMap (e : B →+* S.R) _ y.1, y.2⟩
      invFun := fun z => ⟨piMap (e.symm : S.R →+* B) _ z.1, by
        show piMap (e : B →+* S.R) _ _ ∈ H D c n
        convert z.2 using 1
        ext j; simp⟩
      map_add' := fun y y' => Subtype.ext (map_add _ _ _)
      map_smul' := fun b y => Subtype.ext (map_smulₛₗ _ _ _)
      left_inv := fun y => Subtype.ext (funext fun j => by simp)
      right_inv := fun z => Subtype.ext (funext fun j => by simp) }
  obtain ⟨hHp, hHf⟩ := projective_finite_H p D S G c n
  haveI : Module.Finite B N := finite_of_semilinearEquiv φ.symm
  haveI : Module.Projective B N := Module.Projective.of_equiv φ.symm
  haveI : Module.Finite B (TensorProduct A B L) := Module.Finite.equiv eqv.symm
  haveI : Module.Projective B (TensorProduct A B L) := Module.Projective.of_equiv' eqv.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.CompletionDescent.finite_projective A (p : A) L hAreg hLreg hfl hpl inferInstance inferInstance
  exact ⟨h1, h2, hpL, hspan⟩

end GlobalTheory.PerfdLat.LatDescent
