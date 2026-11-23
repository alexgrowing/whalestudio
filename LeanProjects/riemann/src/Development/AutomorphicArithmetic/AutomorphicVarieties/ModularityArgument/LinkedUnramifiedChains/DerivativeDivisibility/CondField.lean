import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CmpPrime
import Mathlib.RingTheory.DedekindDomain.Different

open Polynomial

namespace UpperTheory.V.J

private theorem cond_field {Λ L : Type} [CommRing Λ] [IsDomain Λ] [IsIntegrallyClosed Λ] [CharZero Λ]
    [Field L] [Algebra (FractionRing Λ) L] [Algebra Λ L] [IsScalarTower Λ (FractionRing Λ) L]
    [FiniteDimensional (FractionRing Λ) L] (g : Λ[X]) (hm : g.Monic)
    (hi : Irreducible (g.map (algebraMap Λ (FractionRing Λ)))) (r : L) (hr : aeval r g = 0)
    (hgen : Algebra.adjoin (FractionRing Λ) {r} = ⊤) (α : L) (hα : IsIntegral Λ α) :
    ∃ W : Λ[X], aeval r (derivative g) * α = aeval r W := by
  have hrA : IsIntegral Λ r := ⟨g, hm, by rwa [aeval_def] at hr⟩
  have hmin : minpoly (FractionRing Λ) r = g.map (algebraMap Λ (FractionRing Λ)) :=
    (minpoly.eq_of_irreducible_of_monic hi (by rw [aeval_map_algebraMap]; exact hr) (hm.map _)).symm
  have hd : aeval r (derivative (minpoly (FractionRing Λ) r)) = aeval r (derivative g) := by
    rw [hmin, derivative_map, aeval_map_algebraMap]
  have hd0 : aeval r (derivative g) ≠ 0 := by
    rw [← hd]
    exact (Algebra.IsSeparable.isSeparable (FractionRing Λ) r).aeval_derivative_ne_zero
      (minpoly.aeval _ r)
  have hmem : α ∈ (Algebra.traceForm (FractionRing Λ) L).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin Λ {r})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [Algebra.traceForm_apply]
    have hyi : IsIntegral Λ y := (mem_integralClosure_iff Λ L).1 (adjoin_le_integralClosure hrA hy)
    have := Algebra.isIntegral_trace (L := FractionRing Λ) (hα.mul hyi)
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [Submodule.mem_one]
    exact ⟨c, hc⟩
  rw [traceForm_dualSubmodule_adjoin Λ (FractionRing Λ) hgen hrA, hd,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨b, hb, hbα⟩ := hmem
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hb
  obtain ⟨W, rfl⟩ := hb
  refine ⟨W, ?_⟩
  rw [← hbα, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]

private theorem cond_core {Λ B : Type} [CommRing Λ] [IsDomain Λ] [IsIntegrallyClosed Λ] [CharZero Λ]
    [CommRing B] (φ : Λ →+* B) (Q : Ideal B) (hQ : Q.IsPrime) (t : B) (g : Λ[X]) (hm : g.Monic)
    (hi : Irreducible (g.map (algebraMap Λ (FractionRing Λ))))
    (hq : ∀ q : Λ[X], q.eval₂ φ t ∈ Q ↔ g ∣ q) (hc : ∀ c : Λ, c ≠ 0 → φ c ∉ Q)
    (a : B) (c : Λ) (hc0 : c ≠ 0) (P : Λ[X]) (haP : φ c * a - P.eval₂ φ t ∈ Q)
    (q : Λ[X]) (hqm : q.Monic) (hqa : q.eval₂ φ a ∈ Q) :
    ∃ W : Λ[X], (derivative g).eval₂ φ t * a - W.eval₂ φ t ∈ Q := by
  haveI := hQ
  haveI : Fact (Irreducible (g.map (algebraMap Λ (FractionRing Λ)))) := ⟨hi⟩
  have hne : g.map (algebraMap Λ (FractionRing Λ)) ≠ 0 := (hm.map _).ne_zero
  haveI : FiniteDimensional (FractionRing Λ) (AdjoinRoot (g.map (algebraMap Λ (FractionRing Λ)))) :=
    (AdjoinRoot.powerBasis hne).finite
  let ι : Λ →+* FractionRing (B ⧸ Q) :=
    (algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q))).comp ((Ideal.Quotient.mk Q).comp φ)
  have h0 : Function.Injective ((Ideal.Quotient.mk Q).comp φ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    exact hc x hx0 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have hι : Function.Injective ι := (IsFractionRing.injective (B ⧸ Q) (FractionRing (B ⧸ Q))).comp h0
  letI : Algebra Λ (FractionRing (B ⧸ Q)) := ι.toAlgebra
  let tF : FractionRing (B ⧸ Q) := algebraMap (B ⧸ Q) _ (Ideal.Quotient.mk Q t)
  have hevx : ∀ (x : B) (p : Λ[X]), aeval (algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q))
      (Ideal.Quotient.mk Q x)) p =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (p.eval₂ φ x)) := by
    intro x p
    rw [aeval_def, hom_eval₂, hom_eval₂]
    rfl
  have hev : ∀ p : Λ[X], aeval tF p =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (p.eval₂ φ t)) := hevx t
  let κ : FractionRing Λ →+* FractionRing (B ⧸ Q) := IsFractionRing.lift hι
  have hκ : ∀ c : Λ, κ (algebraMap Λ (FractionRing Λ) c) = ι c := fun c =>
    IsFractionRing.lift_algebraMap hι c
  have hroot : (g.map (algebraMap Λ (FractionRing Λ))).eval₂ κ tF = 0 := by
    rw [eval₂_map]
    have hk : κ.comp (algebraMap Λ (FractionRing Λ)) = algebraMap Λ (FractionRing (B ⧸ Q)) :=
      RingHom.ext hκ
    rw [hk, ← aeval_def, hev, Ideal.Quotient.eq_zero_iff_mem.2 ((hq g).2 dvd_rfl), map_zero]
  let θ : AdjoinRoot (g.map (algebraMap Λ (FractionRing Λ))) →ₐ[Λ] FractionRing (B ⧸ Q) :=
    { AdjoinRoot.lift κ tF hroot with
      commutes' := fun c => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [IsScalarTower.algebraMap_apply Λ (FractionRing Λ), AdjoinRoot.algebraMap_eq,
          AdjoinRoot.lift_of, hκ]
        rfl }
  have hθr : θ (AdjoinRoot.root _) = tF := AdjoinRoot.lift_root hroot
  have hθinj : Function.Injective θ := θ.toRingHom.injective
  have hθp : ∀ p : Λ[X], θ (aeval (AdjoinRoot.root _) p) =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (p.eval₂ φ t)) := by
    intro p
    rw [← Polynomial.aeval_algHom_apply, hθr, hev]
  let α : AdjoinRoot (g.map (algebraMap Λ (FractionRing Λ))) :=
    aeval (AdjoinRoot.root _) P * (algebraMap Λ _ c)⁻¹
  have hιc : ι c ≠ 0 := by
    rw [ne_eq, ← map_zero ι]
    exact fun h => hc0 (hι h)
  have hca : ι c * algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q a) =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (P.eval₂ φ t)) := by
    have h1 : Ideal.Quotient.mk Q (φ c * a) = Ideal.Quotient.mk Q (P.eval₂ φ t) :=
      Ideal.Quotient.eq.2 haP
    rw [map_mul] at h1
    rw [← h1, map_mul]
    rfl
  have hθα : θ α = algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q a) := by
    simp only [α, map_mul, map_inv₀, hθp, AlgHom.commutes]
    rw [← hca, RingHom.algebraMap_toAlgebra, mul_comm (ι c), mul_assoc, mul_inv_cancel₀ hιc, mul_one]
  have hαint : IsIntegral Λ α := by
    rw [← isIntegral_algHom_iff θ hθinj, hθα]
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, hevx, Ideal.Quotient.eq_zero_iff_mem.2 hqa, map_zero]
  have hr : aeval (AdjoinRoot.root (g.map (algebraMap Λ (FractionRing Λ)))) g = 0 := by
    rw [← aeval_map_algebraMap (FractionRing Λ), AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  obtain ⟨W, hW⟩ := cond_field g hm hi (AdjoinRoot.root _) hr AdjoinRoot.adjoinRoot_eq_top α hαint
  refine ⟨W, ?_⟩
  have h2 := congrArg θ hW
  rw [map_mul, hθp, hθα, hθp, ← map_mul, ← map_mul] at h2
  exact Ideal.Quotient.eq.1 (IsFractionRing.injective (B ⧸ Q) (FractionRing (B ⧸ Q)) h2)

end UpperTheory.V.J

theorem UpperTheory.V.J.cond :
    UpperTheory.V.J.Cond := by
  intro O Λ B _ _ _ _ _ _ _ _ lam J t s g h i a
  obtain ⟨hp, hq, hc⟩ := UpperTheory.V.J.cmpPrime O Λ B lam J t s g h i
  have hJ : J ≤ UpperTheory.V.J.cmp lam J t g i := fun x hx => by
    simp only [UpperTheory.V.J.cmp, Submodule.mem_colon_singleton]
    exact J.mul_mem_right _ hx
  obtain ⟨c, hc0, P, hP⟩ := h.prim a
  obtain ⟨q, hqm, hqa⟩ := h.int a
  exact UpperTheory.V.J.cond_core (lam : Λ →+* B) _ hp t (g i) (h.monic i) (h.irr i) (hq) hc a c hc0 P
    (hJ hP) q hqm (hJ hqa)
