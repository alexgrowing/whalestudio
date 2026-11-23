import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

namespace GlobalTheory.TateLocFree

theorem exists_place_decomp : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C), ∃ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 ∧ ∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j) := by
  intro p _ C _ _ _ v O _ _ _ E _ _ _ P φ
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (embO P.integers φ)
  obtain ⟨hdom, hpid, -⟩ := GlobalTheory.PlaceMono.place_monogenic p (𝓞 E) w
  let A := ℤ_[p] ⊗[ℤ] 𝓞 E
  let e : A := w.e
  let I : Ideal A := Ideal.span {1 - e}
  letI : Module A P.T := Module.compHom P.T (tensorAction P.actT).toRingHom
  have hsmul : ∀ (a : A) (t : P.T), a • t = tensorAction P.actT a t := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[p] A P.T := ⟨fun c a t => by
    rw [hsmul, hsmul, map_smul]; rfl⟩
  let M : Submodule A P.T := LinearMap.range (LinearMap.lsmul A P.T e)
  have hee : e * e = e := w.idem
  have hfix : ∀ m ∈ M, e • m = m := by
    rintro _ ⟨t, rfl⟩
    change e • e • t = e • t
    rw [smul_smul, hee]
  have htor : Module.IsTorsionBySet A M I := by
    intro x a
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 a.2
    apply Subtype.ext
    rw [Submodule.coe_smul, ← hc, mul_smul, sub_smul, one_smul, hfix _ x.2, sub_self, smul_zero,
      Submodule.coe_zero]
  letI : Module (A ⧸ I) M := htor.module
  haveI : IsScalarTower A (A ⧸ I) M := htor.isScalarTower
  haveI : IsDomain (A ⧸ I) := hdom
  haveI : IsPrincipalIdealRing (A ⧸ I) := hpid
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[p] A
  haveI : Module.Finite A P.T := Module.Finite.of_restrictScalars_finite ℤ_[p] A P.T
  haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite A (A ⧸ I) M
  haveI : Module.Finite ℤ_[p] (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] I)
  haveI : Module.IsTorsionFree (A ⧸ I) M := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[p]) hr
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
    have h1 : (algebraMap ℤ_[p] A c) • (m : P.T) = 0 := by
      have : (algebraMap ℤ_[p] (A ⧸ I) c) • m = 0 := by rw [← hs, mul_smul, h, smul_zero]
      have h2 : (((algebraMap ℤ_[p] (A ⧸ I) c) • m : M) : P.T) = 0 := by rw [this]; rfl
      exact h2
    rw [algebraMap_smul] at h1
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left hc0
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A ⧸ I) (M := M)
  have hI : (I : Submodule A A) ≤ LinearMap.ker (LinearMap.mulLeft A e) := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
    linear_combination c * (1 - hee)
  let liftE : (A ⧸ I) →ₗ[A] A := Submodule.liftQ I (LinearMap.mulLeft A e) hI
  have hlift : ∀ (r : A ⧸ I) (m : M), liftE r • (m : P.T) = ((r • m : M) : P.T) := by
    intro r m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : liftE (Ideal.Quotient.mk I x) = e * x := Submodule.liftQ_apply _ _ _
    rw [h1, mul_comm, mul_smul, hfix _ m.2]
    rfl
  let emap : P.T →ₗ[A] M := (LinearMap.lsmul A P.T e).rangeRestrict
  let L : Fin n → (P.T →ₗ[A] A) := fun j => liftE ∘ₗ ((b.coord j).restrictScalars A) ∘ₗ emap
  refine ⟨n, fun j => (b j : P.T), fun j => (L j).restrictScalars ℤ_[p], e, ?_, hw, ?_⟩
  · intro j a t
    have h1 : P.actT a t = (1 ⊗ₜ a : A) • t := by
      rw [hsmul, tensorAction_tmul, one_smul]
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, h1, map_smul, smul_eq_mul]
  · intro t
    have h0 : ((emap t : M) : P.T) = e • t := rfl
    rw [← hsmul, ← h0, ← b.sum_repr (emap t), Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsmul, ← hlift]
    rfl
end GlobalTheory.TateLocFree
