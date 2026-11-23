import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBasisTraceLogNormStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat

namespace LieEigenProjections

section Proj

variable {E K U : Type} [Field E] [NumberField E] [Field K] [AddCommGroup U] [Module K U]

theorem eigProj_rho (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (a : 𝓞 E) (u : U) :
    HT.eigProj ρ σ (ρ a u) = σ (a : E) • HT.eigProj ρ σ u := by
  have h1 : HT.eigProj ρ σ (ρ a u) = ρ a (HT.eigProj ρ σ u) := by
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  rw [h1]
  exact HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ σ u) a

theorem eigProj_eq_zero (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (r : 𝓞 E) (s : K)
    (hs : s ≠ σ (r : E)) {u : U} (hu : ρ r u = s • u) : HT.eigProj ρ σ u = 0 := by
  have h1 := eigProj_rho ρ σ r u
  rw [hu, map_smul] at h1
  have h2 : (s - σ (r : E)) • HT.eigProj ρ σ u = 0 := by rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hs)

theorem eigProj_eq_sum [CharZero K] (hcard : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (r : 𝓞 E) {f : ℕ} (b : Fin f → 𝓞 E) (b' : Fin f → E)
    (hb : ∀ σ' : E →+* K, σ (r : E) = σ' (r : E) →
      (σ = σ' → ∑ k, σ (b' k) * σ' (b k : E) = 1) ∧ (σ ≠ σ' → ∑ k, σ (b' k) * σ' (b k : E) = 0))
    {u : U} (hu : ρ r u = σ (r : E) • u) :
    HT.eigProj ρ σ u = ∑ k, σ (b' k) • ρ (b k) u := by
  classical
  haveI : Finite (E →+* K) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact Module.finrank_pos.ne')
  haveI : Fintype (E →+* K) := Fintype.ofFinite _
  have hsum : ∑ τ : E →+* K, HT.eigProj ρ τ = 1 :=
    HT.sum_eigProj_eq_one K U E ρ (by rw [← Nat.card_eq_fintype_card, hcard])
  have hexp : u = ∑ τ : E →+* K, HT.eigProj ρ τ u := by
    have := congrArg (fun T : Module.End K U => T u) hsum
    simpa [LinearMap.sum_apply] using this.symm
  have hterm : ∀ τ : E →+* K,
      ∑ k, σ (b' k) • ρ (b k) (HT.eigProj ρ τ u) = if τ = σ then HT.eigProj ρ σ u else 0 := by
    intro τ
    have hact : ∀ k, ρ (b k) (HT.eigProj ρ τ u) = τ (b k : E) • HT.eigProj ρ τ u := fun k =>
      HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ τ u) (b k)
    simp only [hact, smul_smul]
    rw [← Finset.sum_smul]
    by_cases h : τ = σ
    · subst h
      rw [(hb τ rfl).1 rfl, one_smul, if_pos rfl]
    · rw [if_neg h]
      by_cases hr : σ (r : E) = τ (r : E)
      · rw [(hb τ hr).2 (Ne.symm h), zero_smul]
      · rw [eigProj_eq_zero ρ τ r (σ (r : E)) hr hu, smul_zero]
  conv_rhs => rw [hexp]
  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [hterm]
  simp

end Proj

end LieEigenProjections

section Core

variable {E K U : Type} [Field E] [NumberField E] [Field K] [CharZero K] [AddCommGroup U] [Module K U]

theorem core (V : Subring K) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (r : 𝓞 E)
    (hr : σ (r : E) ≠ 0) {I J : Type} [Fintype I] [Fintype J] (u : I → U) (u' : J → U) {f : ℕ}
    (b : Fin f → 𝓞 E) (m : Fin f → K) (δ : K) (k₀ : Fin f)
    (hm : ∀ a, HT.eigProj ρ σ (u a) = ∑ k, m k • ρ (b k) (u a))
    (hu' : ∀ a, ρ r (u' a) = -σ (r : E) • u' a)
    (hlin : LinearIndependent K (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
      (fun q : J × Fin f => ρ (b q.2) (u' q.1))))
    (hδ0 : δ ≠ 0) (hk₀ : m k₀ ≠ 0) (hVm : ∀ k, δ * m k ∈ V)
    (hVx : ∀ x : K, x * m k₀ ∈ V → x * δ⁻¹ ∈ V) :
    LinearIndependent K (fun a => δ • HT.eigProj ρ σ (u a)) ∧
      Submodule.span V (Set.range (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
        (fun q : J × Fin f => ρ (b q.2) (u' q.1)))) ⊓ (HT.eigSp ρ σ).restrictScalars V =
      Submodule.span V (Set.range fun a => δ • HT.eigProj ρ σ (u a)) := by
  classical
  have hneg : -σ (r : E) ≠ σ (r : E) := by
    intro h
    have h2 : (2 : K) * σ (r : E) = 0 := by linear_combination -h
    exact hr ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  have hker : ∀ a k, HT.eigProj ρ σ (ρ (b k) (u' a)) = 0 := by
    intro a k
    refine LieEigenProjections.eigProj_eq_zero ρ σ r (-σ (r : E)) hneg ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hu', map_smul]
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hs : ∑ q : I × Fin f, (g q.1 * δ * m q.2) •
        (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
          (fun q : J × Fin f => ρ (b q.2) (u' q.1)) ∘ Sum.inl) q = 0 := by
      rw [Fintype.sum_prod_type, ← hg]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hm, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change (g a * δ * m k) • ρ (b k) (u a) = g a • δ • m k • ρ (b k) (u a)
      rw [smul_smul, smul_smul]
    have hl := Fintype.linearIndependent_iff.1 (hlin.comp Sum.inl Sum.inl_injective) _ hs (a, k₀)
    simpa [hδ0, hk₀] using hl
  · rintro z ⟨hz1, hz2⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hz1
    have hz3 : z ∈ HT.eigSp ρ σ := hz2
    have heig := HT.LatBasic.eigProj_of_mem hz3
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr, Subring.smul_def] at hc
    set x : I → K := fun a => ∑ k, (c (Sum.inl (a, k)) : K) * σ (b k : E) with hx
    have hez : z = ∑ a, x a • HT.eigProj ρ σ (u a) := by
      conv_lhs => rw [← heig, ← hc]
      rw [map_add, map_sum, map_sum]
      have h0 : ∑ q : J × Fin f, HT.eigProj ρ σ ((c (Sum.inr q) : K) • ρ (b q.2) (u' q.1)) = 0 :=
        Finset.sum_eq_zero fun q _ => by rw [map_smul, hker, smul_zero]
      rw [h0, add_zero, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hx, Finset.sum_smul, map_smul, LieEigenProjections.eigProj_rho, smul_smul]
    have hcoef : ∀ a k, (c (Sum.inl (a, k)) : K) = x a * m k := by
      have hz0 : ∑ i, ((c i : K) - Sum.elim (fun q : I × Fin f => x q.1 * m q.2)
          (fun _ : J × Fin f => (0 : K)) i) • (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
            (fun q : J × Fin f => ρ (b q.2) (u' q.1))) i = 0 := by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, sub_zero, sub_smul, Finset.sum_sub_distrib]
        have h1 : ∑ q : I × Fin f, (x q.1 * m q.2) • ρ (b q.2) (u q.1) = z := by
          rw [hez, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hm, Finset.smul_sum]
          simp only [smul_smul]
        rw [h1, sub_add_eq_add_sub, hc, sub_self]
      intro a k
      have := Fintype.linearIndependent_iff.1 hlin _ hz0 (Sum.inl (a, k))
      simpa [sub_eq_zero] using this
    have hy : ∀ a, x a * δ⁻¹ ∈ V := fun a => hVx _ (by
      rw [← hcoef a k₀]; exact (c (Sum.inl (a, k₀))).2)
    rw [hez]
    refine Submodule.sum_mem _ fun a _ => ?_
    have h1 : x a • HT.eigProj ρ σ (u a) =
        (⟨x a * δ⁻¹, hy a⟩ : V) • (δ • HT.eigProj ρ σ (u a)) := by
      rw [Subring.smul_def, smul_smul]
      simp [hδ0]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · change δ • HT.eigProj ρ σ (u a) ∈ Submodule.span V _
      rw [hm, Finset.smul_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      have h1 : δ • m k • ρ (b k) (u a) = (⟨δ * m k, hVm k⟩ : V) •
          (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
            (fun q : J × Fin f => ρ (b q.2) (u' q.1))) (Sum.inl (a, k)) := by
        rw [Subring.smul_def, smul_smul]
        rfl
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · exact (HT.eigSp ρ σ).smul_mem δ (HT.LatBasic.eigProj_mem ρ σ _)

end Core

theorem eigSub_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) (K : Type) [Field K] [CharZero K] (j : K →+* ℂ_[ℓ]) (V : Subring K) (U : Type) [AddCommGroup U] [Module K U] (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I J : Type) [Fintype I] [Fintype J] (u : I → U) (u' : J → U) (f : ℕ) (b : Fin f → 𝓞 E) (δ : K), (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) → Nat.card (E →+* K) = Module.finrank ℚ E → IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b → (∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a) → (∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a) → LinearIndependent K (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1))) → δ ≠ 0 → Real.log ‖j δ‖ = logIdeal ((j.comp σ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (σ (H.rt : E))‖ → LinearIndependent K (fun a => δ • HT.eigProj ρ σ (u a)) ∧ Submodule.span V (Set.range (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1)))) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range fun a => δ • HT.eigProj ρ σ (u a)) := by
  intro E _ _ _ H ℓ K _ _ j V U _ _ ρ σ I J _ _ u u' f b δ hV hcard hloc hu hu' hlin hδ0 hδ
  obtain ⟨b', hb', hj⟩ := GlobalTheory.T.dual_basis_trace_log_norm E H ℓ f b hloc
  obtain ⟨hpos, hlog⟩ := hj (j.comp σ)
  simp only [RingHom.comp_apply] at hpos hlog
  have hδp : 0 < ‖j δ‖ := norm_pos_iff.2 ((map_ne_zero j).2 hδ0)
  have hprod : (⨆ k, ‖j (σ (b' k))‖) * ‖j δ‖ = 1 := by
    refine Real.eq_one_of_pos_of_log_eq_zero (mul_pos hpos hδp) ?_
    rw [Real.log_mul hpos.ne' hδp.ne', hlog, hδ]
    ring
  haveI : Nonempty (Fin f) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Real.iSup_of_isEmpty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨k₀, hk₀⟩ := exists_eq_ciSup_of_finite (f := fun k => ‖j (σ (b' k))‖)
  have hle : ∀ k, ‖j (σ (b' k))‖ ≤ ⨆ k, ‖j (σ (b' k))‖ := fun k =>
    le_ciSup (Set.finite_range fun k => ‖j (σ (b' k))‖).bddAbove k
  have hr : σ (H.rt : E) ≠ 0 := by
    intro h
    have h1 := congrArg (fun y : 𝓞 E => σ (y : E)) H.rt_sq
    simp only [map_pow, map_neg, h, map_natCast] at h1
    have h2 : (H.rt : E) = 0 := by simpa using h
    have h3 : (H.d : K) = 0 := by
      have : σ (((H.rt ^ 2 : 𝓞 E)) : E) = 0 := by simp [h2]
      rw [H.rt_sq] at this
      simpa using this
    exact H.d_prime.ne_zero (by exact_mod_cast h3)
  refine core V ρ σ H.rt hr u u' b (fun k => σ (b' k)) δ k₀ ?_ hu' hlin hδ0 ?_ ?_ ?_
  · exact fun a => LieEigenProjections.eigProj_eq_sum hcard ρ σ H.rt b b' (fun σ' h => hb' K σ σ' h) (hu a)
  · intro h0
    have h0' : σ (b' k₀) = 0 := h0
    have : ‖j (σ (b' k₀))‖ = 0 := by rw [h0', map_zero, norm_zero]
    rw [← hk₀, this] at hpos
    exact lt_irrefl _ hpos
  · intro k
    refine (hV _).1 ?_
    rw [map_mul, norm_mul, mul_comm]
    calc ‖j (σ (b' k))‖ * ‖j δ‖ ≤ (⨆ k, ‖j (σ (b' k))‖) * ‖j δ‖ :=
          mul_le_mul_of_nonneg_right (hle k) hδp.le
      _ = 1 := hprod
  · intro x hx
    have h1 := (hV _).2 hx
    rw [map_mul, norm_mul, hk₀] at h1
    refine (hV _).1 ?_
    rw [map_mul, norm_mul, map_inv₀, norm_inv]
    have h2 : ‖j δ‖⁻¹ = ⨆ k, ‖j (σ (b' k))‖ := by
      field_simp
      linarith
    rw [h2]
    exact h1

end GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat
