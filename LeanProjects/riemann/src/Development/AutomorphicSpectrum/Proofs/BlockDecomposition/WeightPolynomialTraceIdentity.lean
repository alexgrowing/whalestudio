import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparison
open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope

noncomputable section

namespace GlobalTheory.CompanionTheory.RealCount.Tope.Ident

variable {n : ℕ}

theorem chr_ofAdd (z : Fin n → ℂˣ) (μ : Fin n → ℤ) :
    chr z (Multiplicative.ofAdd μ) = ∏ a, ((z a : ℂ) ^ μ a) := by
  simp [chr, Units.val_zpow_eq_zpow_val]

theorem evL_single (z : Fin n → ℂˣ) (μ : Fin n → ℤ) (c : ℂ) :
    evL z (AddMonoidAlgebra.single μ c) = c * ∏ a, ((z a : ℂ) ^ μ a) := by
  rw [evL, AddMonoidAlgebra.lift_single, chr_ofAdd, smul_eq_mul]

theorem lp_eq_sum (f : LP n) :
    f = ∑ m ∈ f.coeff.support, AddMonoidAlgebra.single m (f.coeff m) := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.coeff_sum]
  simp only [AddMonoidAlgebra.coeff_single]
  exact (Finsupp.sum_single f.coeff).symm

theorem evL_eq_sum (z : Fin n → ℂˣ) (f : LP n) :
    evL z f = ∑ m ∈ f.coeff.support, f.coeff m * GlobalTheory.CompanionTheory.CoefId.mon m (fun a => (z a : ℂ)) := by
  conv_lhs => rw [lp_eq_sum f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [evL_single]; rfl

theorem evL_cPoly (z : Fin n → ℂˣ) (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) :
    evL z (cPoly s c) = ∑ μ ∈ s, (∏ a, ((z a : ℂ) ^ μ a)) * c μ := by
  rw [cPoly, map_sum]
  exact Finset.sum_congr rfl fun μ _ => by rw [evL_single, mul_comm]

theorem eq_zero_of_evL (f : LP n)
    (h : ∀ z : Fin n → ℂˣ, (∀ a, ‖(z a : ℂ)‖ = 1) → Function.Injective (fun a => (z a : ℂ) ^ 2) → evL z f = 0) :
    f = 0 := by
  have H := GlobalTheory.CompanionTheory.CoefId.coeff_zero_of_torus f.coeff.support (fun m => f.coeff m) (fun z hz hi => by
    have h0 : ∀ a, z a ≠ 0 := fun a e => by simpa [e] using hz a
    have := h (fun a => Units.mk0 (z a) (h0 a)) (fun a => by simpa using hz a) (by simpa using hi)
    rw [evL_eq_sum] at this
    simpa using this)
  apply AddMonoidAlgebra.coeff_injective
  ext m
  by_cases hm : m ∈ f.coeff.support
  · simpa using H m hm
  · simpa using hm

theorem evL_frL (z : Fin n → ℂˣ) (f : LP n) : evL z (frL n f) = evL (fun a => z a ^ 2) f := by
  have : (evL z).comp (frL n) = evL (fun a => z a ^ 2) := by
    refine AddMonoidAlgebra.algHom_ext (fun μ => ?_) (Subsingleton.elim _ _)
    simp only [AlgHom.comp_apply, frL, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    rw [evL_single, evL_single]
    simp only [one_mul, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Units.val_pow_eq_pow_val]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← zpow_natCast, ← _root_.zpow_mul]; push_cast; ring_nf
  exact congrArg (fun φ : LP n →ₐ[ℂ] ℂ => φ f) this

theorem evL_pPL (z : Fin n → ℂˣ) : evL z (pPL n) = ∏ a, ∏ b, (1 + (z a : ℂ) / z b) := by
  simp only [pPL, map_prod, map_add, map_one, evL_single, one_mul]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  congr 1
  have key : ∀ a : Fin n, ∏ c, (z c : ℂ) ^ ((Pi.single a (1 : ℤ) : Fin n → ℤ) c) = z a := fun a => by
    rw [Finset.prod_eq_single a (fun c _ hc => by simp [Pi.single_apply, hc]) (fun h => absurd (Finset.mem_univ a) h)]
    simp
  simp only [Pi.sub_apply, zpow_sub₀ (Units.ne_zero _), Finset.prod_div_distrib, key]

end GlobalTheory.CompanionTheory.RealCount.Tope.Ident

namespace GlobalTheory.CompanionTheory.RealCount.Tope.Ident

variable {n : ℕ}

theorem evL_altL (z : Fin n → ℂˣ) (m : Fin n → ℤ) :
    evL z (altL m) = (Matrix.of fun i j : Fin n => (z i : ℂ) ^ m j).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply', altL, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, evL_single, one_mul, smul_eq_mul]
  simp [Matrix.transpose_apply, Matrix.of_apply]

theorem det_stair_ne_zero {t : Fin n → ℂ} (ht : Function.Injective t) :
    (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det ≠ 0 := by
  have e : (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde t).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [e, Matrix.det_permute']
  exact mul_ne_zero (by simp) (Matrix.det_vandermonde_ne_zero_iff.2 ht)

theorem evL_altL_delZ (z : Fin n → ℂˣ) :
    evL z (altL (delZ n)) = (Matrix.of fun i j : Fin n => (z i : ℂ) ^ (n - 1 - (j : ℕ))).det := by
  rw [evL_altL]
  congr 1

theorem weylChar_evL (lam : Fin n → ℤ) (z : Fin n → ℂˣ) :
    weylChar lam (fun a => (z a : ℂ)) = evL z (altL (lam + delZ n)) / evL z (altL (delZ n)) := by
  rw [weylChar, evL_altL_delZ, evL_altL]
  congr 2

theorem conj_weylChar (lam : Fin n → ℤ) (γ : Fin n → ℂ) :
    conj (weylChar lam γ) = weylChar lam (fun a => conj (γ a)) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀]

end GlobalTheory.CompanionTheory.RealCount.Tope.Ident

namespace GlobalTheory.CompanionTheory.RealCount.Tope.Ident

variable {n : ℕ}

theorem trace_dualT (E : KMod n) (A : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E A : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      LinearMap.trace ℂ E.V (A : E.V →ₗ[ℂ] E.V) := by
  let e : Module.Dual ℂ E.V ≃ₗ[ℂ] (E.V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap
  have h : (dualT E A : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      e.conj (Module.Dual.transpose (R := ℂ) (A : E.V →ₗ[ℂ] E.V)) := by
    ext ξ x
    simp [e, dualT, LinearEquiv.conj_apply, Module.Dual.transpose_apply]
  rw [h, LinearMap.trace_conj', LinearMap.trace_transpose']

end GlobalTheory.CompanionTheory.RealCount.Tope.Ident

namespace GlobalTheory.CompanionTheory.RealCount.Tope.Ident

variable {n : ℕ}

theorem dualT_mapsTo (E : KMod n) (T' : E.V →L[ℂ] E.V) (hT : ∀ k, T' * E.ρ k = E.ρ k * T') (μ : Fin n → ℤ) :
    ∀ ξ ∈ wtDual E μ, (dualT E T' : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ ∈ wtDual E μ := by
  intro ξ hξ k z hk
  have e1 : (dualT E T' : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ = ξ ∘L T' := rfl
  rw [e1, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def, hT k⁻¹, ContinuousLinearMap.mul_def,
    ← ContinuousLinearMap.comp_assoc, hξ k z hk, ContinuousLinearMap.smul_comp]

theorem dualT_wt (E : KMod n) (T' : E.V →L[ℂ] E.V) (μ : Fin n → ℤ)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) (ξ : E.V →L[ℂ] ℂ)
    (hξ : ξ ∈ wtDual E μ) :
    (dualT E (E.ρ k⁻¹ * T') : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ =
      (∏ a, z a ^ μ a) • (dualT E T' : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ := by
  change ξ ∘L (E.ρ k⁻¹ * T') = (∏ a, z a ^ μ a) • (ξ ∘L T')
  rw [ContinuousLinearMap.mul_def, ← ContinuousLinearMap.comp_assoc, hξ k z hk, ContinuousLinearMap.smul_comp]

theorem trace_restrict_eq (E : KMod n) (T' : E.V →L[ℂ] E.V) (hT : ∀ k, T' * E.ρ k = E.ρ k * T') (μ : Fin n → ℤ)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z)
    (hf : Set.MapsTo (dualT E (E.ρ k⁻¹ * T') : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) (wtDual E μ) (wtDual E μ)) :
    LinearMap.trace ℂ (wtDual E μ) (LinearMap.restrict _ hf) =
      (∏ a, z a ^ μ a) * trOn (wtDual E μ) (dualT E T' : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) := by
  have hg := dualT_mapsTo E T' hT μ
  have e : LinearMap.restrict _ hf = (∏ a, z a ^ μ a) • LinearMap.restrict _ hg := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨ξ, hξ⟩ := x
    simp only [LinearMap.restrict_apply, LinearMap.smul_apply, SetLike.val_smul]
    exact dualT_wt E T' μ k z hk ξ hξ
  rw [trOn, dif_pos hg, e, map_smul, smul_eq_mul]

theorem trace_decomp (E : KMod n) (T' : E.V →L[ℂ] E.V) (hT : ∀ k, T' * E.ρ k = E.ρ k * T')
    (htop : (⨆ μ, wtDual E μ) = ⊤) (hind : iSupIndep (wtDual E)) (s : Finset (Fin n → ℤ))
    (hs : ∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s) (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) :
    LinearMap.trace ℂ E.V ((E.ρ k⁻¹ * T' : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
      ∑ μ ∈ s, (∏ a, z a ^ μ a) * trOn (wtDual E μ) (dualT E T' : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) := by
  classical
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hfin : {μ | wtDual E μ ≠ ⊥}.Finite := (s.finite_toSet).subset fun μ hμ => hs μ hμ
  have hf : ∀ μ, Set.MapsTo (dualT E (E.ρ k⁻¹ * T') : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))
      (wtDual E μ) (wtDual E μ) := fun μ ξ hξ => by
    rw [SetLike.mem_coe, dualT_wt E T' μ k z hk ξ hξ]
    exact Submodule.smul_mem _ _ (dualT_mapsTo E T' hT μ ξ hξ)
  rw [← trace_dualT, LinearMap.trace_eq_sum_trace_restrict' hint hfin hf]
  simp_rw [trace_restrict_eq E T' hT _ k z hk]
  refine Finset.sum_subset (fun μ hμ => hs μ (by simpa using hμ)) fun μ _ hμ => ?_
  have h0 : wtDual E μ = ⊥ := by simpa using hμ
  rw [h0, trOn_bot, mul_zero]

end GlobalTheory.CompanionTheory.RealCount.Tope.Ident

namespace GlobalTheory.CompanionTheory.RealCount.Tope.Ident

variable {n : ℕ}

theorem exists_diag_unitary (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    ∃ k : Matrix.unitaryGroup (Fin n) ℂ, k.1 = diagonal z ∧
      (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = diagonal (fun a => conj (z a)) := by
  have hc : (diagonal z)ᴴ = diagonal (fun a => conj (z a)) := by
    rw [Matrix.diagonal_conjTranspose]; rfl
  have hm : diagonal z ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hc, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]
    simp
  refine ⟨⟨diagonal z, hm⟩, rfl, ?_⟩
  rw [← hc, ← Matrix.star_eq_conjTranspose]
  rfl

theorem conj_eq_inv {w : ℂ} (hw : ‖w‖ = 1) : conj w = w⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]
  simp

theorem prod_conj (z : Fin n → ℂˣ) (hz : ∀ a, ‖(z a : ℂ)‖ = 1) :
    ∏ a, ∏ b, (1 + conj (z a : ℂ) / conj (z b : ℂ)) = ∏ a, ∏ b, (1 + (z a : ℂ) / z b) := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun a _ => ?_
  rw [conj_eq_inv (hz a), conj_eq_inv (hz b), inv_div_inv]

theorem lefK_laurent_ident {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) (hL : IsLefK lam E T)
    (htop : (⨆ μ, wtDual E μ) = ⊤) (hind : iSupIndep (wtDual E)) (s : Finset (Fin n → ℤ))
    (hs : ∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s) :
    cPoly s (fun μ => trOn (wtDual E μ) (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * altL (delZ n) ^ 2 =
          pPL n * altL (lam + delZ n) ^ 2 ∧
        cPoly s (fun μ => trOn (wtDual E μ) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * frL n (altL (delZ n)) =
          pPL n * frL n (altL (lam + delZ n)) := by
  have key : ∀ z : Fin n → ℂˣ, (∀ a, ‖(z a : ℂ)‖ = 1) → Function.Injective (fun a => (z a : ℂ) ^ 2) →
      evL z (cPoly s (fun μ => trOn (wtDual E μ) (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)))) =
          evL z (pPL n) * weylChar lam (fun a => (z a : ℂ)) ^ 2 ∧
        evL z (cPoly s (fun μ => trOn (wtDual E μ) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)))) =
          evL z (pPL n) * weylChar lam (fun a => (z a : ℂ) ^ 2) := by
    intro z hz hi
    obtain ⟨k, hk, hki⟩ := exists_diag_unitary (fun a => (z a : ℂ)) hz
    have hi' : Function.Injective (fun a => conj (z a : ℂ) ^ 2) := by
      intro a b hab
      apply hi
      have := congrArg conj hab
      simpa using this
    obtain ⟨h1, h2⟩ := hL.2.2 k⁻¹ _ hki hi'
    have t1 := trace_decomp E 1 (fun k => by rw [one_mul, mul_one]) htop hind s hs k _ hk
    have t2 := trace_decomp E T hL.1 htop hind s hs k _ hk
    rw [mul_one] at t1
    rw [evL_cPoly, evL_cPoly, evL_pPL]
    refine ⟨?_, ?_⟩
    · rw [← t1, h1, prod_conj z hz, conj_weylChar]
      simp
    · rw [← t2, h2, prod_conj z hz, conj_weylChar]
      simp
  have hΔ : ∀ z : Fin n → ℂˣ, Function.Injective (fun a => (z a : ℂ)) → evL z (altL (delZ n)) ≠ 0 := by
    intro z hz
    rw [evL_altL_delZ]
    exact det_stair_ne_zero hz
  refine ⟨sub_eq_zero.1 (eq_zero_of_evL _ fun z hz hi => ?_), sub_eq_zero.1 (eq_zero_of_evL _ fun z hz hi => ?_)⟩
  · have hinj : Function.Injective (fun a => (z a : ℂ)) := fun a b h => hi (by simp only [h])
    have hd := hΔ z hinj
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, (key z hz hi).1, weylChar_evL]
    field_simp
    ring
  · have hinj : Function.Injective (fun a => ((z a ^ 2 : ℂˣ) : ℂ)) := by simpa using hi
    have hd := hΔ _ hinj
    rw [map_sub, map_mul, map_mul, evL_frL, evL_frL, (key z hz hi).2]
    have e := weylChar_evL lam (fun a => z a ^ 2)
    simp only [Units.val_pow_eq_pow_val] at e hd ⊢
    rw [e]
    field_simp
    ring

end GlobalTheory.CompanionTheory.RealCount.Tope.Ident
