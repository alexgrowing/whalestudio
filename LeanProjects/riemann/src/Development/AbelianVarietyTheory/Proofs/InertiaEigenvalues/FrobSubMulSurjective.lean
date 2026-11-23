import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRingStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.ArtinSchreierWitt

open Polynomial

theorem frob_sub_mul_surjective (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p]
    [PerfectRing k p] (h : ∀ c y : k, ∃ x : k, x ^ p - c * x = y) (c y : WittVector p k) :
    ∃ β : WittVector p k, WittVector.frobenius β - c * β = y := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) (WittVector p k) := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := WittVector p k), Ideal.map_span,
      Set.image_singleton, map_natCast]
    infer_instance
  let f : WittVector p k →ₗ[ℤ] WittVector p k :=
    (WittVector.frobenius (p := p) (R := k)).toAddMonoidHom.toIntLinearMap
      - (AddMonoidHom.mulLeft c).toIntLinearMap
  have hf : ∀ β, f β = WittVector.frobenius β - c * β := fun β => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    obtain ⟨x, hx⟩ := h (c.coeff 0) (g.coeff 0)
    refine ⟨WittVector.teichmuller p x, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have h0 : (WittVector.frobenius (WittVector.teichmuller p x)
        - c * WittVector.teichmuller p x - g) ∈ Ideal.span {(p : WittVector p k)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_sub, map_mul]
      simp only [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
        WittVector.teichmuller_coeff_zero]
      rw [hx, sub_self]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h0
    rw [hu]
    have : (p : WittVector p k) * u = (p : ℤ) • u := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨β, hβ⟩ := hs y
  exact ⟨β, (hf β).symm.trans hβ⟩

theorem monic_as (p : ℕ) [hp : Fact p.Prime] {k : Type} [CommRing k] [Nontrivial k] (c y : k) :
    (X ^ p - (C c * X + C y) : k[X]).Monic ∧ (X ^ p - (C c * X + C y) : k[X]).degree = p := by
  have h1 : (C c * X + C y : k[X]).degree < (p : WithBot ℕ) :=
    lt_of_le_of_lt degree_linear_le (by exact_mod_cast hp.out.one_lt)
  refine ⟨monic_X_pow_sub h1, ?_⟩
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]

theorem exists_root_field (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K]
    (c y : K) : ∃ x : K, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ p - (C c * X + C y) : K[X]) (by
    rw [(monic_as p c y).2]; exact_mod_cast hp.out.ne_zero)
  refine ⟨x, ?_⟩
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_add, eval_mul, eval_C] at hx
  linear_combination hx

theorem exists_root_ring (p : ℕ) [hp : Fact p.Prime] {O K : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [IsAlgClosed K]
    (c y : O) : ∃ x : O, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := exists_root_field p (algebraMap O K c) (algebraMap O K y)
  have hi : IsIntegral O x := by
    refine ⟨X ^ p - (C c * X + C y), (monic_as p c y).1, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    linear_combination hx
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨z, IsFractionRing.injective O K ?_⟩
  rw [map_sub, map_pow, map_mul, hx]

theorem fixed_frob (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (b : WittVector p K)
    (hb : WittVector.map (frobenius K p) b = b) : ∃ z : ℤ_[p], b = zlW p K z := by
  have h : ∀ n, ∃ a : ZMod p, ZMod.castHom (dvd_refl p) K a = b.coeff n := by
    intro n
    have h1 : (b.coeff n) ^ p = b.coeff n := by
      have := congrArg (fun w => WittVector.coeff w n) hb
      simpa [WittVector.map_coeff, frobenius_def] using this
    have h2 := (Subfield.mem_bot_iff_pow_eq_self K p).2 h1
    have h3 : (⊥ : Subfield K) ≤ (ZMod.castHom (dvd_refl p) K).fieldRange := bot_le
    exact h3 h2
  choose a ha using h
  refine ⟨WittVector.equiv p (WittVector.mk p a), ?_⟩
  ext n
  simp [zlW, WittVector.map_coeff, ← ha]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∀ y : WCb l, ∃ b, frobW l b - b = y) ∧ (∀ b : WCb l, frobW l b = b → ∃ z : ℤ_[l], b = algebraMap ℤ_[l] (WCb l) z) ∧ ∀ (c p : Ainf l), ∃ β : Ainf l, WittVector.frobenius β - c * β = p := by
  intro l _
  obtain ⟨hK, hV⟩ := GlobalTheory.T.isAlgClosed_tiltField_and_valuationRing l
  refine ⟨fun y => ?_, fun b hb => fixed_frob l (Cb l) b hb, fun c p => ?_⟩
  · obtain ⟨β, hβ⟩ := frob_sub_mul_surjective l (Cb l) (exists_root_field l) 1 y
    refine ⟨β, ?_⟩
    rw [one_mul, WittVector.frobenius_eq_map_frobenius] at hβ
    exact hβ
  · exact frob_sub_mul_surjective l (OCb l) (exists_root_ring l (K := Cb l)) c p

end GlobalTheory.ArtinSchreierWitt
