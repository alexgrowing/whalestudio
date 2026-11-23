import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizationAwayFromPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTriangularDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorIntegralCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentValuationBoundStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigArith

open Matrix

section Proj

variable {E : Type} [Field E] [NumberField E] {F : Type} [Field F] [CharZero F] {N : ℕ}
  (A : 𝓞 E →+* Matrix (Fin N) (Fin N) F)

def prj (τ : E →+* F) : Matrix (Fin N) (Fin N) F :=
  ∑ k, τ ((integralBasis E).traceDual k) • A (RingOfIntegers.basis E k)

theorem exists_diff_dual (E : Type) [Field E] [NumberField E] : ∃ (δ : 𝓞 E) (c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E),
    δ ≠ 0 ∧ ∀ k, algebraMap (𝓞 E) E (c k) = algebraMap (𝓞 E) E δ * (integralBasis E).traceDual k := by
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
  choose c hc using fun k => GlobalTheory.ColengthDifferent.exists_mul_traceDual hδ k
  exact ⟨δ, c, hδ0, hc⟩

omit [CharZero F] in
theorem act_prj (τ : E →+* F) (a : 𝓞 E) : A a * prj A τ = τ (a : E) • prj A τ := by
  obtain ⟨δ, c, hδ0, hc⟩ := exists_diff_dual E
  have h := GlobalTheory.ColengthDifferent.mul_proj (τ.comp (algebraMap (𝓞 E) E)) A hc a
  have h1 : ∑ k, (τ.comp (algebraMap (𝓞 E) E)) (c k) • A (RingOfIntegers.basis E k) =
      τ (algebraMap (𝓞 E) E δ) • prj A τ := by
    rw [prj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.comp_apply, hc, map_mul, mul_smul]
  have hd : τ (algebraMap (𝓞 E) E δ) ≠ 0 := by
    rw [map_ne_zero_iff _ τ.injective]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mpr hδ0
  rw [h1, Matrix.mul_smul, smul_comm] at h
  exact smul_right_injective _ hd h

omit [CharZero F] in
theorem prj_act (τ : E →+* F) (a : 𝓞 E) : prj A τ * A a = τ (a : E) • prj A τ := by
  rw [← act_prj, prj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← map_mul, ← map_mul, mul_comm]

variable [IsGalois ℚ E]

theorem prj_mul (σ τ : E →+* F) : prj A σ * prj A τ = if σ = τ then prj A τ else 0 := by
  have h := GlobalTheory.InvDifferentArith.orth σ τ
  have h1 : prj A σ * prj A τ = (∑ k, σ ((integralBasis E).traceDual k) * τ (integralBasis E k)) • prj A τ := by
    conv_lhs => rw [prj, Finset.sum_mul]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, act_prj, smul_smul, integralBasis_apply]
  rw [h1, h]
  by_cases hστ : σ = τ
  · subst hστ; simp
  · rw [if_neg hστ, if_neg (Ne.symm hστ), zero_smul]

theorem card_emb (φ₀ : E →+* F) : Fintype.card (E →+* F) = Module.finrank ℚ E := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  refine (Fintype.card_of_bijective (f := fun g : E ≃ₐ[ℚ] E => φ₀.comp g.toRingHom) ⟨?_, ?_⟩).symm
  · intro g h hgh
    ext y
    exact φ₀.injective (RingHom.congr_fun hgh y)
  · intro φ
    obtain ⟨g, hg⟩ := GlobalTheory.InvDifferentArith.exists_aut φ₀ φ
    exact ⟨g, hg.symm⟩

theorem sum_prj (φ₀ : E →+* F) : ∑ τ, prj A τ = 1 := by
  obtain ⟨δ, c, hδ0, hc⟩ := exists_diff_dual E
  rw [← GlobalTheory.ColengthDifferent.sum_proj_eq_one (fun τ : E →+* F => τ) (fun _ _ h => h) (card_emb φ₀) A (fun _ => δ)
    (fun _ => hδ0) (fun _ => c) (fun _ => hc)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hd : τ (algebraMap (𝓞 E) E δ) ≠ 0 := by
    rw [map_ne_zero_iff _ τ.injective]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mpr hδ0
  rw [prj, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc, map_mul, smul_smul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

end Proj

section Den

variable {F : Type} [Field F]

theorem exists_common {κ : Type} [Fintype κ] (Pr : ℕ → Prop) (h1 : Pr 1) (hm : ∀ a b, Pr a → Pr b → Pr (a * b))
    (x : κ → F) (hx : ∀ k, ∃ s : ℕ, Pr s ∧ IsIntegral ℤ ((s : F) * x k)) :
    ∃ s : ℕ, Pr s ∧ ∀ k, IsIntegral ℤ ((s : F) * x k) := by
  choose s hs hsx using hx
  refine ⟨∏ k, s k, Finset.prod_induction _ Pr hm h1 fun k _ => hs k, fun k => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hsx k)
  have := isIntegral_algebraMap (R := ℤ) (A := F) (x := ((∏ j ∈ Finset.univ.erase k, s j : ℕ) : ℤ))
  simpa using this

theorem exists_den [NumberField F] (x : F) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : F) * x) := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, h⟩ := hx.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with h2 | h2
  · rw [h2] at h; simpa using h
  · have h3 := h.neg
    rw [h2] at h3; simpa using h3

theorem exists_common_den [NumberField F] {κ : Type} [Fintype κ] (x : κ → F) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ k, IsIntegral ℤ ((n : F) * x k) :=
  exists_common (fun n => n ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) x fun k => exists_den (x k)

theorem exists_gen (R : Subring F) [IsPrincipalIdealRing R] {κ : Type} [Fintype κ] (x : κ → F) (d : F) (hd : d ≠ 0)
    (hx : ∀ k, d * x k ∈ R) :
    ∃ r : κ → F, (∀ k, r k ∈ R) ∧ ∀ k, ∃ q ∈ R, x k = q * ∑ l, r l * x l := by
  let a : κ → R := fun k => ⟨d * x k, hx k⟩
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range a))).principal
  have hg1 : g ∈ Submodule.span R (Set.range a) := by
    change g ∈ Ideal.span (Set.range a)
    rw [hg]; exact Submodule.mem_span_singleton_self g
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hg1
  refine ⟨fun k => r k, fun k => (r k).2, fun k => ?_⟩
  have hk : a k ∈ Submodule.span R {g} := hg ▸ Ideal.subset_span ⟨k, rfl⟩
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.1 hk
  refine ⟨q, q.2, mul_left_cancel₀ hd ?_⟩
  have h1 : ((q : F)) * (g : F) = d * x k := congrArg Subtype.val hq
  have h2 : (g : F) = ∑ l, (r l : F) * (d * x l) := by
    rw [← hr]; simp [a]
  rw [← h1, h2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => by ring

theorem exists_sep (E : Type) [Field E] [NumberField E] [CharZero F] :
    ∃ α : 𝓞 E, ∀ σ τ : E →+* F, σ ≠ τ → σ (α : E) ≠ τ (α : E) := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ E
  obtain ⟨n, hn, h⟩ := exists_den pb.gen
  refine ⟨⟨_, h⟩, fun σ τ hne he => hne ?_⟩
  have h1 : σ ((n : E) * pb.gen) = τ ((n : E) * pb.gen) := he
  rw [map_mul, map_mul, map_natCast, map_natCast] at h1
  have h2 := mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) h1
  have h3 : σ.toRatAlgHom = τ.toRatAlgHom := pb.algHom_ext h2
  ext x
  exact DFunLike.congr_fun h3 x

end Den

section Pair

variable {F : Type} [Field F] (R : Subring F) {N : ℕ}

theorem dot_mem {G : Matrix (Fin N) (Fin N) F} (hG : ∀ i j, G i j ∈ R) {x y : Fin N → F} (hx : ∀ i, x i ∈ R)
    (hy : ∀ i, y i ∈ R) : x ⬝ᵥ G *ᵥ y ∈ R := by
  simp only [Matrix.mulVec, dotProduct]
  exact R.sum_mem fun i _ => R.mul_mem (hx i) (R.sum_mem fun j _ => R.mul_mem (hG i j) (hy j))

theorem pair_mem {ι : Type} [Fintype ι] (A B : ι → Matrix (Fin N) (Fin N) F) (hA : ∑ σ, A σ = 1) (hB : ∑ σ, B σ = 1)
    {G : Matrix (Fin N) (Fin N) F} (hG : ∀ i j, G i j ∈ R) (c : ι → ι → Prop)
    (hz : ∀ σ τ, ¬ c σ τ → A σ * G * B τ = 0) (hf1 : ∀ σ τ τ', c σ τ → c σ τ' → τ = τ')
    (hf2 : ∀ σ σ' τ, c σ τ → c σ' τ → σ = σ') (Ψ : ι → Prop) (hΨ : ∀ σ τ, c σ τ → (Ψ σ ↔ ¬ Ψ τ))
    {σ τ : ι} {x y : Fin N → F} (hx : x ᵥ* A σ = x) (hx1 : Ψ σ → ∀ i, x i ∈ R)
    (hx2 : ¬ Ψ σ → ∃ z : Fin N → F, (∀ i, z i ∈ R) ∧ x = z ᵥ* A σ) (hy : B τ *ᵥ y = y) (hy1 : Ψ τ → ∀ i, y i ∈ R)
    (hy2 : ¬ Ψ τ → ∃ z : Fin N → F, (∀ i, z i ∈ R) ∧ y = B τ *ᵥ z) : x ⬝ᵥ G *ᵥ y ∈ R := by
  have key : ∀ u v : Fin N → F, (u ᵥ* A σ) ⬝ᵥ G *ᵥ (B τ *ᵥ v) = u ⬝ᵥ (A σ * G * B τ) *ᵥ v := by
    intro u v
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  by_cases hc : c σ τ
  · by_cases hs : Ψ σ
    · obtain ⟨z, hz1, rfl⟩ := hy2 ((hΨ _ _ hc).1 hs)
      have h1 : A σ * G * B τ = A σ * G := by
        conv_rhs => rw [← mul_one (A σ * G), ← hB, Finset.mul_sum]
        exact (Finset.sum_eq_single τ (fun τ' _ h => hz _ _ fun h' => h (hf1 _ _ _ h' hc)) (by simp)).symm
      rw [← hx, key, h1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hx]
      exact dot_mem R hG (hx1 hs) hz1
    · obtain ⟨z, hz1, rfl⟩ := hx2 hs
      have ht : Ψ τ := by
        by_contra h
        exact hs ((hΨ _ _ hc).2 h)
      have h1 : A σ * G * B τ = G * B τ := by
        conv_rhs => rw [← one_mul G, ← hA, Finset.sum_mul, Finset.sum_mul]
        exact (Finset.sum_eq_single σ (fun σ' _ h => hz _ _ fun h' => h (hf2 _ _ _ h' hc)) (by simp)).symm
      rw [← hy, key, h1, ← Matrix.mulVec_mulVec, hy]
      exact dot_mem R hG hz1 (hy1 ht)
  · rw [← hx, ← hy, key, hz _ _ hc]
    simp

end Pair

section Norm

variable {K : Type} [Field K] {w : AbsoluteValue K ℝ}

theorem w_sum_le (hw : IsNonarchimedean w) {κ : Type} (s : Finset κ) (f : κ → K) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ k ∈ s, w (f k) ≤ r) : w (∑ k ∈ s, f k) ≤ r :=
  Finset.sum_induction f (fun x => w x ≤ r) (fun a b ha hb => (hw a b).trans (max_le ha hb)) (by simpa using hr) h

theorem supN_mulVec_le (hw : IsNonarchimedean w) {N : ℕ} {M : Matrix (Fin N) (Fin N) K} (hM : ∀ i j, w (M i j) ≤ 1)
    (y : Fin N → K) : supN w (M *ᵥ y) ≤ supN w y := by
  refine supN_le w (supN_nonneg w y) fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine w_sum_le hw _ _ (supN_nonneg w y) fun j _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left (w.nonneg _) (hM i j)).trans (le_supN w y j)

theorem supN_smul {N : ℕ} (a : K) (y : Fin N → K) : supN w (a • y) = w a * supN w y := by
  unfold supN
  rw [Real.mul_iSup_of_nonneg (w.nonneg a)]
  simp

theorem supN_block (hw : IsNonarchimedean w) {N : ℕ} {ι : Type} (b : Fin N → ι) {U L : Matrix (Fin N) (Fin N) K}
    (hU : ∀ i j, w (U i j) ≤ 1) (hL : ∀ i j, w (L i j) ≤ 1)
    (hLU : ∀ r s, b r = b s → (L * U) r s = if r = s then 1 else 0) (τ : ι) (y : Fin N → K)
    (hy : ∀ r, b r ≠ τ → y r = 0) : supN w (U *ᵥ y) = supN w y := by
  refine le_antisymm (supN_mulVec_le hw hU y) (supN_le w (supN_nonneg w _) fun r => ?_)
  by_cases hr : b r = τ
  · have h1 : (L *ᵥ (U *ᵥ y)) r = y r := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, Finset.sum_eq_single r]
      · rw [hLU r r rfl, if_pos rfl, one_mul]
      · intro s _ hs
        by_cases h : b s = τ
        · rw [hLU r s (hr.trans h.symm), if_neg (Ne.symm hs), zero_mul]
        · rw [hy s h, mul_zero]
      · simp
    rw [← h1]
    exact (le_supN w _ r).trans (supN_mulVec_le hw hL _)
  · rw [hy r hr, map_zero]
    exact supN_nonneg w _

end Norm

section Place

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)

theorem w_p_lt_one {p : ℕ} (hv : resP v = p) : e.w (p : AlgebraicClosure F) < 1 := by
  subst hv
  have h1 : ((resP v : ℕ) : AlgebraicClosure F) =
      algebraMap F _ (algebraMap (𝓞 F) F ((resP v : ℕ) : 𝓞 F)) := by simp
  rw [h1, e.w_alg]
  refine (v.adicAbv_coe_lt_one_iff (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem w_le_one_of_isIntegral {x : AlgebraicClosure F} (hx : IsIntegral ℤ x) : e.w x ≤ 1 := by
  have h2 : IsIntegral e.O x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← e.mem_O, ← hy]
  exact y.2

theorem w_le_one {p : ℕ} (hv : resP v = p) {x : F} {s : ℕ} (hs : s.Coprime p) (hx : IsIntegral ℤ ((s : F) * x)) :
    e.w (algebraMap F (AlgebraicClosure F) x) ≤ 1 := by
  have hw := isNonarchimedean_w e
  have hint : ∀ m : ℤ, e.w (m : AlgebraicClosure F) ≤ 1 := fun m =>
    w_le_one_of_isIntegral e (by simpa using isIntegral_algebraMap (R := ℤ) (A := AlgebraicClosure F) (x := m))
  have h1 : 1 ≤ e.w (s : AlgebraicClosure F) := by
    by_contra hc
    rw [not_le] at hc
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
    have h2 : (a : AlgebraicClosure F) * s + b * p = 1 := by exact_mod_cast congrArg (Int.cast (R := AlgebraicClosure F)) hab
    have h3 := hw ((a : AlgebraicClosure F) * s) (b * p)
    rw [h2, map_one, map_mul, map_mul] at h3
    have h4 := (mul_le_of_le_one_left (e.w.nonneg _) (hint a)).trans_lt hc
    have h5 := (mul_le_of_le_one_left (e.w.nonneg _) (hint b)).trans_lt (w_p_lt_one e hv)
    exact absurd h3 (not_le.2 (max_lt h4 h5))
  have h2 := w_le_one_of_isIntegral e (hx.map (algebraMap F (AlgebraicClosure F)).toIntAlgHom)
  have h3 : (algebraMap F (AlgebraicClosure F)).toIntAlgHom ((s : F) * x) =
      (s : AlgebraicClosure F) * algebraMap F (AlgebraicClosure F) x := by simp
  rw [h3, map_mul] at h2
  exact (le_mul_of_one_le_left (e.w.nonneg _) h1).trans h2

end Place

section Main

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {F : Type} [Field F] [CharZero F] {N : ℕ}

omit [IsGalois ℚ E] in
theorem prj_pair_zero (A : 𝓞 E →+* Matrix (Fin N) (Fin N) F) (bar : 𝓞 E ≃+* 𝓞 E) (G : Matrix (Fin N) (Fin N) F)
    (hG : ∀ a, (A a)ᵀ * G = G * A (bar a)) (σ τ : E →+* F) (h : ¬ ∀ a : 𝓞 E, σ (a : E) = τ ((bar a : 𝓞 E) : E)) :
    (prj A σ)ᵀ * G * prj A τ = 0 := by
  obtain ⟨a, ha⟩ := not_forall.1 h
  have h1 : (prj A σ)ᵀ * ((A a)ᵀ * G) * prj A τ = (prj A σ)ᵀ * (G * A (bar a)) * prj A τ := by rw [hG]
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, act_prj, Matrix.mul_assoc _ (G * _), Matrix.mul_assoc G, act_prj,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
    ← sub_eq_zero, ← sub_smul] at h1
  exact (smul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 ha)

omit [IsGalois ℚ E] in
theorem prj_pair_zero' (A : 𝓞 E →+* Matrix (Fin N) (Fin N) F) (bar : 𝓞 E ≃+* 𝓞 E) (G : Matrix (Fin N) (Fin N) F)
    (hG : ∀ a, G * (A a)ᵀ = A (bar a) * G) (σ τ : E →+* F) (h : ¬ ∀ a : 𝓞 E, τ (a : E) = σ ((bar a : 𝓞 E) : E)) :
    prj A σ * G * (prj A τ)ᵀ = 0 := by
  obtain ⟨a, ha⟩ := not_forall.1 h
  have h1 : prj A σ * (G * (A a)ᵀ) * (prj A τ)ᵀ = prj A σ * (A (bar a) * G) * (prj A τ)ᵀ := by rw [hG]
  rw [← Matrix.mul_assoc _ (A _), prj_act, Matrix.mul_assoc _ (G * _), Matrix.mul_assoc G, ← Matrix.transpose_mul, prj_act,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
    ← sub_eq_zero, ← sub_smul] at h1
  exact (smul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 ha)

omit [NumberField E] [IsGalois ℚ E] [CharZero F] in
theorem emb_ext [NumberField E] {σ τ : E →+* F} (h : ∀ a : 𝓞 E, σ (a : E) = τ (a : E)) : σ = τ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem selfDual (φ₀ : E →+* F) (R : Subring F) (bar : 𝓞 E ≃+* 𝓞 E) (Φ : Set (E →+* F))
    (hΦ : ∀ σ τ : E →+* F, (∀ α : 𝓞 E, τ (α : E) = σ ((bar α : 𝓞 E) : E)) → (σ ∈ Φ ↔ τ ∉ Φ))
    (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ) (J : Matrix (Fin N) (Fin N) ℤ) (hJ : IsUnit J.det)
    (hρ : ∀ α, (ρ α).transpose * J = J * ρ (bar α)) (A : 𝓞 E →+* Matrix (Fin N) (Fin N) F)
    (hA : ∀ a, A a = (ρ a).map (Int.castRingHom F))
    (r : (E →+* F) → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → F) (hr : ∀ τ k, r τ k ∈ R) (c : (E →+* F) → F)
    (hc : ∀ τ, c τ = ∑ k, r τ k * τ ((integralBasis E).traceDual k))
    (hq : ∀ τ k, ∃ q ∈ R, τ ((integralBasis E).traceDual k) = q * c τ) (hc0 : ∀ τ, c τ ≠ 0)
    (b : Fin N → (E →+* F)) (U L : Matrix (Fin N) (Fin N) F) (hUL : ∀ i j, U i j ∈ R ∧ L i j ∈ R)
    (hU : ∀ s, (prj A (b s)).mulVec (fun i => U i s) = fun i => U i s) (cf : (E →+* F) → F)
    (hcf : ∀ τ, cf τ = if τ ∈ Φ then c τ else 1) (P Q : Matrix (Fin N) (Fin N) F)
    (hP : ∀ s, P s = (cf (b s))⁻¹ • (L s ᵥ* prj A (b s))) (hQ : ∀ i s, Q i s = cf (b s) * U i s) (i j : Fin N) :
    (Qᵀ * J.map (Int.castRingHom F) * Q) i j ∈ R ∧ (P * (J.map (Int.castRingHom F))⁻¹ * Pᵀ) i j ∈ R := by
  set JF := J.map (Int.castRingHom F) with hJF
  have hJi : JF * (J⁻¹).map (Int.castRingHom F) = 1 := by
    rw [hJF, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv : JF⁻¹ = (J⁻¹).map (Int.castRingHom F) := Matrix.inv_eq_right_inv hJi
  have hJ1 : JF * JF⁻¹ = 1 := hinv ▸ hJi
  have hJ2 : JF⁻¹ * JF = 1 := mul_eq_one_comm.1 hJ1
  have hG : ∀ a, (A a)ᵀ * JF = JF * A (bar a) := fun a => by
    rw [hA, hA, hJF, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hρ]
  have hG' : ∀ a, JF⁻¹ * (A a)ᵀ = A (bar a) * JF⁻¹ := fun a => by
    calc JF⁻¹ * (A a)ᵀ = JF⁻¹ * ((A a)ᵀ * JF) * JF⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hJ1, Matrix.mul_one]
      _ = A (bar a) * JF⁻¹ := by rw [hG, ← Matrix.mul_assoc, hJ2, Matrix.one_mul]
  have hs : ∑ τ, prj A τ = 1 := sum_prj A φ₀
  have hs' : ∑ τ, (prj A τ)ᵀ = 1 := by rw [← Matrix.transpose_sum, hs, Matrix.transpose_one]
  have hidem : ∀ τ, prj A τ * prj A τ = prj A τ := fun τ => by rw [prj_mul, if_pos rfl]
  have hbar : ∀ {τ τ' : E →+* F}, (∀ a : 𝓞 E, τ ((bar a : 𝓞 E) : E) = τ' ((bar a : 𝓞 E) : E)) → τ = τ' :=
    fun h => emb_ext fun a => by obtain ⟨a, rfl⟩ := bar.surjective a; exact h a
  constructor
  · have hcol : ∀ s, (fun i => Q i s) = cf (b s) • fun i => U i s := fun s => funext fun i => hQ i s
    have h1 : ∀ s, prj A (b s) *ᵥ (fun i => Q i s) = fun i => Q i s := fun s => by
      rw [hcol, Matrix.mulVec_smul, hU]
    have h2 : ∀ s, b s ∉ Φ → ∀ i, Q i s ∈ R := fun s h i => by
      rw [hQ, hcf, if_neg h, one_mul]; exact (hUL i s).1
    have h3 : ∀ s, ¬ b s ∉ Φ → ∃ z : Fin N → F, (∀ i, z i ∈ R) ∧ (fun i => Q i s) = prj A (b s) *ᵥ z := fun s h => by
      obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.eigenvector_integral_completion E F R N ρ (b s) (fun i => U i s) (fun i => (hUL i s).1) (fun a => by
        rw [← hA, ← hU s, Matrix.mulVec_mulVec, act_prj, Matrix.smul_mulVec]) (r (b s)) (hr _)
      refine ⟨z, hz, ?_⟩
      rw [hz' _ fun a => by rw [← hA, prj_act], hU, hcol, hcf, if_pos (not_not.1 h), hc]
    have key := pair_mem R (fun σ => (prj A σ)ᵀ) (prj A) hs' hs (G := JF) (fun _ _ => intCast_mem R _)
      (fun σ τ => ∀ a : 𝓞 E, σ (a : E) = τ ((bar a : 𝓞 E) : E)) (prj_pair_zero A bar JF hG)
      (fun σ τ τ' h h' => hbar fun a => (h a).symm.trans (h' a))
      (fun σ σ' τ h h' => emb_ext fun a => (h a).trans (h' a).symm) (fun τ => τ ∉ Φ)
      (fun σ τ h => by rw [not_not]; exact (hΦ τ σ h).symm) (σ := b i) (τ := b j)
      (x := fun k => Q k i) (y := fun k => Q k j) (by rw [Matrix.vecMul_transpose, h1]) (h2 i)
      (fun h => by simpa only [Matrix.vecMul_transpose] using h3 i h) (h1 j) (h2 j) (h3 j)
    rw [Matrix.mul_assoc]
    exact key
  · have h1 : ∀ s, P s ᵥ* prj A (b s) = P s := fun s => by
      rw [hP, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hidem]
    have h2 : ∀ s, b s ∈ Φ → ∀ i, P s i ∈ R := fun s h i => by
      rw [hP, hcf, if_pos h, ← Matrix.vecMul_smul]
      simp only [Matrix.vecMul, dotProduct]
      refine R.sum_mem fun k _ => R.mul_mem (hUL s k).2 ?_
      rw [prj, Finset.smul_sum, Matrix.sum_apply]
      refine R.sum_mem fun l _ => ?_
      obtain ⟨q, hq1, hq2⟩ := hq (b s) l
      rw [smul_smul, hq2, mul_comm q, ← mul_assoc, inv_mul_cancel₀ (hc0 _), one_mul, hA]
      exact R.mul_mem hq1 (intCast_mem R _)
    have h3 : ∀ s, ¬ b s ∈ Φ → ∃ z : Fin N → F, (∀ i, z i ∈ R) ∧ P s = z ᵥ* prj A (b s) := fun s h =>
      ⟨L s, fun i => (hUL s i).2, by rw [hP, hcf, if_neg h, inv_one, one_smul]⟩
    have key := pair_mem R (prj A) (fun σ => (prj A σ)ᵀ) hs hs' (G := JF⁻¹)
      (fun _ _ => by rw [hinv]; exact intCast_mem R _)
      (fun σ τ => ∀ a : 𝓞 E, τ (a : E) = σ ((bar a : 𝓞 E) : E)) (prj_pair_zero' A bar JF⁻¹ hG')
      (fun σ τ τ' h h' => emb_ext fun a => (h a).trans (h' a).symm)
      (fun σ σ' τ h h' => hbar fun a => (h a).symm.trans (h' a)) (fun τ => τ ∈ Φ)
      hΦ (σ := b i) (τ := b j)
      (x := P i) (y := P j) (h1 i) (h2 i) (h3 i) (by rw [Matrix.mulVec_transpose, h1]) (h2 j)
      (fun h => by simpa only [Matrix.mulVec_transpose] using h3 j h)
    rw [Matrix.mul_assoc]
    exact key

end Main

theorem w_gen {K : Type} [Field K] {w : AbsoluteValue K ℝ} (hw : IsNonarchimedean w) {κ : Type} [Fintype κ]
    (x r : κ → K) (c : K) (m : ℝ) (hc : c = ∑ k, r k * x k) (hr : ∀ k, w (r k) ≤ 1)
    (hq : ∀ k, ∃ q, w q ≤ 1 ∧ x k = q * c) (hm : (∀ k, w (x k) ≤ m) ∧ ∃ k, w (x k) = m) : w c = m := by
  obtain ⟨h1, k, hk⟩ := hm
  have hm0 : 0 ≤ m := hk ▸ w.nonneg _
  refine le_antisymm ?_ ?_
  · rw [hc]
    refine w_sum_le hw _ _ hm0 fun l _ => ?_
    rw [map_mul]
    exact (mul_le_of_le_one_left (w.nonneg _) (hr l)).trans (h1 l)
  · obtain ⟨q, hq1, hq2⟩ := hq k
    rw [← hk, hq2, map_mul]
    exact mul_le_of_le_one_left (w.nonneg _) hq1

theorem exists_eigBasis : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (F : Type) [Field F] [NumberField F], Nonempty (E →+* F) →
    ∀ (bar : 𝓞 E ≃+* 𝓞 E) (Φ : Set (E →+* F)),
    (∀ σ τ : E →+* F, (∀ α : 𝓞 E, τ (α : E) = σ ((bar α : 𝓞 E) : E)) → (σ ∈ Φ ↔ τ ∉ Φ)) →
    ∀ {N : ℕ} (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ) (J : Matrix (Fin N) (Fin N) ℤ), IsUnit J.det →
    (∀ α, (ρ α).transpose * J = J * ρ (bar α)) → ∀ p : ℕ, p.Prime →
    ∃ (n : ℕ) (P Q : Matrix (Fin N) (Fin N) F), n ≠ 0 ∧
      EigBasis ρ J (fun τ => if τ ∈ Φ then vDiff E p else 0) p n P Q := by
  intro E _ _ _ F _ _ ⟨φ₀⟩ bar Φ hΦ N ρ J hJ hρ p hp
  obtain ⟨R, hR, hmem⟩ := GlobalTheory.T.exists_localization_away_from_prime F p hp
  have hnat : ∀ {n : ℕ} {x : F}, IsIntegral ℤ ((n : F) * x) → (n : F) * x ∈ R := fun h =>
    (hmem _).2 ⟨1, Nat.coprime_one_left p, by simpa using h⟩
  let A : 𝓞 E →+* Matrix (Fin N) (Fin N) F := (Int.castRingHom F).mapMatrix.comp ρ
  have hA : ∀ a, A a = (ρ a).map (Int.castRingHom F) := fun _ => rfl
  obtain ⟨b, U, L, hUL, hU, hLU⟩ := GlobalTheory.T.idempotent_triangular_decomposition F R hR (fun x => by
    obtain ⟨n, hn, h⟩ := exists_den x
    exact ⟨n, natCast_mem R n, Nat.cast_ne_zero.2 hn, hnat h⟩) (E →+* F) N (prj A) (prj_mul A) (sum_prj A φ₀)
  have hgen : ∀ τ : E →+* F, ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → F, (∀ k, r k ∈ R) ∧
      ∀ k, ∃ q ∈ R, τ ((integralBasis E).traceDual k) = q * ∑ l, r l * τ ((integralBasis E).traceDual l) := fun τ => by
    obtain ⟨n, hn, h⟩ := exists_common_den fun k => τ ((integralBasis E).traceDual k)
    exact exists_gen R _ (n : F) (Nat.cast_ne_zero.2 hn) fun k => hnat (h k)
  choose r hr hq using hgen
  obtain ⟨c, hc⟩ : ∃ c : (E →+* F) → F, ∀ τ, c τ = ∑ k, r τ k * τ ((integralBasis E).traceDual k) := ⟨_, fun _ => rfl⟩
  simp only [← hc] at hq
  have hc0 : ∀ τ, c τ ≠ 0 := fun τ h0 => by
    obtain ⟨k⟩ := (integralBasis E).index_nonempty
    obtain ⟨q, -, h⟩ := hq τ k
    rw [h0, mul_zero, map_eq_zero] at h
    exact (integralBasis E).traceDual.ne_zero k h
  obtain ⟨cf, hcf⟩ : ∃ cf : (E →+* F) → F, ∀ τ, cf τ = if τ ∈ Φ then c τ else 1 := ⟨_, fun _ => rfl⟩
  have hcf0 : ∀ τ, cf τ ≠ 0 := fun τ => by
    rw [hcf]; split_ifs
    exacts [hc0 τ, one_ne_zero]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin N) (Fin N) F, ∀ s, P s = (cf (b s))⁻¹ • (L s ᵥ* prj A (b s)) :=
    ⟨Matrix.of fun s => (cf (b s))⁻¹ • (L s ᵥ* prj A (b s)), fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin N) (Fin N) F, ∀ i s, Q i s = cf (b s) * U i s :=
    ⟨Matrix.of fun i s => cf (b s) * U i s, fun _ _ => rfl⟩
  have hcol : ∀ s, (fun i => Q i s) = cf (b s) • fun i => U i s := fun s => funext fun i => hQ i s
  have hPQ : P * Q = 1 := by
    ext i s
    have h1 : (P * Q) i s = P i ⬝ᵥ fun k => Q k s := rfl
    have h2 : (L * U) i s = L i ⬝ᵥ fun k => U k s := rfl
    rw [h1, hP, hcol, smul_dotProduct, dotProduct_smul, ← Matrix.dotProduct_mulVec, ← hU s, Matrix.mulVec_mulVec,
      prj_mul, Matrix.one_apply]
    by_cases h : b i = b s
    · rw [if_pos h, hU, ← h2, hLU i s h, h, smul_smul, inv_mul_cancel₀ (hcf0 _), one_smul]
    · rw [if_neg h, if_neg fun h' => h (by rw [h'])]
      simp
  obtain ⟨α, hα⟩ := exists_sep (F := F) E
  obtain ⟨n, hn, hnx⟩ := exists_common_den (F := F) (κ := (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ ((E →+* F) × (E →+* F)))
    (Sum.elim (fun t => P t.1 t.2) (Sum.elim (fun t => Q t.1 t.2) fun t => (t.1 (α : E) - t.2 (α : E))⁻¹))
  have hsd := selfDual φ₀ R bar Φ hΦ ρ J hJ hρ A hA r hr c hc hq hc0 b U L hUL hU cf hcf P Q hP hQ
  obtain ⟨s, hs, hsx⟩ := exists_common (F := F) (κ := (Fin N × Fin N) ⊕ (Fin N × Fin N)) (fun s => s.Coprime p)
    (Nat.coprime_one_left p) (fun _ _ => Nat.Coprime.mul_left)
    (Sum.elim (fun t => (Qᵀ * J.map (Int.castRingHom F) * Q) t.1 t.2)
      fun t => (P * (J.map (Int.castRingHom F))⁻¹ * Pᵀ) t.1 t.2) (by
      rintro (t | t)
      exacts [(hmem _).1 (hsd t.1 t.2).1, (hmem _).1 (hsd t.1 t.2).2])
  refine ⟨n, P, Q, hn, ⟨hPQ, fun i j => ⟨hnx (.inl (i, j)), hnx (.inr (.inl (i, j)))⟩, s, hs,
    fun i j => ⟨hsx (.inl (i, j)), hsx (.inr (i, j))⟩⟩, b, α, ?_, fun σ τ h => ⟨hα σ τ h, ?_⟩, ?_⟩
  · have h1 : A α * Q = Q * Matrix.diagonal fun s => b s (α : E) := by
      ext i s
      have h2 : (A α * Q) i s = (A α *ᵥ fun k => Q k s) i := rfl
      rw [h2, hcol, ← hU s, Matrix.mulVec_smul, Matrix.mulVec_mulVec, act_prj, Matrix.smul_mulVec, hU,
        Matrix.mul_diagonal, hQ]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [← hA, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  · rw [div_eq_mul_inv]
    exact hnx (.inr (.inr (σ, τ)))
  · intro v hv e τ y hy
    have hw := isNonarchimedean_w e
    set ι := algebraMap F (AlgebraicClosure F) with hι
    have hRw : ∀ x ∈ R, e.w (ι x) ≤ 1 := fun x hx => by
      obtain ⟨s, hs, h⟩ := (hmem x).1 hx
      exact w_le_one e hv hs h
    have h1 : (Q.map ι) *ᵥ y = ι (cf τ) • ((U.map ι) *ᵥ y) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.map_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h : b s = τ
      · rw [hQ, h, map_mul, mul_assoc]
      · rw [hy s h, mul_zero, mul_zero, mul_zero]
    have h2 := supN_block hw b (U := U.map ι) (L := L.map ι) (fun i j => hRw _ (hUL i j).1) (fun i j => hRw _ (hUL i j).2)
      (fun i s h => by
        rw [← Matrix.map_mul, Matrix.map_apply, hLU i s h]
        split_ifs <;> simp) τ y hy
    rw [h1, supN_smul, h2, ← mul_assoc, hcf]
    by_cases hτ : τ ∈ Φ
    · have h3 : e.w (ι (c τ)) = e.w (p : AlgebraicClosure F) ^ (-vDiff E p) := by
        refine w_gen hw (fun k => ι (τ ((integralBasis E).traceDual k))) (fun k => ι (r τ k)) _ _
          (by rw [hc, map_sum]; simp only [map_mul]) (fun k => hRw _ (hr τ k)) (fun k => ?_)
          (GlobalTheory.T.different_valuation_bound E _ e.w hw p hp (w_p_lt_one e hv) (ι.comp τ))
        obtain ⟨q, hq1, hq2⟩ := hq τ k
        exact ⟨ι q, hRw q hq1, by rw [hq2, map_mul]⟩
      have hp0 : 0 < e.w (p : AlgebraicClosure F) := e.w.pos (Nat.cast_ne_zero.2 hp.ne_zero)
      simp only [if_pos hτ]
      rw [h3, ← Real.rpow_add hp0, add_neg_cancel, Real.rpow_zero, one_mul]
    · simp only [if_neg hτ]
      simp

end GlobalTheory.EigArith
