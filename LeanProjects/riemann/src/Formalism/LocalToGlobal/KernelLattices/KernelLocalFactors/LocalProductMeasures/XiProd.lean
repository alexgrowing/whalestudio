import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapENe
import Formalism.LocalToGlobal.Divisibility.TuplesLemmas

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Ker

open Formalism.L2.DIV Formalism.UG

section XP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def xpJ (d : FiniteAdeleRing (𝓞 F) F) (a : E) : AfE F E := a ⊗ₜ[F] d + (1 : E) ⊗ₜ[F] (1 - d)

theorem xp_J_locId (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ) : ((locId E v a : (AfE F E)ˣ) : AfE F E) = xpJ (Formalism.L2.G.sgl F v 1) (a : E) := rfl

theorem xp_J_zero (a : E) : xpJ (0 : FiniteAdeleRing (𝓞 F) F) a = 1 := by
  unfold xpJ
  rw [TensorProduct.tmul_zero, zero_add, sub_zero]
  rfl

theorem xp_J_one (a : E) : xpJ (1 : FiniteAdeleRing (𝓞 F) F) a = a ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) := by
  unfold xpJ
  rw [sub_self, TensorProduct.tmul_zero, add_zero]

theorem xp_J_orth {d d' : FiniteAdeleRing (𝓞 F) F} (h : d * d' = 0) (a : E) : xpJ d a * xpJ d' a = xpJ (d + d') a := by
  have h1 : d * (1 - d') = d := by rw [mul_sub, mul_one, h, sub_zero]
  have h2 : (1 - d) * d' = d' := by rw [_root_.sub_mul, one_mul, h, sub_zero]
  have h3 : (1 - d) * (1 - d') = 1 - (d + d') := by rw [_root_.sub_mul, one_mul, h1]; ring
  unfold xpJ
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, h, h1, h2, h3, TensorProduct.tmul_zero, zero_add, mul_one, one_mul, one_mul, TensorProduct.tmul_add]
  abel

theorem xp_J_same {d : FiniteAdeleRing (𝓞 F) F} (h : d * d = d) (a b : E) : xpJ d a * xpJ d b = xpJ d (a * b) := by
  have h2 : d * (1 - d) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  have h3 : (1 - d) * d = 0 := by rw [_root_.sub_mul, one_mul, h, sub_self]
  have h4 : (1 - d) * (1 - d) = 1 - d := by rw [mul_sub, mul_one, h3, sub_zero]
  unfold xpJ
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, h, h2, h3, h4, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero, zero_add, one_mul]

theorem xp_J_sub (d : FiniteAdeleRing (𝓞 F) F) (a : E) : xpJ d a = 1 + (a - 1) ⊗ₜ[F] d := by
  unfold xpJ
  rw [TensorProduct.tmul_sub, TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
  abel

theorem xp_scal (n : ℕ) (y : E) (g : FiniteAdeleRing (𝓞 F) F) :
    y ⊗ₜ[F] (((n : ℕ) : FiniteAdeleRing (𝓞 F) F) * g) = (((n : ℕ) : E) * y) ⊗ₜ[F] g := by
  have h1 : ((n : ℕ) : FiniteAdeleRing (𝓞 F) F) * g = ((n : ℕ) : F) • g := by rw [Algebra.smul_def, map_natCast]
  rw [h1, ← TensorProduct.smul_tmul, Algebra.smul_def, map_natCast]

theorem xp_J_eq (N k : ℕ) (a : E) (b : 𝓞 E) (hb : ((k : ℕ) : E) * (a - 1) = (b : E)) (g : FiniteAdeleRing (𝓞 F) F) (hg : g ∈ intAd F)
    (d : FiniteAdeleRing (𝓞 F) F) (hd : d = ((N * k : ℕ) : FiniteAdeleRing (𝓞 F) F) * g) :
    ∃ r : RInt F E, xpJ d a = ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) := by
  refine ⟨toRInt F E b * ⟨(1 : E) ⊗ₜ[F] g, qu_right g hg⟩, ?_⟩
  rw [xp_J_sub, hd, xp_scal]
  push_cast
  congr 1
  show _ = (N : AfE F E) * ((algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] g))
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  conv_rhs => rw [← nsmul_eq_mul, TensorProduct.smul_tmul', nsmul_eq_mul]
  rw [mul_assoc, hb]

theorem xp_J_at_one (d : FiniteAdeleRing (𝓞 F) F) : xpJ d (1 : E) = 1 := by
  unfold xpJ
  rw [← TensorProduct.tmul_add, add_sub_cancel]
  rfl

theorem xp_mem_congN (N k : ℕ) (a : Eˣ) (b b' : 𝓞 E) (hb : ((k : ℕ) : E) * ((a : E) - 1) = (b : E))
    (hb' : ((k : ℕ) : E) * (((a⁻¹ : Eˣ) : E) - 1) = (b' : E)) (g : FiniteAdeleRing (𝓞 F) F) (hg : g ∈ intAd F)
    (d : FiniteAdeleRing (𝓞 F) F) (hd : d = ((N * k : ℕ) : FiniteAdeleRing (𝓞 F) F) * g) (hdd : d * d = d)
    (u : (AfE F E)ˣ) (hu : (u : AfE F E) = xpJ d (a : E)) : u ∈ congN F E N := by
  obtain ⟨r, hr⟩ := xp_J_eq N k (a : E) b hb g hg d hd
  obtain ⟨r', hr'⟩ := xp_J_eq N k ((a⁻¹ : Eˣ) : E) b' hb' g hg d hd
  let u₀ : (RInt F E)ˣ :=
    { val := 1 + (N : RInt F E) * r
      inv := 1 + (N : RInt F E) * r'
      val_inv := Subtype.ext (by
        show ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) * ((1 + (N : RInt F E) * r' : RInt F E) : AfE F E) = 1
        rw [← hr, ← hr', xp_J_same hdd, Units.mul_inv, xp_J_at_one])
      inv_val := Subtype.ext (by
        show ((1 + (N : RInt F E) * r' : RInt F E) : AfE F E) * ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) = 1
        rw [← hr, ← hr', xp_J_same hdd, Units.inv_mul, xp_J_at_one]) }
  unfold congN congU
  rw [Subgroup.mem_map]
  refine ⟨u₀, (mem_kerRed _ u₀).2 ?_, Units.ext ?_⟩
  · show 1 + (N : RInt F E) * r - 1 ∈ _
    rw [add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · show ((1 + (N : RInt F E) * r : RInt F E) : AfE F E) = u
    rw [← hr, hu]

theorem xp_g (M : ℕ) (hM : 0 < M) (d : FiniteAdeleRing (𝓞 F) F) (hd : d ∈ intAd F)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∈ v.asIdeal → evalV F v d = 0) :
    ∃ g ∈ intAd F, d = ((M : ℕ) : FiniteAdeleRing (𝓞 F) F) * g := by
  have hM0 : ((M : ℕ) : F) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) ((M : ℕ) : F)⁻¹ * d, ?_, ?_⟩
  · intro v
    show algebraMap F (v.adicCompletion F) ((M : ℕ) : F)⁻¹ * d v ∈ v.adicCompletionIntegers F
    by_cases hv : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal
    · have h0 : d v = 0 := hT v hv
      rw [h0, mul_zero]
      exact zero_mem _
    · have hval : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ((M : ℕ) : 𝓞 F))) = 1 := by
        rw [Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R, intValuation_eq_one_iff_mem_primeCompl]
        exact Ideal.mem_primeCompl_iff.mpr hv
      rw [map_natCast] at hval
      rw [mem_adicCompletionIntegers, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hd v
  · rw [← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]

def xpE (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ T, Formalism.L2.G.sgl F v 1

open Classical in
theorem xp_E_at (T : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    evalV F w (xpE T) = if w ∈ T then 1 else 0 := by
  unfold xpE
  rw [map_sum]
  split_ifs with hw
  · rw [Finset.sum_eq_single w (fun b _ hb => Formalism.L2.G.sgl_apply_ne F b 1 (Ne.symm hb)) (fun h => absurd hw h), Formalism.L2.G.sgl_apply_same]
  · exact Finset.sum_eq_zero fun b hb => Formalism.L2.G.sgl_apply_ne F b 1 (fun h => hw (h ▸ hb))

theorem xp_E_idem (T : Finset (HeightOneSpectrum (𝓞 F))) : xpE T * xpE T = xpE T := by
  classical
  apply Formalism.L2.G.adele_ext
  intro w
  rw [map_mul, xp_E_at]
  split_ifs <;> simp

theorem xp_E_compl_idem (T : Finset (HeightOneSpectrum (𝓞 F))) : (1 - xpE T) * (1 - xpE T) = 1 - xpE T := by
  rw [mul_sub, mul_one, _root_.sub_mul, one_mul, xp_E_idem, sub_self, sub_zero]

theorem xp_E_orth (T : Finset (HeightOneSpectrum (𝓞 F))) : xpE T * (1 - xpE T) = 0 := by
  rw [mul_sub, mul_one, xp_E_idem, sub_self]

theorem xp_sgl_orth (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
    Formalism.L2.G.sgl F v 1 * xpE T = 0 := by
  classical
  apply Formalism.L2.G.adele_ext
  intro w
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    rw [xp_E_at, if_neg hv, mul_zero]
  · rw [Formalism.L2.G.sgl_apply_ne F v 1 h, zero_mul]

theorem xp_E_int (T : Finset (HeightOneSpectrum (𝓞 F))) : xpE T ∈ intAd F :=
  Subring.sum_mem _ fun v _ => qu_sgl_int v 1 (one_mem _)

theorem xp_prod (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Eˣ) :
    ((∏ v ∈ T, locId E v x : (AfE F E)ˣ) : AfE F E) = xpJ (xpE T) (x : E) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Units.val_one, xpE, Finset.sum_empty, xp_J_zero]
  | insert v T hv ih =>
    rw [Finset.prod_insert hv, Units.val_mul, ih, xp_J_locId, xp_J_orth (xp_sgl_orth T v hv)]
    unfold xpE
    rw [Finset.sum_insert hv]

theorem xp_den (a : E) : ∃ k : ℕ, 0 < k ∧ ∃ c : 𝓞 E, ((k : ℕ) : E) * a = (c : E) := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hI : Ideal.span {q} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hk : Ideal.absNorm (Ideal.span {q}) ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {q}))
  refine ⟨Ideal.absNorm (Ideal.span {q}), Nat.pos_of_ne_zero hk, t * p, ?_⟩
  have hqE : algebraMap (𝓞 E) E q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hq0
  rw [← map_natCast (algebraMap (𝓞 E) E), ← ht]
  show algebraMap (𝓞 E) E (t * q) * _ = algebraMap (𝓞 E) E (t * p)
  rw [map_mul, map_mul]
  field_simp

theorem unit_sub_one_bounded_denominator (x : Eˣ) : ∃ k : ℕ, 0 < k ∧ ∃ b b' : 𝓞 E, ((k : ℕ) : E) * ((x : E) - 1) = (b : E) ∧
    ((k : ℕ) : E) * (((x⁻¹ : Eˣ) : E) - 1) = (b' : E) := by
  obtain ⟨k₁, hk₁, c₁, h₁⟩ := xp_den (x : E)
  obtain ⟨k₂, hk₂, c₂, h₂⟩ := xp_den ((x⁻¹ : Eˣ) : E)
  refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, (k₂ : 𝓞 E) * (c₁ - k₁), (k₁ : 𝓞 E) * (c₂ - k₂), ?_, ?_⟩
  · have h := h₁
    push_cast at h ⊢
    linear_combination (k₂ : E) * h
  · have h := h₂
    push_cast at h ⊢
    linear_combination (k₁ : E) * h

variable (F) in
theorem xp_T_finite (M : ℕ) (hM : 0 < M) : {v : HeightOneSpectrum (𝓞 F) | ((M : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((M : ℕ) : 𝓞 F)} ≠ (0 : Ideal (𝓞 F)) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.2 hv

theorem twist_product_formula : XiProd := by
  intro F E _ _ _ _ _ L _ S ξ x
  obtain ⟨⟨hrat, ⟨N, hN, hcong⟩, _⟩, -⟩ := (mem_tupGrp (ξ : Chr F E L)).mp ξ.2
  obtain ⟨k, hk, b, b', hb, hb'⟩ := unit_sub_one_bounded_denominator x
  have hM : 0 < N * k := Nat.mul_pos hN hk
  set T : Finset (HeightOneSpectrum (𝓞 F)) := (xp_T_finite F (N * k) hM).toFinset with hTdef
  have hmemT : ∀ v, v ∈ T ↔ ((N * k : ℕ) : 𝓞 F) ∈ v.asIdeal := fun v => by
    rw [hTdef, Set.Finite.mem_toFinset]; rfl
  have hloc : ∀ v, v ∉ T → lamX (ξ : Chr F E L) v x = 1 := by
    intro v hv
    obtain ⟨g, hg, hd⟩ := xp_g (N * k) hM (Formalism.L2.G.sgl F v 1) (qu_sgl_int v 1 (one_mem _)) (fun w hw => by
      have hwv : w ≠ v := fun h => hv ((hmemT v).2 (h ▸ hw))
      exact Formalism.L2.G.sgl_apply_ne F v 1 hwv)
    have hdd : Formalism.L2.G.sgl F v 1 * Formalism.L2.G.sgl F v 1 = Formalism.L2.G.sgl F v 1 := by rw [← Formalism.L2.G.sgl_mul, one_mul]
    exact hcong (xp_mem_congN N k x b b' hb hb' g hg _ hd hdd (locId E v x) rfl)
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => lamX (ξ : Chr F E L) v x) ⊆ (T : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    by_contra h
    exact hv (hloc v h)
  refine ⟨T.finite_toSet.subset hsupp, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  have e1 : (∏ v ∈ T, lamX (ξ : Chr F E L) v x) = (ξ : Chr F E L) (∏ v ∈ T, locId E v x) := by
    rw [map_prod]; rfl
  rw [e1]
  let U : (AfE F E)ˣ :=
    { val := xpJ (1 - xpE T) (x : E)
      inv := xpJ (1 - xpE T) ((x⁻¹ : Eˣ) : E)
      val_inv := by rw [xp_J_same (xp_E_compl_idem T), Units.mul_inv, xp_J_at_one]
      inv_val := by rw [xp_J_same (xp_E_compl_idem T), Units.inv_mul, xp_J_at_one] }
  have hU : (ξ : Chr F E L) U = 1 := by
    obtain ⟨g, hg, hd⟩ := xp_g (N * k) hM (1 - xpE T) (Subring.sub_mem _ (Subring.one_mem _) (xp_E_int T)) (fun w hw => by
      classical
      rw [map_sub, map_one, xp_E_at, if_pos ((hmemT w).2 hw), sub_self])
    exact hcong (xp_mem_congN N k x b b' hb hb' g hg _ hd (xp_E_compl_idem T) U rfl)
  have hprod : (∏ v ∈ T, locId E v x) * U = ratId F E x := by
    apply Units.ext
    rw [Units.val_mul, xp_prod]
    show xpJ (xpE T) (x : E) * xpJ (1 - xpE T) (x : E) = _
    rw [xp_J_orth (xp_E_orth T), add_sub_cancel, xp_J_one]
    rfl
  have hr : (ξ : Chr F E L) (ratId F E x) = 1 := hrat ⟨x, rfl⟩
  rw [← hprod, map_mul, hU, mul_one] at hr
  exact hr

end XP

end Formalism.L2.Ker
