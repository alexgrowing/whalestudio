import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldAlternant
import GroundTheory.AutomorphicForms.SatakeNormalized
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.AutomorphicForms.AffineBruhat
import GroundTheory.AutomorphicForms.MeasuresGL

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

noncomputable local instance fintypeResidue : Fintype 𝓀[F] := Fintype.ofFinite _

theorem torusPow_mul_mul_neg_apply (l : Fin n → ℤ) (g : GL (Fin n) F) (a b : Fin n) :
    ((torusPow F n l * g * torusPow F n (-l) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      π ^ (l a - l b) * g a b := by
  rw [Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, mul_diagonal, diagonal_mul,
    Pi.neg_apply, zpow_sub₀ (uniformizer_ne_zero F), _root_.zpow_neg, div_eq_mul_inv]
  ring

theorem torusPow_conj_unipC_mem {l : Fin n → ℤ} (hl : Antitone l) (S : Finset (Fin n))
    (c : Pairs S → 𝓀[F]) :
    torusPow F n l * unipC S c * torusPow F n (-l) ∈ unipotent F n ⊓ integralGL F n := by
  rw [mem_unipotent_inf_integralGL_iff]
  have hN : torusPow F n l * unipC S c * torusPow F n (-l) ∈ unipotent F n := by
    rw [torusPow_neg, torusPow]
    exact diagGL_mul_mul_inv_mem_unipotent F n (unipC_mem_unipotent S c) _
  refine ⟨hN, fun a b => ?_⟩
  by_cases hab : a ≤ b
  · rw [torusPow_mul_mul_neg_apply]
    refine Subring.mul_mem _ (zpow_mem_of_nonneg (by linarith [hl hab])) ?_
    rw [coe_unipC, Matrix.add_apply]
    refine Subring.add_mem _ ?_ (cMat_mem c a b)
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hN.1 (show id b < id a from lt_of_not_ge hab)]
    exact Subring.zero_mem _

theorem torusPow_mul_gMat (l : Fin n → ℤ) (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    torusPow F n l * gMat S c =
      (torusPow F n l * unipC S c * torusPow F n (-l)) * torusPow F n (l + lamS S) := by
  rw [gMat, torusPow_add, torusPow_neg]
  group

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem minusculeHecke_apply (r : ℕ) (x : GL (Fin n) F) :
    (minusculeHecke μ r : HeckeAlgebra μ) x = (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) x :=
  rfl

theorem integral_minusculeHecke_mul {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (g : GL (Fin n) F) (r : ℕ) :
    ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) ∂μ =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[F], f (g * gMat S c) := by
  classical
  set Φ : GL (Fin n) F → ℂ := fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) with hΦ
  have hcs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [hΦ, minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  have hK : ∀ x, ∀ k ∈ integralOpen F n, Φ (x * k) = Φ x := by
    intro x k hk
    simp only [hΦ]
    rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs hK,
    Complex.real_smul]
  congr 1
  set Cs : Finset (GL (Fin n) F ⧸ integralGL F n) := (Finset.univ.powersetCard r).biUnion
    fun S => Finset.univ.image fun c : Pairs S → 𝓀[F] => (QuotientGroup.mk (gMat S c) : _)
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n, Φ x.out) = _
  rw [finsum_eq_sum_of_support_subset (s := Cs)]
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun S hS => ?_
      have hSr := (Finset.mem_powersetCard.1 hS).2
      rw [Finset.sum_image fun c _ c' _ h => gMat_injective S h]
      refine Finset.sum_congr rfl fun c _ => ?_
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (gMat S c)
      rw [hk, hK _ k k.2]
      simp only [hΦ, minusculeHecke_apply]
      rw [Set.indicator_of_mem (hSr ▸ gMat_mem_minusculeSet S c), one_mul]
    · intro S _ S' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨c', -, hc'⟩ := Finset.mem_image.1 hx'
      have := congrArg (fun x : GL (Fin n) F ⧸ integralGL F n => iwasawaExponent F n x.out) hc'
      simp only [iwasawaExponent_out, iwasawaExponent_gMat] at this
      exact hne (lamS_injective this).symm
  · intro x hx
    have hm : x.out ∈ minusculeSet F n r := by
      by_contra hm
      apply hx
      simp only [hΦ, minusculeHecke_apply, Set.indicator_of_notMem hm, zero_mul]
    obtain ⟨S, hS, c, hc⟩ := exists_gMat hm
    rw [QuotientGroup.out_eq'] at hc
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩,
      Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩⟩

def kappa (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (S : Finset (Fin n)) : ℕ :=
  Nat.card (Pairs S → 𝓀[F])

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem kappa_pos (S : Finset (Fin n)) : 0 < kappa F S := by
  have : Nonempty 𝓀[F] := ⟨0⟩
  exact Nat.card_pos

theorem sum_gMat_torusPow {f : GL (Fin n) F → ℂ}
    (hN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, f (u * g) = f g)
    {l : Fin n → ℤ} (hl : Antitone l) (S : Finset (Fin n)) :
    ∑ c : Pairs S → 𝓀[F], f (torusPow F n l * gMat S c) =
      (kappa F S : ℂ) * f (torusPow F n (l + lamS S)) := by
  simp only [torusPow_mul_gMat, hN _ (torusPow_conj_unipC_mem hl S _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, kappa, Nat.card_eq_fintype_card]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem kappa_mul_halfModulus {r : ℕ} (hr : r ≤ n) {S : Finset (Fin n)} (hS : S.card = r) :
    (kappa F S : ℂ) * halfModulus F (lamS S) = sqrtQ F ^ (r * (n - r)) := by
  classical
  have hcard : kappa F S = qF F ^ Fintype.card (Pairs S) := by
    rw [kappa, Nat.card_fun, qF, Nat.card_eq_fintype_card (α := Pairs S)]
  have hrho : rhoPair (lamS S) = (r : ℤ) * ((n : ℤ) - 1) - 2 * ∑ i ∈ S, ((i : ℕ) : ℤ) := by
    rw [rhoPair]
    simp only [lamS_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, hS, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have h2 : ((S.card.choose 2 : ℕ) : ℤ) * 2 = (r : ℤ) * ((r : ℤ) - 1) := by
    rw [hS]
    have h := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)
    rw [← Nat.choose_two_right] at h
    rcases Nat.eq_zero_or_pos r with h0 | hr0
    · subst h0
      simp
    · have : ((r.choose 2 * 2 : ℕ) : ℤ) = ((r * (r - 1) : ℕ) : ℤ) := by rw [h]
      push_cast [Nat.cast_sub hr0] at this
      linarith
  have h3 : ((∑ i ∈ S, (n - 1 - (i : ℕ)) : ℕ) : ℤ) =
      (r : ℤ) * ((n : ℤ) - 1) - ∑ i ∈ S, ((i : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl fun (i : Fin n) (_ : i ∈ S) =>
      (show ((n - 1 - (i : ℕ) : ℕ) : ℤ) = ((n : ℤ) - 1) - ((i : ℕ) : ℤ) by have := i.2; omega)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, hS, nsmul_eq_mul]
    ring
  have h1 : (Fintype.card (Pairs S) : ℤ) + (S.card.choose 2 : ℕ) =
      ((∑ i ∈ S, (n - 1 - (i : ℕ)) : ℕ) : ℤ) := by
    exact_mod_cast card_pairs_add_choose S
  rw [hcard, halfModulus_eq, Nat.cast_pow, ← sqrtQ_sq, ← pow_mul, ← zpow_natCast (sqrtQ F) (2 * _),
    ← zpow_add₀ sqrtQ_ne_zero, ← zpow_natCast]
  congr 1
  rw [hrho]
  push_cast [Nat.cast_sub hr]
  linarith

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem evalAt_esymmL (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      monomialChar (lamS S) z := by
  rw [esymmL, map_sum]
  simp only [monomial, evalAt_single, one_mul]

theorem evalAt_satakeTransform_minusculeHecke (z : Fin n → ℂˣ) {r : ℕ} (hr : r ≤ n) :
    evalAt z (satakeTransform μ (minusculeHecke μ r)) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (r * (n - r)) *
        evalAt z (esymmL n r) := by
  classical
  rw [satakeTransform_apply, satake_minusculeHecke]
  simp only [map_smul, map_sum, smul_eq_mul, evalAt_esymmL]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSr := (Finset.mem_powersetCard.1 hS).2
  rw [monomial, normalize_single, evalAt_single, one_mul, ← kappa_mul_halfModulus hr hSr, kappa]
  ring

theorem exists_lt_succ_of_not_antitone {μ : Fin n → ℤ} (h : ¬ Antitone μ) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ μ i < μ j := by
  by_contra hne
  push Not at hne
  exact h (antitone_of_forall_succ_le hne)

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in

theorem psiN_eq_one_of_mem {ψ₀ : AddChar F ℂ} (hψ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) {u : GL (Fin n) F}
    (hu : u ∈ unipotent F n ⊓ integralGL F n) : Whittaker.psiN ψ₀ u = 1 := by
  rw [Whittaker.psiN]
  refine hψ _ (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
  split_ifs
  · exact ((mem_unipotent_inf_integralGL_iff F n).1 hu).2 i j
  · exact Subring.zero_mem _

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem eq_zero_of_not_antitone {ψ₀ : AddChar F ℂ} (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1)
    {W : GL (Fin n) F → ℂ} (hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g)
    (hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g) {μ : Fin n → ℤ} (hμ : ¬ Antitone μ) :
    W (torusPow F n μ) = 0 := by
  obtain ⟨i, j, hij, hlt⟩ := exists_lt_succ_of_not_antitone hμ
  obtain ⟨x, hx, hψx⟩ := hψ₁
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hij' : i < j := Fin.lt_def.2 (by omega)
  set u := Whittaker.rootElt i j x
  have huN : u ∈ unipotent F n := Whittaker.rootElt_mem_unipotent hij' x
  set k := torusPow F n (-μ) * u * torusPow F n (-(-μ))
  have hk : k ∈ integralGL F n := by
    have hkN : k ∈ unipotent F n := by
      show torusPow F n (-μ) * u * torusPow F n (-(-μ)) ∈ unipotent F n
      rw [neg_neg, show torusPow F n μ = (torusPow F n (-μ))⁻¹ by rw [torusPow_neg, inv_inv],
        torusPow]
      exact diagGL_mul_mul_inv_mem_unipotent F n huN _
    refine ((mem_unipotent_inf_integralGL_iff F n).2 ⟨hkN, fun a b => ?_⟩).2
    rw [show k = torusPow F n (-μ) * u * torusPow F n (-(-μ)) from rfl, torusPow_mul_mul_neg_apply,
      Whittaker.rootElt_apply hne]
    simp only [Pi.neg_apply]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq, if_neg (fun h => hne (h.1.trans h.2.symm)), sub_self, zpow_zero,
        add_zero, one_mul]
      exact Subring.one_mem _
    · rw [Matrix.one_apply_ne hab, zero_add]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [show -μ i - -μ j = (-μ i - -μ j - 1) + 1 by ring, zpow_add₀ (uniformizer_ne_zero F),
          zpow_one, mul_assoc]
        exact Subring.mul_mem _ (zpow_mem_of_nonneg (by linarith)) hx
      · rw [mul_zero]
        exact Subring.zero_mem _
  have heq : torusPow F n μ * k = u * torusPow F n μ := by
    simp only [k, neg_neg, torusPow_neg]
    group
  have h1 := hWK (torusPow F n μ) k hk
  rw [heq, hWN u huN, Whittaker.psiN_rootElt ψ₀ hne, if_pos hij] at h1
  have : (ψ₀ x - 1) * W (torusPow F n μ) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hψx)

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem permGL_conj_torusPow (σ : Equiv.Perm (Fin n)) (μ : Fin n → ℤ) :
    (permGL F σ)⁻¹ * torusPow F n μ * permGL F σ = torusPow F n (μ ∘ σ) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Units.val_mul, mul_permGL_apply, ← map_inv, Units.val_mul, permGL_mul_apply, inv_inv,
    coe_torusPow, coe_torusPow, diagonal_apply, diagonal_apply]
  simp only [Function.comp_apply, σ.injective.eq_iff]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem continuous_of_mul_right_invariant {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open f).2 fun g => ?_)
  refine ⟨g • (integralGL F n : Set (GL (Fin n) F)), (isOpen_integralGL F n).smul g,
    Set.mem_smul_set.2 ⟨1, (integralGL F n).one_mem, by simp⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact hf g k hk

end Spherical

end GroundTheory.Automorphic
