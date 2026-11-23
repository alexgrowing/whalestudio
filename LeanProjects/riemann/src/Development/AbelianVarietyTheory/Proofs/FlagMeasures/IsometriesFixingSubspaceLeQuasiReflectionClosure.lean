import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfPerpEqBot

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.QReflGen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_r (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_r (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_cj (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h j) i
  simp only [hf, map_sum, map_mul, h', L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_qrefl (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (a : Fin n → E) (ha : IsUnit (hf L Hm a a)) (c : E)
    (hc : c + L.cj c + c * L.cj c * hf L Hm a a = 0) :
    ∃ g, IsQRefl L Hm a g ∧ ∀ v, g v = v + (c * hf L Hm v a) • a := by
  let g : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    { toFun := fun v => v + (c * hf L Hm v a) • a
      invFun := fun v => v + (L.cj c * hf L Hm v a) • a
      map_add' := by
        intro v w
        rw [hf_add_l]; module
      map_smul' := by
        intro r v
        rw [hf_smul_l]; simp only [RingHom.id_apply]; module
      left_inv := by
        intro v
        simp only [hf_add_l, hf_smul_l]
        rw [add_assoc, ← add_smul]
        have : c * hf L Hm v a + L.cj c * (hf L Hm v a + c * hf L Hm v a * hf L Hm a a) = 0 := by
          linear_combination hf L Hm v a * hc
        rw [this]; simp
      right_inv := by
        intro v
        simp only [hf_add_l, hf_smul_l]
        rw [add_assoc, ← add_smul]
        have : L.cj c * hf L Hm v a + c * (hf L Hm v a + L.cj c * hf L Hm v a * hf L Hm a a) = 0 := by
          linear_combination hf L Hm v a * hc
        rw [this]; simp }
  refine ⟨g, ⟨ha, ?_, c, fun v => rfl⟩, fun v => rfl⟩
  intro v w
  change hf L Hm (v + (c * hf L Hm v a) • a) (w + (c * hf L Hm w a) • a) = _
  simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, hf_cj L h]
  linear_combination hf L Hm v a * hf L Hm a w * hc

theorem unit_of_fix (L : LocE F E) {z : E} (hz : L.cj z = z) (h0 : z ≠ 0) : IsUnit z := by
  obtain ⟨a, rfl⟩ := (L.cj_fix z).1 hz
  have : a ≠ 0 := by rintro rfl; simp at h0
  exact (IsUnit.mk0 a this).map _

theorem nontriv (L : LocE F E) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := L.rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega

theorem exists_skew (L : LocE F E) :
    ∃ (δ : E) (D : F), D ≠ 0 ∧ L.cj δ = -δ ∧ δ * δ = algebraMap F E D := by
  have h1 : ∃ z : E, L.cj z ≠ z := by
    by_contra h
    push_neg at h
    have hs : Function.Surjective (Algebra.linearMap F E) := fun z => (L.cj_fix z).1 (h z)
    have := LinearMap.finrank_le_finrank_of_surjective hs
    rw [L.rank, Module.finrank_self] at this
    omega
  obtain ⟨z, hz⟩ := h1
  have hδ : L.cj (z - L.cj z) = -(z - L.cj z) := by simp [L.cj_cj]
  obtain ⟨D, hD⟩ := (L.cj_fix ((z - L.cj z) * (z - L.cj z))).1 (by rw [map_mul, hδ]; ring)
  refine ⟨z - L.cj z, D, ?_, hδ, hD.symm⟩
  rintro rfl
  haveI := L.reduced
  have : z - L.cj z = 0 := IsNilpotent.eq_zero ⟨2, by rw [pow_two, ← hD]; simp⟩
  exact hz (sub_eq_zero.1 this).symm

theorem quad_finite {K : Type} [Field K] (a b c : K) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {r : K | a * r ^ 2 + b * r + c = 0}.Finite := by
  have hp : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ≠ 0 := by
    intro h0
    apply h
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg (fun p => Polynomial.coeff p 2) h0
    · simpa using congrArg (fun p => Polynomial.coeff p 1) h0
    · simpa using congrArg (fun p => Polynomial.coeff p 0) h0
  have := Polynomial.finite_setOf_isRoot hp
  simpa [Polynomial.IsRoot] using this

theorem exists_norm_one [CharZero F] (L : LocE F E) (t s : E) (ht : IsUnit t) (htc : L.cj t = t) :
    ∃ u : E, u * L.cj u = 1 ∧ IsUnit (t - L.cj u * s) ∧
      IsUnit ((t - L.cj u * s) + L.cj (t - L.cj u * s)) := by
  haveI := nontriv L
  obtain ⟨δ, D, hD, hδ, hδ2⟩ := exists_skew L
  obtain ⟨τ, rfl⟩ := (L.cj_fix t).1 htc
  have hτ : τ ≠ 0 := by rintro rfl; simp at ht
  obtain ⟨A, hA⟩ := (L.cj_fix (s + L.cj s)).1 (by simp [L.cj_cj, add_comm])
  obtain ⟨B, hB⟩ := (L.cj_fix (δ * (s - L.cj s))).1 (by simp [L.cj_cj, hδ]; ring)
  obtain ⟨N, hN⟩ := (L.cj_fix (s * L.cj s)).1 (by simp [L.cj_cj, mul_comm])
  have inj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hrel : D * A ^ 2 - B ^ 2 = 4 * D * N := by
    apply inj
    simp only [map_sub, map_mul, map_pow, map_ofNat, hA, hB, hN, ← hδ2]
    ring
  have f1 := quad_finite (1 : F) 0 (-D) (by simp)
  have f2 := quad_finite (A - 2 * τ) (-2 * B) (D * (A + 2 * τ)) (by
    rintro ⟨h1, -, h3⟩
    have h4 := (mul_eq_zero.1 h3).resolve_left hD
    apply hτ
    linear_combination (1 / 4 : F) * (h4 - h1))
  have f3 := quad_finite (τ * A - (τ ^ 2 + N)) (-2 * τ * B) (D * (τ * A + (τ ^ 2 + N))) (by
    rintro ⟨h1, h2, h3⟩
    have h4 := (mul_eq_zero.1 h3).resolve_left hD
    have hA0 : A = 0 := by
      have : τ * A = 0 := by linear_combination (1 / 2 : F) * (h4 + h1)
      exact (mul_eq_zero.1 this).resolve_left hτ
    have hB0 : B = 0 := by
      have : τ * B = 0 := by linear_combination (-1 / 2 : F) * h2
      exact (mul_eq_zero.1 this).resolve_left hτ
    have hN0 : N = 0 := by
      have : D * N = 0 := by rw [hA0, hB0] at hrel; linear_combination (-1 / 4 : F) * hrel
      exact (mul_eq_zero.1 this).resolve_left hD
    apply hτ
    have : τ ^ 2 = 0 := by rw [hA0, hN0] at h1; linear_combination -h1
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this)
  obtain ⟨r, hr⟩ := ((f1.union f2).union f3).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hr
  obtain ⟨⟨r1, r2⟩, r3⟩ := hr
  have r1' : r ^ 2 - D ≠ 0 := fun h => r1 (by linear_combination h)
  set e : F := (r ^ 2 - D)⁻¹ with he
  have he1 : e * (r ^ 2 - D) = 1 := inv_mul_cancel₀ r1'
  have he2 : algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) = 1 := by
    rw [hδ2, ← map_pow, ← map_sub, ← map_mul, he1, map_one]
  set u : E := algebraMap F E e * (algebraMap F E r + δ) ^ 2 with hu
  have hcu : L.cj u = algebraMap F E e * (algebraMap F E r - δ) ^ 2 := by
    simp [hu, hδ, sub_eq_add_neg]
  have huu : u * L.cj u = 1 := by
    rw [hcu, hu]
    linear_combination (algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) + 1) * he2
  have hT : L.cj u * s + u * L.cj s = algebraMap F E (e * ((r ^ 2 + D) * A - 2 * r * B)) := by
    rw [hcu, hu]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hA, hB, ← hδ2]
    ring
  have hcb : L.cj (algebraMap F E τ - L.cj u * s) = algebraMap F E τ - u * L.cj s := by
    simp [L.cj_cj]
  clear_value u
  refine ⟨u, huu, ?_, ?_⟩
  · have : (algebraMap F E τ - L.cj u * s) * (algebraMap F E τ - u * L.cj s) =
        algebraMap F E (τ ^ 2 + N - τ * (e * ((r ^ 2 + D) * A - 2 * r * B))) := by
      rw [map_sub, map_add, map_mul (algebraMap F E), ← hT, hN, map_pow]
      linear_combination s * L.cj s * huu
    refine isUnit_of_mul_isUnit_left (y := algebraMap F E τ - u * L.cj s) ?_
    rw [this]
    refine (IsUnit.mk0 _ fun h => r3 ?_).map _
    linear_combination (-(r ^ 2 - D)) * h - τ * ((r ^ 2 + D) * A - 2 * r * B) * he1
  · have : (algebraMap F E τ - L.cj u * s) + (algebraMap F E τ - u * L.cj s) =
        algebraMap F E (2 * τ - (e * ((r ^ 2 + D) * A - 2 * r * B))) := by
      rw [map_sub, map_mul (algebraMap F E), ← hT, map_ofNat]
      ring
    rw [hcb, this]
    refine (IsUnit.mk0 _ fun h => r2 ?_).map _
    linear_combination (-(r ^ 2 - D)) * h - ((r ^ 2 + D) * A - 2 * r * B) * he1

theorem step [CharZero F] (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) (hx : IsUnit (hf L Hm x x)) (hxy : hf L Hm y y = hf L Hm x x) :
    ∃ (u : E) (σ ρ : (Fin n → E) ≃ₗ[E] (Fin n → E)),
      IsQRefl L Hm (x + (-u) • y) σ ∧ IsQRefl L Hm y ρ ∧ σ x = ρ y := by
  obtain ⟨u, huu, hb, hbb⟩ := exists_norm_one L (hf L Hm x x) (hf L Hm x y) hx (hf_cj L h x x)
  have haa : hf L Hm (x + (-u) • y) (x + (-u) • y) =
      (hf L Hm x x - L.cj u * hf L Hm x y) + L.cj (hf L Hm x x - L.cj u * hf L Hm x y) := by
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, map_sub, map_neg, hf_cj L h,
      L.cj_cj, hxy]
    linear_combination hf L Hm x x * huu
  have hxa : hf L Hm x (x + (-u) • y) = hf L Hm x x - L.cj u * hf L Hm x y := by
    simp only [hf_add_r, hf_smul_r, map_neg]; ring
  obtain ⟨b, hb1⟩ := hb.exists_left_inv
  obtain ⟨t, ht1⟩ := hx.exists_left_inv
  have hb2 := congrArg L.cj hb1
  have ht2 := congrArg L.cj ht1
  rw [map_mul, map_one] at hb2 ht2
  rw [hf_cj L h] at ht2
  have htt : L.cj t = t := by linear_combination t * ht2 - L.cj t * ht1
  obtain ⟨σ, hσ, hσ'⟩ := exists_qrefl L h (x + (-u) • y) (haa ▸ hbb) (-b) (by
    rw [haa, map_neg]
    linear_combination L.cj b * hb1 + b * hb2)
  obtain ⟨ρ, hρ, hρ'⟩ := exists_qrefl L h y (hxy ▸ hx) ((u - 1) * t) (by
    rw [hxy, map_mul, map_sub, map_one, htt]
    linear_combination (u - 1) * (L.cj u - 1) * t * ht1 + t * huu)
  refine ⟨u, σ, ρ, hσ, hρ, ?_⟩
  rw [hσ', hρ', hxa, hxy, neg_mul, hb1, mul_assoc, ht1]
  module

theorem qrefl_fix (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} {a : Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : IsQRefl L Hm a g) {v : Fin n → E}
    (hv : hf L Hm v a = 0) : g v = v := by
  obtain ⟨-, -, c, hc⟩ := hg
  rw [hc, hv]; simp

theorem induct [CharZero F] (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (Y : Submodule E (Fin n → E)) (hY : Y ⊔ perp L Hm Y = ⊤) {d : ℕ} (w : Fin d → Fin n → E)
    (hw : Submodule.span E (Set.range w) = perp L Hm Y) (hu : ∀ i, IsUnit (hf L Hm (w i) (w i)))
    (ho : ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0) (S : Finset (Fin d)) :
    ∀ g ∈ isomG L Hm, (∀ v ∈ Y, g v = v) → (∀ j, j ∉ S → g (w j) = w j) →
      g ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} := by
  induction S using Finset.induction_on with
  | empty =>
    intro g _ h1 h2
    have : g = 1 := by
      apply LinearEquiv.toLinearMap_injective
      have hle : (⊤ : Submodule E (Fin n → E)) ≤
          LinearMap.eqLocus g.toLinearMap (1 : (Fin n → E) ≃ₗ[E] (Fin n → E)).toLinearMap := by
        rw [← hY, ← hw, sup_le_iff, Submodule.span_le]
        refine ⟨fun v hv => h1 v hv, ?_⟩
        rintro _ ⟨j, rfl⟩
        exact h2 j (by simp)
      exact LinearMap.ext fun v => hle (Submodule.mem_top (x := v))
    rw [this]; exact one_mem _
  | insert i S hi ih =>
    intro g hg h1 h2
    have hwp : w i ∈ perp L Hm Y := hw ▸ Submodule.subset_span ⟨i, rfl⟩
    have hyp : g (w i) ∈ perp L Hm Y := fun z hz => by
      rw [← h1 z hz, hg (w i) z]; exact hwp z hz
    obtain ⟨u, σ, ρ, hσ, hρ, hσρ⟩ := step L h (w i) (g (w i)) (hu i) (hg _ _)
    have hap : w i + (-u) • g (w i) ∈ perp L Hm Y := add_mem hwp (Submodule.smul_mem _ _ hyp)
    have mσ : σ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} :=
      Subgroup.subset_closure ⟨_, hap, hσ⟩
    have mρ : ρ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} :=
      Subgroup.subset_closure ⟨_, hyp, hρ⟩
    have key : ∀ v, σ v = ρ (g v) → (σ⁻¹ * ρ * g) v = v := fun v hv => by
      change σ.symm (ρ (g v)) = v
      rw [← hv, LinearEquiv.symm_apply_apply]
    have hg' := ih (σ⁻¹ * ρ * g) (mul_mem (mul_mem (inv_mem hσ.2.1) hρ.2.1) hg)
      (fun v hv => key v (by
        rw [h1 v hv, qrefl_fix L hσ (by rw [← hf_cj L h, hap v hv, map_zero]),
          qrefl_fix L hρ (by rw [← hf_cj L h, hyp v hv, map_zero])]))
      (fun j hj => key _ (by
        by_cases hji : j = i
        · rw [hji]; exact hσρ
        · have hj2 := h2 j (by simp [hji, hj])
          have h3 : hf L Hm (w j) (g (w i)) = 0 := by
            rw [← hj2, hg (w j) (w i)]; exact ho j i hji
          rw [hj2, qrefl_fix L hσ (by rw [hf_add_r, hf_smul_r, h3, ho j i hji]; simp),
            qrefl_fix L hρ h3]))
    have : g = ρ⁻¹ * σ * (σ⁻¹ * ρ * g) := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem mρ) mσ) hg'

theorem fixG_le_closure : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → fixG L Hm (Submodule.span E (Set.range x)) ≤ Subgroup.closure {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g} := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx g hg
  obtain ⟨-, hc, w, hw, hu, ho⟩ := GlobalTheory.HermOrthBasis.orth_basis_perp L Hm hH m x hx
  refine induct L hH.1 _ hc.sup_eq_top w hw hu ho Finset.univ g hg.1 (fun v hv => ?_) (by simp)
  have := hg.2.2 v hv
  rwa [Submodule.mem_bot, sub_eq_zero] at this

end GlobalTheory.HL.QReflGen
