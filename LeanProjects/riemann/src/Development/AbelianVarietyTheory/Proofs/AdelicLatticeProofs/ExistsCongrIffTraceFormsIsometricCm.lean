import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuaternaryOfCoordinates
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuedTernaryLtOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroFiveOfValuation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometric

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

theorem isotropic_ternary_of_units (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (a : Fin 3 → v.adicCompletion F) (ha : ∀ i, Valued.v (a i) = 1) :
    ∃ x : Fin 3 → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, -, ⟨k, hk⟩, hx⟩ := exists_unit_valued_ternary_lt_one F v (Matrix.diagonal a) (by
    intro i j
    by_cases h : i = j
    · subst h; simp [ha]
    · simp [Matrix.diagonal_apply_ne _ h])
  have e : ∑ i, ∑ j, Matrix.diagonal a i j * x i * x j = ∑ i, a i * x i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne _ hj.symm]) (by simp)]
    simp [sq, mul_assoc]
  rw [e] at hx
  set q := ∑ i, a i * x i ^ 2 with hq
  have hu : Valued.v (a k * x k ^ 2) = 1 := by simp [ha, hk]
  have hu0 : a k * x k ^ 2 ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, mul_one]
  have hlt : Valued.v (1 - q / (a k * x k ^ 2) - 1) < 1 := by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, hu, div_one]; exact hx
  obtain ⟨s, hs⟩ := isSquare_of_valued_sub_one_lt F v (1 - q / (a k * x k ^ 2)) (by rwa [h4])
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [hs] at hlt
    simp at hlt
  have hxk : x k ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  refine ⟨Function.update x k (x k * s), fun hc => ?_, ?_⟩
  · have := congrFun hc k
    simp [hs0, hxk] at this
  · have h1 : a k * x k ^ 2 * (s * s) = a k * x k ^ 2 - q := by
      rw [← hs, mul_sub, mul_one, mul_div_cancel₀ _ hu0]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hq ⊢
    rw [Finset.sum_congr rfl (g := fun i => a i * x i ^ 2)
      (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]), Function.update_self]
    linear_combination h1 - hq

theorem isotropic_adicCompletion_of_five_le (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {ι : Type*} [Fintype ι] (hι : 5 ≤ Fintype.card ι)
    (a : ι → v.adicCompletion F) :
    ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hι)
  exact isotropic_of_injective e e.injective
    (exists_zero_five_of_valuation two_ne_zero Valued.v (v.valuedAdicCompletion_surjective F)
      (isSquare_of_valued_sub_one_lt F v) (exists_unit_valued_ternary_lt_one F v) _)

theorem exists_norm_over_extension (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [NumberField L] [Algebra F L] {α β γ : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) {s : L} (hs : s ^ 2 = algebraMap F L (α * β * γ))
    (hr : ∀ σ : F →+* ℝ, ∃ x y z t : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - σ α * y ^ 2 - σ β * z ^ 2 + σ γ * t ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x y z t : v.adicCompletion F,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - algebraMap F _ α * y ^ 2 - algebraMap F _ β * z ^ 2 + algebraMap F _ γ * t ^ 2 = 0) :
    ∃ X Y : L, algebraMap F L β = X ^ 2 - algebraMap F L α * Y ^ 2 := by
  refine H L _ _ (by simpa using hα) (by simpa using hβ) (fun σ => ?_) (fun w => ?_)
  · obtain ⟨x, y, z, t, h0, h⟩ := hr (σ.comp (algebraMap F L))
    exact exists_norm_of_quaternary (s := σ s) (γ := σ (algebraMap F L γ)) (by simpa using hα)
      (by simpa using hβ) (by simpa using hγ) (by rw [← map_pow, hs]; simp) h0 h
  · haveI : CharZero (w.adicCompletion L) :=
      charZero_of_injective_algebraMap (algebraMap L (w.adicCompletion L)).injective
    obtain ⟨v, φ, hφ⟩ := exists_ringHom_adicCompletion F L w
    obtain ⟨x, y, z, t, h0, h⟩ := hf v
    refine exists_norm_of_quaternary (s := algebraMap L _ s)
      (γ := algebraMap L _ (algebraMap F L γ)) (x := φ x) (y := φ y) (z := φ z) (t := φ t)
      (by simpa using hα) (by simpa using hβ) (by simpa using hγ)
      (by rw [← map_pow, hs]; simp only [map_mul]) (by simpa using h0) ?_
    have := congrArg φ h
    simpa only [map_add, map_sub, map_mul, map_pow, hφ, map_zero] using this

theorem isotropic_four (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  rw [isotropic_four_iff (ha 0)]
  have hα : -(a 0 * a 1) ≠ 0 := by simp [ha]
  have hβ : -(a 0 * a 2) ≠ 0 := by simp [ha]
  have hγ : a 0 * a 3 ≠ 0 := by simp [ha]
  have hr' := fun σ : F →+* ℝ =>
    (isotropic_four_iff (a := fun i => σ (a i)) (by simpa using ha 0)).1 (hr σ)
  have hf' := fun v : HeightOneSpectrum (𝓞 F) =>
    (isotropic_four_iff (a := fun i => algebraMap F (v.adicCompletion F) (a i))
      (by simpa using ha 0)).1 (hf v)
  simp only [← map_mul, ← map_neg] at hr' hf'
  generalize -(a 0 * a 1) = α at *
  generalize -(a 0 * a 2) = β at *
  generalize a 0 * a 3 = γ at *
  by_cases hs : IsSquare (α * β * γ)
  · obtain ⟨s, hs⟩ := hs
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F F hα hβ hγ (s := s)
      (by rw [hs, sq]; rfl) hr' hf'
    refine ⟨X, Y, 1, 0, by simp, ?_⟩
    change β = X ^ 2 - α * Y ^ 2 at h
    linear_combination -h
  · have : Fact (∀ r : F, r ^ 2 ≠ α * β * γ + 0 * r) :=
      ⟨fun r h => hs ⟨r, by linear_combination -h⟩⟩
    let L := QuadraticAlgebra F (α * β * γ) 0
    have : NumberField L := NumberField.of_module_finite F L
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F L hα hβ hγ (s := ⟨0, 1⟩)
      (by ext <;> simp [sq, L]) hr' hf'
    have h1 := congrArg QuadraticAlgebra.re h
    have h2 := congrArg QuadraticAlgebra.im h
    simp [sq, L] at h1 h2
    refine exists_quaternary_of_coordinates hα hβ (X₀ := X.re) (X₁ := X.im) (Y₀ := Y.re)
      (Y₁ := Y.im) (by linear_combination h1) ?_
    linear_combination (-1 / 2 : F) * h2

end GlobalTheory.LocalQuad

namespace GlobalTheory.LocalQuad

theorem exists_value_isSquare_div (F : Type) [Field F] [NumberField F] {a a' : F} (ha : a ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (p q : (v : T) → v.1.adicCompletion F)
    (hpq : ∀ v, algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2 ≠ 0)
    (p' q' : (F →+* ℝ) → ℝ) (hpq' : ∀ σ, σ a * p' σ ^ 2 + σ a' * q' σ ^ 2 ≠ 0) :
    ∃ x y : F, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧
      (∀ v : T, IsSquare (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
        (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2))) ∧
      ∀ σ : F →+* ℝ, IsSquare (σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)) := by
  have hd := (denseRange_finite_real F T).prodMap (denseRange_finite_real F T)
  have h4 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≠ 0 := by
    intro v
    haveI : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    simp
  have h41 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≤ 1 := by
    intro v
    have h2 : Valued.v (1 + 1 : v.1.adicCompletion F) ≤ 1 :=
      Valuation.map_add_le _ (by simp) (by simp)
    rw [show (4 : v.1.adicCompletion F) = (1 + 1) * (1 + 1) by norm_num, map_mul]
    exact mul_le_one' h2 h2
  let U : Set ((((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := (⋂ v : T, {z | Valued.v ((algebraMap F _ a * z.1.1 v ^ 2 +
      algebraMap F _ a' * z.2.1 v ^ 2) / (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1)
        < Valued.v (4 : v.1.adicCompletion F)}) ∩
    ⋂ σ : F →+* ℝ, {z | 0 < (σ a * z.1.2 σ ^ 2 + σ a' * z.2.2 σ ^ 2) /
      (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · have ho : IsOpen {u : v.1.adicCompletion F | Valued.v u < Valued.v (4 : v.1.adicCompletion F)} := by
        have := Valued.isOpen_ball (v.1.adicCompletion F) (Valued.v.restrict (4 : v.1.adicCompletion F))
        simpa only [Valuation.restrict_lt_iff] using this
      exact ho.preimage (f := fun z : (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) => (algebraMap F _ a * z.1.1 v ^ 2 +
        algebraMap F _ a' * z.2.1 v ^ 2) /
          (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  obtain ⟨⟨x, y⟩, hT, hR⟩ := hd.exists_mem_open hU ⟨((p, p'), (q, q')), by
    refine ⟨Set.mem_iInter.2 fun v => ?_, Set.mem_iInter.2 fun σ => ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq v), sub_self, map_zero]
      exact zero_lt_iff.2 (h4 v)
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq' σ)]
      exact one_pos⟩
  replace hT : ∀ v : T, Valued.v (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
      (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) <
        Valued.v (4 : v.1.adicCompletion F) := by
    intro v
    simp only [map_add, map_mul, map_pow]
    exact Set.mem_iInter.1 hT v
  replace hR : ∀ σ : F →+* ℝ,
      0 < σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2) := by
    intro σ
    simp only [map_add, map_mul, map_pow]
    exact Set.mem_iInter.1 hR σ
  by_cases h0 : a * x ^ 2 + a' * y ^ 2 = 0
  · refine ⟨1, 0, by simpa using ha, fun v => ?_, fun σ => ?_⟩
    · have := (hT v).trans_le (h41 v)
      simp [h0] at this
    · have := hR σ
      simp [h0] at this
  · exact ⟨x, y, h0, fun v => isSquare_of_valued_sub_one_lt F v _ (hT v),
      fun σ => Real.isSquare_iff.2 (hR σ).le⟩

theorem finite_setOf_valued_ne_one (F : Type) [Field F] [NumberField F] {c : F} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) |
      Valued.v (algebraMap F (v.adicCompletion F) c) ≠ 1}.Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hc).preimage
    (f := FinitePlace.equivHeightOneSpectrum.symm)
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  refine h.subset fun v hv => ?_
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply]
  intro h1
  exact hv (le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h1.le)
    (Valued.toNormedField.one_le_norm_iff.1 h1.ge))

theorem isotropic_add_four (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F] (n : ℕ)
    (a : Fin (n + 4) → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin (n + 4) → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin (n + 4) → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin (n + 4) → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  induction n with
  | zero => exact isotropic_four H F a ha hr hf
  | succ n ih =>
    classical
    have split : ∀ (k : Type) [Field k] (φ : F →+* k),
        (∃ x : Fin (n + 1 + 4) → k, x ≠ 0 ∧ ∑ i, φ (a i) * x i ^ 2 = 0) →
        ∃ x y : k, φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2 ≠ 0 ∧
          ∀ μ : F, IsSquare (φ μ / (φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2)) →
          ∃ x : Fin (n + 4) → k, x ≠ 0 ∧
            ∑ i, φ ((Fin.cons μ fun j : Fin (n + 3) => a j.succ.succ : Fin (n + 4) → F) i) * x i ^ 2
              = 0 := by
      rintro k _ φ ⟨x, hx, h⟩
      haveI : CharZero k := (RingHom.charZero_iff φ.injective).1 inferInstance
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
      obtain ⟨X, Y, hXY, H⟩ := exists_value_isotropic (a := φ (a 0)) (a' := φ (a 1))
        (b := fun j : Fin (n + 2 + 1) => φ (a j.succ.succ)) (by simpa using ha 0)
        (by simpa using ha 1) (by simpa using ha _) (x := x 0) (y := x 1)
        (z := fun j => x j.succ.succ) (by
          by_contra hc
          push Not at hc
          apply hx
          funext i
          refine Fin.cases hc.1 (fun j => Fin.cases hc.2.1 (fun l => congrFun hc.2.2 l) j) i) h
      refine ⟨X, Y, hXY, fun μ hμ => ?_⟩
      refine (isotropic_succ_iff (n := n + 3)).2 ?_
      simpa using H _ hμ
    let e : Fin 3 → Fin (n + 3) := Fin.natAdd n
    have hT := (finite_setOf_valued_ne_one F (two_ne_zero (α := F))).union
      (Set.finite_iUnion fun i : Fin 3 => finite_setOf_valued_ne_one F (ha (e i).succ.succ))
    choose p q hpq hp using fun v : hT.toFinset => split _ _ (hf v.1)
    choose p' q' hpq' hp' using fun σ : F →+* ℝ => split _ _ (hr σ)
    obtain ⟨x, y, h0, h1, h2⟩ := exists_value_isSquare_div F (a' := a 1) (ha 0) _ p q hpq p' q' hpq'
    obtain ⟨t, z, hz0, hz⟩ := (isotropic_succ_iff (n := n + 3)).1 (ih
      (Fin.cons (a 0 * x ^ 2 + a 1 * y ^ 2) fun j : Fin (n + 3) => a j.succ.succ)
      (fun i => Fin.cases h0 (fun j => ha _) i) (fun σ => hp' σ _ (h2 σ)) (fun v => by
        by_cases hv : v ∈ hT.toFinset
        · exact hp ⟨v, hv⟩ _ (h1 ⟨v, hv⟩)
        · simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
            not_or, not_exists, not_not] at hv
          refine isotropic_of_injective (fun i => (e i).succ)
            ((Fin.succ_injective _).comp (Fin.natAdd_injective _ _)) ?_
          exact isotropic_ternary_of_units F v (by simpa only [map_ofNat] using hv.1) _ hv.2))
    simp only [Fin.cons_zero, Fin.cons_succ] at hz
    refine (isotropic_succ_iff (n := n + 4)).2 ⟨x * t, Fin.cons (y * t) z, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      obtain ⟨hx, hy⟩ := hc
      have hy0 : y * t = 0 := by simpa using congrFun hy 0
      rcases hz0 with ht | hz0
      · rw [mul_eq_zero_iff_right ht] at hx hy0
        simp [hx, hy0] at h0
      · exact hz0 (funext fun i => by simpa using congrFun hy i.succ)
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
      linear_combination hz

theorem isotropic_of_locally_isotropic (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F]
    [NumberField F] {ι : Type*} [Fintype ι] (hι : 4 ≤ Fintype.card ι) (a : ι → F)
    (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hι
  let e : ι ≃ Fin (n + 4) := Fintype.equivFinOfCardEq hn
  refine isotropic_of_injective e.symm e.symm.injective
    (isotropic_add_four H F n _ (fun i => ha _) (fun σ => ?_) (fun v => ?_))
  · exact isotropic_of_injective e e.injective (by simpa using hr σ)
  · exact isotropic_of_injective e e.injective (by simpa only [e.symm_apply_apply] using hf v)

theorem isotropic_of_indefinite (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    {ι : Type*} [Fintype ι] (a : ι → F) (hι : 5 ≤ Fintype.card ι) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 :=
  isotropic_of_locally_isotropic H F (by omega) a ha
    (fun σ => by
      obtain ⟨i, j, hi, hj⟩ := hr σ
      exact isotropic_real (a := fun i => σ (a i)) hi hj)
    (fun v => isotropic_adicCompletion_of_five_le F v hι _)

theorem landherr_of_hasseNormSt (H : GlobalTheory.Published.HasseNormSt) : GlobalTheory.Published.Landherr :=
  landherr_of_isotropy fun F _ _ _ _ a hι ha hr => isotropic_of_indefinite H F a hι ha hr

universe u v w in

theorem trace_forms_and_landherr :
    (∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E], (2 : E) ≠ 0 →
      ∀ c : E →+* E, (∀ t, c (c t) = t) → (∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) →
      ∀ {n : Type w} [Fintype n] [DecidableEq n] {G G' : Matrix n n E},
      (∀ a b, c (G a b) = G b a) → (∀ a b, c (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
      ((∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
        ∃ φ : (n → E) ≃ₗ[F] (n → E),
          ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x))) ∧
    (GlobalTheory.Published.HasseNormSt → ∀ (F : Type) [Field F] [NumberField F] {ι : Type w} [Fintype ι],
      4 ≤ Fintype.card ι → ∀ a : ι → F, (∀ i, a i ≠ 0) →
      (∀ σ : F →+* ℝ, ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0) →
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧
        ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) →
      ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ∧
    (GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.Landherr) :=
  ⟨fun h2 c hc hF _ _ _ _ _ hG hG' hd hd' =>
      exists_congr_iff_trace_forms_isometric h2 c hc hF hG hG' hd hd',
    fun H F _ _ _ _ hι a ha hr hf => isotropic_of_locally_isotropic H F hι a ha hr hf,
    landherr_of_hasseNormSt⟩

end GlobalTheory.LocalQuad
