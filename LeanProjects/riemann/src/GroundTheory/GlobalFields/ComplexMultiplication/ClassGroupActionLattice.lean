import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso

open NumberField Module
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ)

def idealLattice (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule ℤ ℂ :=
  Submodule.map σ.toIntAlgHom.toLinearMap ((I : Submodule (𝓞 K) K).restrictScalars ℤ)

theorem mem_idealLattice {I : FractionalIdeal (𝓞 K)⁰ K} {z : ℂ} :
    z ∈ idealLattice σ I ↔ ∃ x ∈ I, σ x = z :=
  Iff.rfl

theorem map_mem_idealLattice {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) :
    σ x ∈ idealLattice σ I :=
  ⟨x, hx, rfl⟩

theorem mem_of_map_mem_idealLattice {I : FractionalIdeal (𝓞 K)⁰ K} {x : K}
    (hx : σ x ∈ idealLattice σ I) : x ∈ I := by
  obtain ⟨y, hy, e⟩ := (mem_idealLattice σ).1 hx
  rwa [← σ.injective e]

theorem idealLattice_mul (I J : FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice σ (I * J) = idealLattice σ I * idealLattice σ J := by
  rw [idealLattice, FractionalIdeal.coe_mul, Submodule.restrictScalars_mul, Submodule.map_mul]
  rfl

def cmRing : Subring ℂ := (σ.comp (algebraMap (𝓞 K) K)).range

theorem mem_cmRing {z : ℂ} : z ∈ cmRing σ ↔ ∃ a : 𝓞 K, σ (algebraMap (𝓞 K) K a) = z :=
  Iff.rfl

def cmRingEquiv : 𝓞 K ≃+* cmRing σ :=
  RingEquiv.ofBijective (σ.comp (algebraMap (𝓞 K) K)).rangeRestrict
    ⟨fun a b h ↦ (FaithfulSMul.algebraMap_injective (𝓞 K) K) (σ.injective (congrArg Subtype.val h)),
      (σ.comp (algebraMap (𝓞 K) K)).rangeRestrict_surjective⟩

theorem cmRingEquiv_apply (a : 𝓞 K) : (cmRingEquiv σ a : ℂ) = σ (algebraMap (𝓞 K) K a) :=
  rfl

section Quadratic

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]
include hK

theorem exists_rat_eq_of_im_eq_zero {x : K} (hx : (σ x).im = 0) : ∃ q : ℚ, algebraMap ℚ K q = x := by
  by_contra hq
  push_neg at hq
  have hind : LinearIndependent ℚ ![1, x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hq (-(s / t))
      rw [Algebra.algebraMap_eq_smul_one] at *
      have : t • x = -(s • (1 : K)) := eq_neg_of_add_eq_zero_right hst
      calc (-(s / t)) • (1 : K) = t⁻¹ • (-(s • (1 : K))) := by
            rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
        _ = x := by rw [← this, smul_smul, inv_mul_cancel₀ ht, one_smul]
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by rw [hK]; rfl)
  have hreal : ∀ y : K, (σ y).im = 0 := by
    intro y
    rw [← b.sum_repr y, Fin.sum_univ_two]
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, Rat.smul_def, map_mul, map_one,
      mul_one, map_ratCast, Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re,
      hx, Complex.one_im, zero_mul, mul_zero, add_zero]
  have hR : ComplexEmbedding.IsReal σ := by
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
    exact hreal y
  exact InfinitePlace.isComplex_mk_iff.mp (IsTotallyComplex.isComplex _) hR

theorem exists_ringOfIntegers_not_rat : ∃ θ : 𝓞 K, ∀ q : ℚ, algebraMap ℚ K q ≠ algebraMap (𝓞 K) K θ := by
  by_contra hall
  push_neg at hall
  have hsurj : ∀ x : K, ∃ q : ℚ, algebraMap ℚ K q = x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    obtain ⟨qa, ha⟩ := hall a
    obtain ⟨qb, hb⟩ := hall b
    exact ⟨qa / qb, by rw [map_div₀, ha, hb]⟩
  have htop : (⊥ : Subalgebra ℚ K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨q, rfl⟩ := hsurj x
    exact Subalgebra.algebraMap_mem _ q
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
  omega

omit [IsTotallyComplex K] in
theorem card_chooseBasisIndex (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Fintype.card (Free.ChooseBasisIndex ℤ I) = 2 := by
  rw [← hK, ← finrank_eq_card_basis (basisOfFractionalIdeal K I)]

def idealBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Basis (Fin 2) ℚ K :=
  (basisOfFractionalIdeal K I).reindex (Fintype.equivFinOfCardEq (card_chooseBasisIndex hK I))

omit [IsTotallyComplex K] in
theorem mem_span_idealBasis {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K} :
    x ∈ Submodule.span ℤ (Set.range (idealBasis hK I)) ↔ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [idealBasis, Basis.range_reindex]
  exact mem_span_basisOfFractionalIdeal K

omit [IsTotallyComplex K] in
theorem idealBasis_mem (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (i : Fin 2) :
    idealBasis hK I i ∈ (I : FractionalIdeal (𝓞 K)⁰ K) :=
  (mem_span_idealBasis hK).1 (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_real {a c : K} (h : LinearIndependent ℚ ![a, c]) :
    LinearIndependent ℝ ![σ a, σ c] := by
  have ha : a ≠ 0 := by simpa using h.ne_zero 0
  have hσa : σ a ≠ 0 := (map_ne_zero σ).2 ha
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero, Complex.real_smul, mul_eq_zero] at hst
    exact ⟨by exact_mod_cast hst.resolve_right hσa, rfl⟩
  · exfalso
    rw [Complex.real_smul, Complex.real_smul] at hst
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hc : σ (c / a) = ((-(s / t) : ℝ) : ℂ) := by
      rw [map_div₀, div_eq_iff hσa]
      push_cast
      field_simp
      linear_combination hst
    obtain ⟨q, hq⟩ := exists_rat_eq_of_im_eq_zero σ hK (x := c / a) (by rw [hc, Complex.ofReal_im])
    have hq' : (q : K) = c / a := hq
    have e : q • a + (-1 : ℚ) • c = 0 := by
      rw [Rat.smul_def, Rat.smul_def, hq', div_mul_cancel₀ _ ha]
      simp
    exact absurd (h q (-1) e).2 (by norm_num)

def idealPeriodPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : PeriodPair where
  ω₁ := σ (idealBasis hK I 0)
  ω₂ := σ (idealBasis hK I 1)
  indep := by
    apply linearIndependent_real σ hK
    have := (idealBasis hK I).linearIndependent
    convert this using 1
    ext i
    fin_cases i <;> rfl

theorem lattice_idealPeriodPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (idealPeriodPair σ hK I).lattice = idealLattice σ I := by
  ext z
  rw [PeriodPair.mem_lattice, mem_idealLattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m • idealBasis hK I 0 + n • idealBasis hK I 1, ?_, ?_⟩
    · rw [← FractionalIdeal.mem_coe]
      exact Submodule.add_mem _
        (Submodule.smul_of_tower_mem _ m (FractionalIdeal.mem_coe.2 (idealBasis_mem hK I 0)))
        (Submodule.smul_of_tower_mem _ n (FractionalIdeal.mem_coe.2 (idealBasis_mem hK I 1)))
    · simp [idealPeriodPair, zsmul_eq_mul]
  · rintro ⟨x, hx, rfl⟩
    rw [← mem_span_idealBasis hK (I := I), Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c 0, c 1, ?_⟩
    simp [Fin.sum_univ_two, idealPeriodPair, zsmul_eq_mul]

theorem latticeEnd_idealPeriodPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    latticeEnd (idealPeriodPair σ hK I) = cmRing σ := by
  ext α
  show (∀ l ∈ (idealPeriodPair σ hK I).lattice, α * l ∈ (idealPeriodPair σ hK I).lattice) ↔ _
  rw [lattice_idealPeriodPair]
  constructor
  · intro hα
    set x₀ := idealBasis hK I 0
    have hx₀ : x₀ ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := idealBasis_mem hK I 0
    have hx₀0 : x₀ ≠ 0 := (idealBasis hK I).ne_zero 0
    obtain ⟨y, -, hy⟩ := (mem_idealLattice σ).1 (hα _ (map_mem_idealLattice σ hx₀))
    set k := y / x₀
    have hαk : α = σ k := by
      rw [map_div₀, hy, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hx₀0)]
    have hkI : ∀ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), k * x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
      intro x hx
      apply mem_of_map_mem_idealLattice σ
      rw [map_mul, ← hαk]
      exact hα _ (map_mem_idealLattice σ hx)
    have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) ≤ I := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hz
      exact hkI x hx
    have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≤ 1 := by
      calc FractionalIdeal.spanSingleton (𝓞 K)⁰ k
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) *
            ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [mul_assoc, Units.mul_inv, mul_one]
        _ ≤ (I : FractionalIdeal (𝓞 K)⁰ K) *
            ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
            mul_le_mul_left h1 _
        _ = 1 := Units.mul_inv I
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1
      (FractionalIdeal.spanSingleton_le_iff_mem.1 h2)
    exact ⟨a, by rw [RingHom.comp_apply, ha, hαk]⟩
  · rintro ⟨a, rfl⟩ l hl
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ).1 hl
    rw [RingHom.comp_apply, ← map_mul, ← Algebra.smul_def]
    exact map_mem_idealLattice σ (Submodule.smul_mem _ a hx)

theorem exists_idealLattice_of_latticeEnd_eq (L : PeriodPair) (hL : latticeEnd L = cmRing σ) :
    ∃ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℂ), c ≠ 0 ∧
      (L.lattice : Set ℂ) = (c * ·) '' idealLattice σ I := by
  have hω : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  obtain ⟨θ, hθ⟩ := exists_ringOfIntegers_not_rat hK (K := K)
  have hθL : σ (algebraMap (𝓞 K) K θ) ∈ latticeEnd L := by rw [hL]; exact ⟨θ, rfl⟩
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 (hθL _ L.ω₁_mem_lattice)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hθ m
    apply σ.injective
    simp only [Int.cast_zero, zero_mul, add_zero] at hmn
    have h0 : (σ (algebraMap (𝓞 K) K θ) - m) * L.ω₁ = 0 := by linear_combination -hmn
    have h2 : σ (algebraMap (𝓞 K) K θ) = m := by
      linear_combination (mul_eq_zero.1 h0).resolve_right hω
    rw [h2]
    simp
  set y : K := (algebraMap (𝓞 K) K θ - m) / n
  have hy : σ y * L.ω₁ = L.ω₂ := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [show σ y = (σ (algebraMap (𝓞 K) K θ) - m) / n by simp [y], div_mul_eq_mul_div,
      div_eq_iff hn']
    linear_combination -hmn

  let M : Submodule (𝓞 K) K :=
    { carrier := {x | σ x * L.ω₁ ∈ L.lattice}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_add, add_mul] at *
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a x hx ↦ by
        simp only [Set.mem_setOf_eq] at *
        rw [Algebra.smul_def, map_mul, mul_assoc]
        have ha : σ (algebraMap (𝓞 K) K a) ∈ latticeEnd L := by rw [hL]; exact ⟨a, rfl⟩
        exact ha _ hx }
  have hmem : ∀ x : K, x ∈ M ↔ σ x * L.ω₁ ∈ L.lattice := fun _ ↦ Iff.rfl
  have h1 : (1 : K) ∈ M := by rw [hmem, map_one, one_mul]; exact L.ω₁_mem_lattice
  have hyM : y ∈ M := by rw [hmem, hy]; exact L.ω₂_mem_lattice
  have hM : ∀ x ∈ M, ∃ a b : ℤ, x = a + b * y := by
    intro x hx
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 ((hmem x).1 hx)
    refine ⟨a, b, σ.injective ?_⟩
    apply mul_right_cancel₀ hω
    rw [← hab, map_add, map_mul, map_intCast, map_intCast, add_mul, mul_assoc, hy]
  have hspan : M = Submodule.span (𝓞 K) {1, y} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, b, rfl⟩ := hM x hx
      refine add_mem ?_ ?_
      · rw [← mul_one (a : K), ← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ a (Submodule.subset_span (by simp))
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ b (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact h1
      · exact hyM
  have hfg : M.FG := by
    rw [hspan]
    exact Submodule.fg_span (Set.toFinite _)
  let I₀ : FractionalIdeal (𝓞 K)⁰ K := ⟨M, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI₀ : I₀ ≠ 0 := by
    intro h
    have : (1 : K) ∈ I₀ := h1
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  refine ⟨Units.mk0 I₀ hI₀, L.ω₁, hω, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
    refine ⟨σ (a + b * y), map_mem_idealLattice σ (x := a + b * y) ?_, ?_⟩
    · show (a + b * y : K) ∈ M
      rw [hspan]
      refine add_mem ?_ ?_
      · rw [← mul_one (a : K), ← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ a (Submodule.subset_span (by simp))
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ b (Submodule.subset_span (by simp))
    · rw [map_add, map_mul, map_intCast, map_intCast]
      linear_combination (b : ℂ) * hy
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ).1 hw
    rw [mul_comm]
    exact (hmem x).1 hx

theorem latticeEnd_eq_cmRing_of_ringEquiv (L : PeriodPair) (e : latticeEnd L ≃+* 𝓞 K) :
    latticeEnd L = cmRing σ := by
  have : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  let g : 𝓞 K →+* ℂ := (latticeEnd L).subtype.comp e.symm.toRingHom
  have hg : Function.Injective g := Subtype.val_injective.comp e.symm.injective
  let τ : K →+* ℂ := IsFractionRing.lift hg
  have hτ : ∀ a : 𝓞 K, τ (algebraMap (𝓞 K) K a) = g a := IsFractionRing.lift_algebraMap hg

  have hrange : ∀ (φ ψ : K →+* ℂ), ∀ x : K, ∃ y : K, ψ y = φ x := by
    intro φ ψ x
    have hN : Normal ℚ K := Algebra.IsQuadraticExtension.normal ℚ K
    let E : IntermediateField ℚ ℂ := ψ.toRatAlgHom.fieldRange
    have e₁ : K ≃ₐ[ℚ] E := AlgEquiv.ofInjectiveField ψ.toRatAlgHom
    have hE := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ E
      (by convert Normal.of_algEquiv (h := hN) e₁; exact Subsingleton.elim _ _)
      (φ.toRatAlgHom.comp e₁.symm.toAlgHom)
    have hx : φ x ∈ (φ.toRatAlgHom.comp e₁.symm.toAlgHom).fieldRange := ⟨e₁ x, by simp⟩
    have hx' : φ x ∈ E := hE ▸ hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y, hy⟩

  have hint : ∀ (φ : K →+* ℂ) (y : K), IsIntegral ℤ (φ y) → ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = y := by
    intro φ y hy
    have : IsIntegral ℤ y := (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 hy
    exact ⟨⟨y, (mem_integralClosure_iff ℤ K).2 this⟩, rfl⟩
  have hintσ : ∀ (φ : K →+* ℂ) (a : 𝓞 K), IsIntegral ℤ (φ (algebraMap (𝓞 K) K a)) := by
    intro φ a
    exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).2 a.isIntegral_coe
  ext z
  constructor
  · intro hz
    set a := e ⟨z, hz⟩
    have hza : g a = z := by simp [g, a]
    obtain ⟨y, hy⟩ := hrange τ σ (algebraMap (𝓞 K) K a)
    have hyint : IsIntegral ℤ (σ y) := by rw [hy]; exact hintσ τ a
    obtain ⟨b, rfl⟩ := hint σ y hyint
    refine ⟨b, ?_⟩
    rw [RingHom.comp_apply, hy, hτ, hza]
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := hrange σ τ (algebraMap (𝓞 K) K a)
    have hyint : IsIntegral ℤ (τ y) := by rw [hy]; exact hintσ σ a
    obtain ⟨b, rfl⟩ := hint τ y hyint
    rw [RingHom.comp_apply, ← hy, hτ]
    exact (e.symm b).2

theorem classGroup_mk_eq_iff (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K I = ClassGroup.mk K J ↔
      ∃ c : ℂ, c ≠ 0 ∧ (idealLattice σ J : Set ℂ) = (c * ·) '' idealLattice σ I := by
  constructor
  · intro h
    have h1 : ClassGroup.mk K (I⁻¹ * J) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rw [ClassGroup.mk_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1.principal
    have hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) := by
      have e : ((I⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ k := by
        apply FractionalIdeal.coeToSubmodule_injective
        show ((↑(I⁻¹ * J) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
          ((FractionalIdeal.spanSingleton (𝓞 K)⁰ k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
        rw [FractionalIdeal.coe_spanSingleton]
        exact hk
      calc (J : FractionalIdeal (𝓞 K)⁰ K)
          = (I : FractionalIdeal (𝓞 K)⁰ K) * ((I⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
              FractionalIdeal (𝓞 K)⁰ K) := by
            rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
        _ = _ := by rw [e, mul_comm]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [FractionalIdeal.spanSingleton_zero, zero_mul] at hJ
      exact J.ne_zero hJ
    refine ⟨σ k, (map_ne_zero σ).2 hk0, ?_⟩
    ext z
    simp only [SetLike.mem_coe, Set.mem_image, mem_idealLattice, hJ, FractionalIdeal.mem_singleton_mul]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨σ y, ⟨y, hy, rfl⟩, (map_mul σ k y).symm⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨k * y, ⟨y, hy, rfl⟩, map_mul σ k y⟩
  · rintro ⟨c, hc, hJ⟩
    obtain ⟨x₀, hx₀, hx₀0⟩ : ∃ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), x ≠ 0 :=
      ⟨idealBasis hK I 0, idealBasis_mem hK I 0, (idealBasis hK I).ne_zero 0⟩
    have hcx : c * σ x₀ ∈ (idealLattice σ J : Set ℂ) := by
      rw [hJ]; exact ⟨σ x₀, map_mem_idealLattice σ hx₀, rfl⟩
    obtain ⟨y₀, -, hy₀⟩ := (mem_idealLattice σ).1 hcx
    set k := y₀ / x₀
    have hck : c = σ k := by
      rw [map_div₀, hy₀, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hx₀0)]
    have hk0 : k ≠ 0 := by
      rintro h
      rw [h, map_zero] at hck
      exact hc hck
    have hJk : (J : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) := by
      ext x
      rw [FractionalIdeal.mem_singleton_mul]
      constructor
      · intro hx
        have : σ x ∈ (idealLattice σ J : Set ℂ) := map_mem_idealLattice σ hx
        rw [hJ] at this
        obtain ⟨w, hw, hwx⟩ := this
        obtain ⟨y, hy, rfl⟩ := (mem_idealLattice σ).1 hw
        refine ⟨y, hy, σ.injective ?_⟩
        rw [← hwx, map_mul, hck]
      · rintro ⟨y, hy, rfl⟩
        apply mem_of_map_mem_idealLattice σ
        have : c * σ y ∈ (idealLattice σ J : Set ℂ) := by
          rw [hJ]; exact ⟨σ y, map_mem_idealLattice σ hy, rfl⟩
        rwa [map_mul, ← hck]
    have hJ' : J = toPrincipalIdeal (𝓞 K) K (Units.mk0 k hk0) * I := by
      apply Units.ext
      rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hJk]
    rw [hJ', map_mul]
    have : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K (Units.mk0 k hk0)) = 1 := by
      rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨k, rfl⟩⟩
    rw [this, one_mul]

end Quadratic

end Elliptic
end GroundTheory.Global
