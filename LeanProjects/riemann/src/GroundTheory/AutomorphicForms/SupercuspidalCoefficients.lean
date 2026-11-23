import Mathlib
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.AutomorphicForms.IwahoriFactorization
import GroundTheory.AutomorphicForms.SmoothRepContragredient

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}

theorem mk_fixedProj_eq (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z)
    {w : V} (hwNbar : ∀ z ∈ K ⊓ Nbar, ρ z w = w)
    (hwM : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w) :
    Representation.Coinvariants.mk (ρ.comp N.subtype) (fixedProj ρ hρ hKc hKo w : V) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
  classical
  have hterm : ∀ k ∈ K, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ k w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
    intro k hk
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hfact k hk
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hwNbar z hz,
      mk_apply_of_mem ρ N (Subgroup.mem_inf.1 hx).2, hwM y hy]
  obtain ⟨N', -, -, hN'U, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo
    ((hρ w).mem_nhds (one_mem (stabilizerOf ρ w)))
  have := Fintype.ofFinite (K ⧸ N'.subgroupOf K)
  have hw' : w ∈ fixedVectors ρ N' := fun k hk => hN'U hk
  set c : ℂ := (Fintype.card (K ⧸ N'.subgroupOf K) : ℂ)
  have hc : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hyK : c⁻¹ • cosetSum ρ K N' w ∈ fixedVectors ρ K :=
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hw')
  have hey : fixedProj ρ hρ hKc hKo w = ⟨c⁻¹ • cosetSum ρ K N' w, hyK⟩ := by
    rw [fixedProj_eq_iff]
    have heq : w - c⁻¹ • cosetSum ρ K N' w =
        c⁻¹ • ∑ q : K ⧸ N'.subgroupOf K, (w - ρ ((Quotient.out q : K) : G) w) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← cosetSum_apply, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    show w - c⁻¹ • cosetSum ρ K N' w ∈ coinvariantsKer ρ K
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    rw [← neg_sub]
    exact Submodule.neg_mem _ (sub_mem_coinvariantsKer (Quotient.out q).2 w)
  rw [hey]
  show Representation.Coinvariants.mk (ρ.comp N.subtype) (c⁻¹ • cosetSum ρ K N' w) = _
  rw [map_smul, cosetSum_apply, map_sum,
    Finset.sum_congr rfl fun q _ => hterm _ (Quotient.out q).2, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

end General

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

def IsSupercuspidal (π : Representation ℂ (GL (Fin n) F) V) : Prop :=
  ∀ γ : Fin n → ℕ, (∃ i j, γ i ≠ γ j) → Subsingleton (JacquetModule F n γ π)

def matrixCoeff (π : Representation ℂ (GL (Fin n) F) V) (v : V) (f : Module.Dual ℂ V)
    (g : GL (Fin n) F) : ℂ :=
  f (π g v)

def IsCompactModCenter (φ : GL (Fin n) F → ℂ) : Prop :=
  ∃ C : Set (GL (Fin n) F), IsCompact C ∧
    Function.support φ ⊆ (Subgroup.center (GL (Fin n) F) : Set (GL (Fin n) F)) * C

section Compact

variable {π : Representation ℂ (GL (Fin n) F) V}

theorem exists_finset_of_isSupercuspidal (hsc : IsSupercuspidal π) {S : Finset (Fin n)}
    (hS : ∃ i j, i ∈ S ∧ j ∉ S) (w : V) :
    ∃ U : Finset (GL (Fin n) F), (∀ u ∈ U, u ∈ unipotentRadical F n (splitFun S)) ∧
      w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = π u x - x} := by
  classical
  obtain ⟨i, j, hi, hj⟩ := hS
  have hsub := hsc (splitFun S) ⟨i, j, by simp [splitFun, hi, hj]⟩
  have hw : w ∈ Representation.Coinvariants.ker (π.comp (unipotentRadical F n (splitFun S)).subtype) :=
    (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨T, hT, hwT⟩ := Submodule.mem_span_finite_of_mem_span hw
  have hpre : ∀ y ∈ T, ∃ gv : unipotentRadical F n (splitFun S) × V,
      π (gv.1 : GL (Fin n) F) gv.2 - gv.2 = y := by
    intro y hy
    obtain ⟨gv, h⟩ := hT hy
    exact ⟨gv, h⟩
  choose! pre hpre using hpre
  refine ⟨T.image fun y => ((pre y).1 : GL (Fin n) F), ?_, ?_⟩
  · intro u hu
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hu
    exact (pre y).1.2
  · refine Submodule.span_mono ?_ hwT
    intro y hy
    exact ⟨((pre y).1 : GL (Fin n) F), Finset.mem_image_of_mem _ hy, (pre y).2, (hpre y hy).symm⟩

theorem diagPow_const_mem_center (c : ℤ) :
    Cartan.diagPow F n (fun _ => c) ∈ Subgroup.center (GL (Fin n) F) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
    ⟨(uniformizer F : F) ^ c, by rw [Matrix.scalar_apply, Cartan.coe_diagPow]⟩

theorem isCompactModCenter_matrixCoeff (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (v : V)
    {f : Module.Dual ℂ V} (hf : f ∈ smoothVectors (Representation.dual π)) :
    IsCompactModCenter (matrixCoeff π v f) := by
  classical
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1 ((hπ v).mem_nhds (one_mem _))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hf).mem_nhds (one_mem _))
  set m := max m₁ m₂
  set K := congruenceSubgroup F n m
  have hvK : v ∈ fixedVectors π K := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_left _ _) hk)
  have hfK : ∀ k ∈ K, ∀ x, f (π k x) = f x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)
  set K₀ := integralGL F n
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  let R : Finset (GL (Fin n) F) :=
    Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, π k v = π r v := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq π hvK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ K.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  let V₂ : Finset V := R.image fun r => π r v
  have hU : ∀ S : Finset (Fin n), (∃ i j, i ∈ S ∧ j ∉ S) → ∀ w : V,
      ∃ U : Finset (GL (Fin n) F), (∀ u ∈ U, u ∈ unipotentRadical F n (splitFun S)) ∧
        w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = π u x - x} :=
    fun S hS w => exists_finset_of_isSupercuspidal hsc hS w
  choose! Uf hUf1 hUf2 using hU
  let Uall : Finset (GL (Fin n) F) := Finset.univ.biUnion fun S : Finset (Fin n) => V₂.biUnion (Uf S)
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n
    ((Uall ∪ Uall.image fun u => u⁻¹ : Finset (GL (Fin n) F)) : Set (GL (Fin n) F)).toFinite.isCompact
  have hbu : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * u i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp [hu])
  have hbu' : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * (u⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨u, hu, rfl⟩)
  set C : ℤ := ((t + m : ℕ) : ℤ) + 1 with hCdef
  have hC : ((t + m : ℕ) : ℤ) < C := lt_add_one _
  have hC0 : 0 < C := by positivity
  let Nset : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc 0 (n * C)
  let Cset : Set (GL (Fin n) F) := ⋃ ν ∈ (Nset : Set (Fin n → ℤ)),
    (fun p : GL (Fin n) F × GL (Fin n) F => p.1 * Cartan.diagPow F n ν * p.2) ''
      ((K₀ : Set (GL (Fin n) F)) ×ˢ (K₀ : Set (GL (Fin n) F)))
  have hCset : IsCompact Cset :=
    Nset.finite_toSet.isCompact_biUnion fun ν _ =>
      ((isCompact_integralGL F n).prod (isCompact_integralGL F n)).image (by fun_prop)
  refine ⟨Cset, hCset, fun g hg => ?_⟩
  rw [Function.mem_support] at hg
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  obtain ⟨r₂, hr₂, hr₂v⟩ := hR k₂ hk₂
  have hwV : π r₂ v ∈ V₂ := Finset.mem_image_of_mem _ hr₂
  rcases gap_or_bounded (β := fun _ : Fin n => (0 : ℕ)) μ hC0 with
    ⟨θ, b, ⟨i, hib, hiθ⟩, ⟨j, hjb, hjθ⟩, hgap⟩ | hbd
  · exfalso
    apply hg
    set S : Finset (Fin n) :=
      Finset.univ.filter fun j => (fun _ : Fin n => (0 : ℕ)) j = b ∧ θ ≤ μ j with hSdef
    have hS : ∃ i j, i ∈ S ∧ j ∉ S :=
      ⟨i, j, by simp [S, hib, hiθ], by simp [S, hjb, not_le.2 hjθ]⟩
    have hsp := hUf2 S hS (π r₂ v)
    set a := Cartan.diagPow F n μ
    have hker : Submodule.span ℂ {y | ∃ u ∈ Uf S (π r₂ v), ∃ x, y = π u x - x} ≤
        LinearMap.ker (f ∘ₗ π k₁ ∘ₗ π a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, x, rfl⟩
      have huA : u ∈ Uall := Finset.mem_biUnion.2 ⟨S, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨π r₂ v, hwV, hu⟩⟩
      have huN := hUf1 S hS (π r₂ v) u hu
      have hlev : ∀ w : GL (Fin n) F, w ∈ levi F n (fun _ : Fin n => (0 : ℕ)) :=
        fun w => mem_levi.2 fun i j h => absurd rfl h
      have hconj : a * u * a⁻¹ ∈ K :=
        diagPow_conj_mem_congruenceSubgroup hC (apply_eq_or_gap hgap (hlev u) huN)
          (apply_eq_or_gap hgap (hlev u⁻¹) ((unipotentRadical F n _).inv_mem huN))
          (hbu u huA) (hbu' u huA)
      have hconj' : k₁ * (a * u * a⁻¹) * k₁⁻¹ ∈ K := conj_mem_congruenceSubgroup F n hk₁ hconj
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        map_sub]
      have h1 : π k₁ (π a (π u x)) = π (k₁ * (a * u * a⁻¹) * k₁⁻¹) (π k₁ (π a x)) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        group
      rw [h1, hfK _ hconj', sub_self]
    have := hker hsp
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply] at this
    show f (π (k₁ * a * k₂) v) = 0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr₂v]
    exact this
  ·
    let c₀ : ℤ := if h : ∃ k : Fin n, True then
      (Finset.univ.image μ).min' ⟨_, Finset.mem_image_of_mem μ (Finset.mem_univ h.choose)⟩ else 0
    have hc₀le : ∀ k, c₀ ≤ μ k := by
      intro k
      simp only [c₀, dif_pos (⟨k, trivial⟩ : ∃ k : Fin n, True)]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    have hc₀mem : ∀ j : Fin n, ∃ k, c₀ = μ k := by
      intro j
      simp only [c₀, dif_pos (⟨j, trivial⟩ : ∃ k : Fin n, True)]
      obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (Finset.min'_mem (Finset.univ.image μ) _)
      exact ⟨k, hk.symm⟩
    let ν : Fin n → ℤ := μ - fun _ => c₀
    have hν : ν ∈ Nset := by
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_Icc]
      obtain ⟨k, hk⟩ := hc₀mem j
      have h1 := hc₀le j
      have h2 := hbd j k rfl
      constructor
      · show 0 ≤ μ j - c₀
        linarith
      · show μ j - c₀ ≤ n * C
        linarith
    have hμ : μ = (fun _ => c₀) + ν := by
      funext j
      simp [ν]
    have hz := diagPow_const_mem_center (F := F) (n := n) c₀
    refine Set.mem_mul.2 ⟨Cartan.diagPow F n (fun _ => c₀), hz, k₁ * Cartan.diagPow F n ν * k₂,
      Set.mem_biUnion hν ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩, ?_⟩
    rw [hμ, diagPow_add, ← mul_assoc k₁, Subgroup.mem_center_iff.1 hz k₁]
    group

end Compact

section Converse

variable {π : Representation ℂ (GL (Fin n) F) V}

theorem rankTorus_apply_self {α : Type*} [LinearOrder α] (β : Fin n → α) (e : ℕ) (i : Fin n) :
    (rankTorus F n β e : GL (Fin n) F) i i =
      (uniformizer F : F) ^ (-((e * blockRank β i : ℕ) : ℤ)) := by
  show ((rankTorus F n β e : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = _
  rw [rankTorus, coe_torusPow, diagonal_apply_eq]

theorem rankTorus_inv_apply_self {α : Type*} [LinearOrder α] (β : Fin n → α) (e : ℕ)
    (i : Fin n) :
    ((rankTorus F n β e)⁻¹ : GL (Fin n) F) i i =
      (uniformizer F : F) ^ (((e * blockRank β i : ℕ) : ℤ)) := by
  show (((rankTorus F n β e)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = _
  rw [rankTorus, ← torusPow_neg, coe_torusPow, diagonal_apply_eq, Pi.neg_apply, neg_neg]

theorem nonneg_of_zpow_mem {z : ℤ} (h : (uniformizer F : F) ^ z ∈ 𝒪[F]) : 0 ≤ z := by
  have h1 := (Valuation.mem_integer_iff _ _).1 h
  rw [map_zpow₀] at h1
  exact (zpow_le_one_iff_right_of_lt_one₀
    (zero_lt_iff.2 (valuation_uniformizer_ne_zero F)) (valuation_uniformizer_lt_one F)).1 h1

theorem isSupercuspidal_of_isCompactModCenter (hπ : IsAdmissible π)
    (h : ∀ v : V, ∀ f ∈ smoothVectors (Representation.dual π),
      IsCompactModCenter (matrixCoeff π v f)) :
    IsSupercuspidal π := by
  classical
  intro γ hγ
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : JacquetModule F n γ π)
  obtain ⟨x₀, rfl⟩ := Representation.Coinvariants.mk_surjective _ y₀
  set q := Representation.Coinvariants.mk (π.comp (unipotentRadical F n γ).subtype) with hqdef

  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1 ((hπ.1 x₀).mem_nhds (one_mem _))
  set m := max m₁ 1
  have hm : 1 ≤ m := le_max_right _ _
  set K := congruenceSubgroup F n m
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hx₀K : x₀ ∈ fixedVectors π K := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_left _ _) hk)
  set e := fixedProj π hπ.1 hKc hKo

  set a := rankTorus F n γ 1 with hadef
  have hapow : ∀ j : ℕ, a ^ j = rankTorus F n γ j := fun j => by
    rw [hadef, rankTorus_pow, one_mul]
  have haN : ∀ u ∈ unipotentRadical F n γ, a * u * a⁻¹ ∈ unipotentRadical F n γ :=
    fun u hu => conj_mem_unipotentRadical (rankTorus_mem_blockUpper 1) hu
  have haN' : ∀ u ∈ unipotentRadical F n γ, a⁻¹ * u * a ∈ unipotentRadical F n γ := fun u hu => by
    simpa using conj_mem_unipotentRadical ((blockUpper F n γ).inv_mem (rankTorus_mem_blockUpper 1)) hu
  set A := coinvariantsTranslate π (unipotentRadical F n γ) a haN
  have hAinj : Function.Injective A := coinvariantsTranslate_injective haN haN'
  have hAiter : ∀ (j : ℕ) (x : V), A^[j] (q x) = q (π (a ^ j) x) := fun j x =>
    iterate_coinvariantsTranslate_mk haN j x

  have hkey : ∀ (j : ℕ), ∀ x ∈ fixedVectors π K,
      q (e (π (a ^ j) x) : V) = q (π (a ^ j) x) := by
    intro j x hx
    refine mk_fixedProj_eq hπ.1 hKc hKo (congruenceSubgroup_iwahoriFactorization' γ hm)
      (fun z hz => ?_) (fun y hy => ?_)
    · have hz' := (Subgroup.mem_inf.1
        (rankTorus_inv_conj_mem_congruenceSubgroup (e := j) hz)).1
      have hz'' : (a ^ j)⁻¹ * z * a ^ j ∈ K := by
        rw [hapow]
        exact congruenceSubgroup_antitone F n (by omega) hz'
      have hzeq : z = a ^ j * ((a ^ j)⁻¹ * z * a ^ j) * (a ^ j)⁻¹ := by group
      rw [hzeq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (π (a ^ j)⁻¹), ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, hx _ hz'']
    · have hc : y * a ^ j = a ^ j * y := by
        rw [hapow]
        exact (rankTorus_commute j (Subgroup.mem_inf.1 hy).2).symm
      rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply,
        hx y (Subgroup.mem_inf.1 hy).1]

  set I : Submodule ℂ (JacquetModule F n γ π) := Submodule.map q (fixedVectors π K)
  have : FiniteDimensional ℂ (fixedVectors π K) := hπ.2 K hKc hKo
  have hIfin : FiniteDimensional ℂ I := inferInstance
  have hAI : ∀ j : ℕ, A^[j] (q x₀) ∈ I := fun j =>
    ⟨(e (π (a ^ j) x₀) : V), (e _).2, by rw [hkey j x₀ hx₀K, hAiter]⟩
  have hne : ∀ j : ℕ, A^[j] (q x₀) ≠ 0 := by
    intro j hj
    apply hy₀
    have h0 : A^[j] (0 : JacquetModule F n γ π) = 0 := Function.iterate_fixed (map_zero A) j
    exact (hAinj.iterate j) (hj.trans h0.symm)

  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ I, ∀ J : ℕ, ∃ j ≥ J,
      lam ⟨A^[j] (q x₀), hAI j⟩ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    let b := Module.finBasis ℂ I
    choose J hJ using fun i => hcon (b.coord i)
    set J₀ := Finset.univ.sup J
    have h0 : (⟨A^[J₀] (q x₀), hAI J₀⟩ : I) = 0 := by
      refine b.ext_elem fun i => ?_
      rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply]
      exact hJ i J₀ (Finset.le_sup (Finset.mem_univ i))
    exact hne J₀ (congrArg Subtype.val h0)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend lam

  set f : Module.Dual ℂ V := Λ ∘ₗ q ∘ₗ (fixedVectors π K).subtype ∘ₗ e with hfdef
  have hf : f ∈ smoothVectors (Representation.dual π) := by
    refine mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 fun k hk y => ?_)
    simp only [hfdef, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [fixedProj_apply_act hπ.1 hKc hKo hk]
  have hcoef : ∀ j : ℕ, matrixCoeff π x₀ f (a ^ j) = lam ⟨A^[j] (q x₀), hAI j⟩ := by
    intro j
    simp only [matrixCoeff, hfdef, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hkey j x₀ hx₀K, ← hAiter]
    exact LinearMap.congr_fun hΛ ⟨A^[j] (q x₀), hAI j⟩

  obtain ⟨C, hC, hsupp⟩ := h x₀ f hf
  obtain ⟨eb, heb⟩ := exists_pow_mul_mem_of_isCompact F n (hC.union hC.inv)
  obtain ⟨i, i', hlt⟩ : ∃ i i', γ i' < γ i := by
    obtain ⟨i, i', hii'⟩ := hγ
    rcases lt_or_gt_of_ne hii' with h' | h'
    · exact ⟨i', i, h'⟩
    · exact ⟨i, i', h'⟩
  have hr := blockRank_lt hlt
  obtain ⟨j, hj, hjne⟩ := hlam (2 * eb + 1)
  have hmem : a ^ j ∈ (Subgroup.center (GL (Fin n) F) : Set (GL (Fin n) F)) * C :=
    hsupp (by rw [Function.mem_support, hcoef]; exact hjne)
  obtain ⟨z, hz, g, hg, hzg⟩ := Set.mem_mul.1 hmem
  obtain ⟨s, hs⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have h1 : s * g i i = (a ^ j) i i := by
    rw [← hzg]
    show s * g i i = ((z : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F)) i i
    rw [← hs, Matrix.scalar_apply, diagonal_mul]
  have hginv : g⁻¹ = (a ^ j)⁻¹ * z := by
    rw [← hzg]
    group
  have h2 : (g⁻¹ : GL (Fin n) F) i' i' = ((a ^ j)⁻¹ : GL (Fin n) F) i' i' * s := by
    rw [hginv]
    show ((((a ^ j)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (z : Matrix (Fin n) (Fin n) F)) i' i' = _
    rw [← hs, Matrix.scalar_apply, mul_diagonal]
  have hb1 := heb g (Or.inl hg) i i
  have hb2 := heb g⁻¹ (Or.inr (by simpa using hg)) i' i'
  have hprod : ((uniformizer F : F) ^ eb * g i i) * ((uniformizer F : F) ^ eb * (g⁻¹ : GL (Fin n) F) i' i') =
      (uniformizer F : F) ^ ((2 * eb : ℕ) + (((j * blockRank γ i' : ℕ) : ℤ) -
        ((j * blockRank γ i : ℕ) : ℤ))) := by
    rw [h2]
    have h3 : ((uniformizer F : F) ^ eb * g i i) * ((uniformizer F : F) ^ eb *
        (((a ^ j)⁻¹ : GL (Fin n) F) i' i' * s)) =
        (uniformizer F : F) ^ eb * (uniformizer F : F) ^ eb * ((s * g i i) *
          ((a ^ j)⁻¹ : GL (Fin n) F) i' i') := by ring
    rw [h3, h1, hapow, rankTorus_apply_self, rankTorus_inv_apply_self, ← pow_add,
      ← zpow_natCast, ← zpow_add₀ (Cartan.uniformizer_ne_zero F),
      ← zpow_add₀ (Cartan.uniformizer_ne_zero F)]
    congr 1
    push_cast
    ring
  have hnn := nonneg_of_zpow_mem (hprod ▸ mul_mem hb1 hb2)
  have hj' : (j : ℤ) * ((blockRank γ i' : ℤ) + 1) ≤ (j : ℤ) * blockRank γ i :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (by positivity)
  push_cast at hnn
  nlinarith

theorem isSupercuspidal_iff_isCompactModCenter [π.IsIrreducible] (hπ : IsSmooth π) :
    IsSupercuspidal π ↔ ∀ v : V, ∀ f ∈ smoothVectors (Representation.dual π),
      IsCompactModCenter (matrixCoeff π v f) :=
  ⟨fun hsc v _ hf => isCompactModCenter_matrixCoeff hπ hsc v hf,
    isSupercuspidal_of_isCompactModCenter (isAdmissible_of_isIrreducible hπ)⟩

end Converse

end Parabolic

end GroundTheory.Automorphic
