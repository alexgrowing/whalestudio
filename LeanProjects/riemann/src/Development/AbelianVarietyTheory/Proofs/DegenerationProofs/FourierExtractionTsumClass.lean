import Mathlib

open Module

namespace GlobalTheory

namespace TorsionFourier

section Algebra

variable {K X : Type} [Field K] [AddCommGroup X]

def torsionChars (K X : Type) [Field K] [AddCommGroup X] (N : ℕ) :
    Subgroup (Multiplicative X →* Kˣ) where
  carrier := {t | t ^ N = 1}
  one_mem' := one_pow N
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow, ha, inv_one]

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in

theorem _root_.GlobalTheory.TorsionFourier.char_apply_eq_prod {ι : Type} [Fintype ι] (b : Basis ι ℤ X)
    (t : Multiplicative X →* Kˣ) (x : X) :
    t (Multiplicative.ofAdd x) = ∏ i, t (Multiplicative.ofAdd (b i)) ^ (b.repr x i) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]

noncomputable def charOfValues {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (u : ι → Kˣ) :
    Multiplicative X →* Kˣ where
  toFun x := ∏ i, u i ^ (b.repr x.toAdd i)
  map_one' := by simp
  map_mul' x y := by simp [zpow_add, Finset.prod_mul_distrib]

theorem charOfValues_apply {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (u : ι → Kˣ) (x : X) :
    charOfValues b u (Multiplicative.ofAdd x) = ∏ i, u i ^ (b.repr x i) := rfl

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
theorem _root_.GlobalTheory.TorsionFourier.charOfValues_basis {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (u : ι → Kˣ)
    (j : ι) : _root_.GlobalTheory.TorsionFourier.charOfValues b u (Multiplicative.ofAdd (b j)) = u j := by
  simp only [_root_.GlobalTheory.TorsionFourier.charOfValues, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    Basis.repr_self]
  rw [Finset.prod_eq_single j
    (fun i _ hi => by simp [Finsupp.single_apply, Ne.symm hi]) (by simp)]
  simp

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
theorem _root_.GlobalTheory.TorsionFourier.charOfValues_pow {ι : Type} [Fintype ι] (b : Basis ι ℤ X)
    (u : ι → Kˣ) (N : ℕ) (hu : ∀ i, u i ^ N = 1) : _root_.GlobalTheory.TorsionFourier.charOfValues b u ^ N = 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  simp only [_root_.GlobalTheory.TorsionFourier.charOfValues, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
theorem _root_.GlobalTheory.TorsionFourier.apply_pow_eq_one {N : ℕ} {t : Multiplicative X →* Kˣ}
    (ht : t ^ N = 1) (x : Multiplicative X) : t x ^ N = 1 := by
  rw [← MonoidHom.pow_apply, ht, MonoidHom.one_apply]

noncomputable def torsionCharsEquiv {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (N : ℕ) :
    torsionChars K X N ≃ (ι → rootsOfUnity N K) where
  toFun t i := ⟨t.1 (Multiplicative.ofAdd (b i)),
    (mem_rootsOfUnity _ _).2 (apply_pow_eq_one t.2 _)⟩
  invFun u := ⟨charOfValues b fun i => (u i).1,
    charOfValues_pow b _ N fun i => (mem_rootsOfUnity _ _).1 (u i).2⟩
  left_inv t := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    exact (char_apply_eq_prod b t.1 x.toAdd).symm
  right_inv u := by
    funext i
    exact Subtype.ext (charOfValues_basis b _ i)

variable [Module.Free ℤ X] [Module.Finite ℤ X]

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
variable [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem _root_.GlobalTheory.TorsionFourier.natCard_torsionChars {N : ℕ} {ζ : K} (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) :
    Nat.card (_root_.GlobalTheory.TorsionFourier.torsionChars K X N) = N ^ finrank ℤ X := by
  haveI : NeZero N := ⟨hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ X
  rw [Nat.card_congr (_root_.GlobalTheory.TorsionFourier.torsionCharsEquiv (K := K) (X := X) b N), Nat.card_fun,
    hζ.card_rootsOfUnity, Module.finrank_eq_card_basis b, Nat.card_eq_fintype_card]

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
variable [Module.Free ℤ X] [Module.Finite ℤ X] in
omit [Module.Finite ℤ X] in
theorem _root_.GlobalTheory.TorsionFourier.add_nsmul_injective {N : ℕ} (hN : 0 < N) (α : X) :
    Function.Injective fun μ : X => α + N • μ := by
  intro μ ν h
  have h' : N • μ = N • ν := add_left_cancel h
  have h'' : (N : ℤ) • μ = (N : ℤ) • ν := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h']
  exact smul_right_injective X (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0) h''

end Algebra

end TorsionFourier

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
private theorem sum_torsionCharacters_apply_nsmul_eq_card {N : ℕ}
    [Fintype (_root_.GlobalTheory.TorsionFourier.torsionChars K X N)] (μ : X) :
    ∑ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N, ((t.1 (Multiplicative.ofAdd (N • μ)) : Kˣ) : K) =
      (Nat.card (_root_.GlobalTheory.TorsionFourier.torsionChars K X N) : K) := by
  have hone : ∀ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N,
      ((t.1 (Multiplicative.ofAdd (N • μ)) : Kˣ) : K) = 1 := fun t => by
    rw [ofAdd_nsmul, map_pow, _root_.GlobalTheory.TorsionFourier.apply_pow_eq_one t.2, Units.val_one]
  rw [Finset.sum_congr rfl fun t _ => hone t]
  simp [Nat.card_eq_fintype_card]

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
private theorem exists_torsionCharacter_apply_ne_one {ι : Type} [Fintype ι] (b : Basis ι ℤ X)
    {N : ℕ} [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N) {x : X}
    (hx : ¬ ∃ μ : X, N • μ = x) :
    ∃ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N, t.1 (Multiplicative.ofAdd x) ≠ 1 := by
  classical
  have hcoord : ∃ i, ¬ (N : ℤ) ∣ b.repr x i := by
    by_contra! hall
    apply hx
    refine ⟨∑ i, (b.repr x i / N) • b i, ?_⟩
    conv_rhs => rw [← b.sum_repr x]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, Int.mul_ediv_cancel' (hall i)]
  obtain ⟨i, hi⟩ := hcoord
  let u : ι → rootsOfUnity N K := Pi.mulSingle i hζ.toRootsOfUnity
  refine ⟨(_root_.GlobalTheory.TorsionFourier.torsionCharsEquiv b N).symm u, ?_⟩
  change _root_.GlobalTheory.TorsionFourier.charOfValues b (fun j => (u j).1) (Multiplicative.ofAdd x) ≠ 1
  simp only [_root_.GlobalTheory.TorsionFourier.charOfValues, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [Finset.prod_eq_single i
    (fun j _ hj => by simp [u, Pi.mulSingle_eq_of_ne hj]) (by simp)]
  intro h
  apply hi
  have hval := congrArg Units.val h
  simp only [u, Pi.mulSingle_eq_same, Units.val_zpow_eq_zpow_val,
    IsPrimitiveRoot.val_toRootsOfUnity_coe, Units.val_one] at hval
  exact (hζ.zpow_eq_one_iff_dvd _).1 hval

open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
private theorem sum_torsionCharacters_apply_eq_zero {ι : Type} [Fintype ι] (b : Basis ι ℤ X)
    {N : ℕ} [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    [Fintype (_root_.GlobalTheory.TorsionFourier.torsionChars K X N)] {x : X} (hx : ¬ ∃ μ : X, N • μ = x) :
    ∑ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N, ((t.1 (Multiplicative.ofAdd x) : Kˣ) : K) = 0 := by
  obtain ⟨t₀, ht₀⟩ := exists_torsionCharacter_apply_ne_one b hζ hx
  set S := ∑ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N, ((t.1 (Multiplicative.ofAdd x) : Kˣ) : K)
  have hS : ((t₀.1 (Multiplicative.ofAdd x) : Kˣ) : K) * S = S := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft t₀) _ _ (fun t => by
      simp [Subgroup.coe_mul, MonoidHom.mul_apply, Units.val_mul])
  have hne : ((t₀.1 (Multiplicative.ofAdd x) : Kˣ) : K) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => ht₀ (Units.ext h)
  have hzero : (((t₀.1 (Multiplicative.ofAdd x) : Kˣ) : K) - 1) * S = 0 := by
    rw [sub_mul, hS, one_mul, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left hne

open Module in

theorem _root_.GlobalTheory.fourier_extraction_tsum_class :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : K), 0 < N → ‖(N : K)‖ = 1 → IsPrimitiveRoot ζ N → ∀ (σ : X → K), Filter.Tendsto σ Filter.cofinite (nhds 0) → ∀ α : X, Finite {t : Multiplicative X →* Kˣ // t ^ N = 1} ∧ (∑ᶠ t : {t : Multiplicative X →* Kˣ // t ^ N = 1}, (((t.1 (Multiplicative.ofAdd α))⁻¹ : Kˣ) : K) * ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K)) = (N : K) ^ finrank ℤ X * ∑' μ, σ (α + N • μ) ∧ ((∀ μ, μ ≠ 0 → ‖σ (α + N • μ)‖ < ‖σ α‖) → ‖∑' μ, σ (α + N • μ)‖ = ‖σ α‖) := by
  intro K X _ _ _ _ _ _ N ζ hN hNK hζ σ hσ α
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ X
  let e : {t : Multiplicative X →* Kˣ // t ^ N = 1} ≃ _root_.GlobalTheory.TorsionFourier.torsionChars K X N :=
    Equiv.subtypeEquivRight fun _ => Iff.rfl
  haveI : Finite (_root_.GlobalTheory.TorsionFourier.torsionChars K X N) :=
    Finite.of_equiv _ (_root_.GlobalTheory.TorsionFourier.torsionCharsEquiv (K := K) b N).symm
  letI : Fintype (_root_.GlobalTheory.TorsionFourier.torsionChars K X N) := Fintype.ofFinite _
  refine ⟨Finite.of_equiv _ e.symm, ?_, ?_⟩
  · rw [← finsum_comp_equiv e.symm, finsum_eq_sum_of_fintype]

    have hnorm : ∀ (t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N) (y : X),
        ‖((t.1 (Multiplicative.ofAdd y) : Kˣ) : K)‖ = 1 := fun t y => by
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 ?_
      rw [← norm_pow, ← Units.val_pow_eq_pow_val,
        _root_.GlobalTheory.TorsionFourier.apply_pow_eq_one t.2, Units.val_one, norm_one]
    have hsum : ∀ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N,
        Summable fun β => σ β * ((t.1 (Multiplicative.ofAdd (β - α)) : Kˣ) : K) := fun t =>
      NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa [norm_mul, hnorm] using hσ.norm)
    have hterm : ∀ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N,
        (((t.1 (Multiplicative.ofAdd α))⁻¹ : Kˣ) : K) *
            ∑' β, σ β * ((t.1 (Multiplicative.ofAdd β) : Kˣ) : K) =
          ∑' β, σ β * ((t.1 (Multiplicative.ofAdd (β - α)) : Kˣ) : K) := fun t => by
      rw [← tsum_mul_left]
      congr 1
      funext β
      rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg, map_mul, map_inv, Units.val_mul]
      ring
    refine (Finset.sum_congr rfl fun t _ => hterm t).trans ?_
    rw [← Summable.tsum_finsetSum fun t _ => hsum t]
    simp_rw [← Finset.mul_sum]
    have hg : Function.Injective fun μ : X => α + N • μ := _root_.GlobalTheory.TorsionFourier.add_nsmul_injective hN α
    have hcard : ((Nat.card (_root_.GlobalTheory.TorsionFourier.torsionChars K X N) : ℕ) : K) =
        (N : K) ^ finrank ℤ X := by
      rw [_root_.GlobalTheory.TorsionFourier.natCard_torsionChars hN hζ]
      push_cast
      rfl
    have key : ∀ β, σ β * ∑ t : _root_.GlobalTheory.TorsionFourier.torsionChars K X N,
        ((t.1 (Multiplicative.ofAdd (β - α)) : Kˣ) : K) =
          (N : K) ^ finrank ℤ X * (Set.range fun μ : X => α + N • μ).indicator σ β := by
      intro β
      by_cases hβ : β ∈ Set.range fun μ : X => α + N • μ
      · obtain ⟨μ, rfl⟩ := hβ
        rw [add_sub_cancel_left, sum_torsionCharacters_apply_nsmul_eq_card, hcard,
          Set.indicator_of_mem (Set.mem_range_self μ)]
        ring
      · rw [sum_torsionCharacters_apply_eq_zero b hζ
          (fun ⟨μ, hμ⟩ => hβ ⟨μ, by simp [hμ]⟩), Set.indicator_of_notMem hβ]
        simp
    simp_rw [key]
    rw [tsum_mul_left, ← hg.tsum_eq Set.support_indicator_subset]
    congr 1
    congr 1
    funext μ
    exact Set.indicator_of_mem (Set.mem_range_self (f := fun μ : X => α + N • μ) μ) σ
  · intro h
    set f : X → K := fun μ => σ (α + N • μ) with hf_def
    have hf : Filter.Tendsto f Filter.cofinite (nhds 0) :=
      hσ.comp (_root_.GlobalTheory.TorsionFourier.add_nsmul_injective hN α).tendsto_cofinite
    have hfs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf
    have hf0 : f 0 = σ α := by simp [f]
    rw [hfs.tsum_eq_add_tsum_ite 0, hf0]
    set g : X → K := fun μ => if μ = 0 then 0 else f μ with hg_def
    rcases (norm_nonneg (σ α)).eq_or_lt with hc | hc
    · have hzero : ∀ μ, g μ = 0 := fun μ => by
        by_cases hμ : μ = 0
        · simp [g, hμ]
        · exact absurd (h μ hμ) (by rw [← hc]; exact not_lt.2 (norm_nonneg _))
      have hg0 : g = 0 := funext hzero
      rw [hg0, show (0 : X → K) = fun _ => 0 from rfl, tsum_zero, add_zero]
    · have hε : ‖σ α‖ / 2 < ‖σ α‖ := half_lt_self hc
      have hS : {μ | ‖σ α‖ / 2 ≤ ‖f μ‖}.Finite := by
        have hev := (tendsto_zero_iff_norm_tendsto_zero.1 hf).eventually
          (gt_mem_nhds (half_pos hc))
        simpa [Filter.eventually_cofinite, not_lt] using hev
      have hC : (insert 0 hS.toFinset).sup' (Finset.insert_nonempty _ _)
          (fun μ => ‖g μ‖) < ‖σ α‖ := by
        rw [Finset.sup'_lt_iff]
        intro μ _
        by_cases hμ : μ = 0
        · simpa [g, hμ] using hc
        · simpa [g, hμ] using h μ hμ
      have hbound : ∀ μ, ‖g μ‖ ≤ max (‖σ α‖ / 2)
          ((insert 0 hS.toFinset).sup' (Finset.insert_nonempty _ _) (fun μ => ‖g μ‖)) := by
        intro μ
        by_cases hμ : μ ∈ hS.toFinset
        · exact le_max_of_le_right
            (Finset.le_sup' (fun μ => ‖g μ‖) (Finset.mem_insert_of_mem hμ))
        · refine le_max_of_le_left ?_
          rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hμ
          by_cases h0 : μ = 0
          · simp [g, h0]
            positivity
          · simpa [g, h0] using hμ.le
      have htail : ‖∑' μ, g μ‖ < ‖σ α‖ :=
        (IsUltrametricDist.norm_tsum_le_of_forall_le hbound).trans_lt (max_lt hε hC)
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm htail.ne', max_eq_left htail.le]

end GlobalTheory
