import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem sub_id_bij_of_contracting {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (I : Ideal A)
    [IsPrecomplete I M] [IsHausdorff I M] (T : M →+ M)
    (hT : ∀ (j : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) → T m ∈ (I ^ (j + 1) • ⊤ : Submodule A M)) :
    (∀ b : M, ∃ m, T m - m = b) ∧ ∀ m : M, T m = m → m = 0 := by
  have hmem0 : ∀ m : M, m ∈ (I ^ 0 • ⊤ : Submodule A M) := by intro m; simp

  have hTpow : ∀ (j k : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) →
      T^[k] m ∈ (I ^ (j + k) • ⊤ : Submodule A M) := by
    intro j k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply', ← add_assoc]
      exact hT _ _ (ih m hm)
  have hhaus : ∀ m : M, (∀ j, m ∈ (I ^ j • ⊤ : Submodule A M)) → m = 0 := fun m hm =>
    IsHausdorff.haus ‹IsHausdorff I M› m fun j => by rw [SModEq.zero]; exact hm j
  have hle : ∀ {j k : ℕ}, j ≤ k → (I ^ k • ⊤ : Submodule A M) ≤ I ^ j • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  refine ⟨fun b => ?_, fun m hm => hhaus m fun j => ?_⟩
  · have hiter : ∀ k, T^[k] b ∈ (I ^ k • ⊤ : Submodule A M) := fun k => by
      simpa using hTpow 0 k b (hmem0 b)

    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) m ≡
          (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) n [SMOD (I ^ m • ⊤ : Submodule A M)] := by
      intro m n hmn
      rw [SModEq.sub_mem]
      have hd : -(∑ k ∈ Finset.range m, T^[k] b) - -(∑ k ∈ Finset.range n, T^[k] b) =
          ∑ k ∈ Finset.Ico m n, T^[k] b := by
        rw [Finset.sum_Ico_eq_sub _ hmn]
        abel
      simp only
      rw [hd]
      exact Submodule.sum_mem _ fun k hk => hle (Finset.mem_Ico.mp hk).1 (hiter k)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsPrecomplete I M› hcauchy
    refine ⟨L, sub_eq_zero.mp (hhaus _ fun j => ?_)⟩
    have h1 : L - -(∑ k ∈ Finset.range j, T^[k] b) ∈ (I ^ j • ⊤ : Submodule A M) := by
      have h := SModEq.sub_mem.mp (hL j)
      rw [← neg_sub]
      exact Submodule.neg_mem _ h
    have htel := Finset.sum_range_sub' (fun k => T^[k] b) j
    rw [Finset.sum_sub_distrib] at htel
    simp only [Function.iterate_zero_apply] at htel
    have hsucc : ∀ k, T (T^[k] b) = T^[k + 1] b := fun k => (Function.iterate_succ_apply' T k b).symm
    have h2 : T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
        -(T^[j] b) := by
      rw [map_neg, map_sum]
      simp only [hsucc]
      have e : -(∑ k ∈ Finset.range j, T^[k + 1] b) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
          ((∑ k ∈ Finset.range j, T^[k] b) - ∑ k ∈ Finset.range j, T^[k + 1] b) - b := by abel
      rw [e, htel]
      abel
    have h3 : T (L - -(∑ k ∈ Finset.range j, T^[k] b)) ∈ (I ^ j • ⊤ : Submodule A M) :=
      hle (Nat.le_succ j) (hT j _ h1)
    have hsplit : T L - L - b = (T (L - -(∑ k ∈ Finset.range j, T^[k] b)) -
        (L - -(∑ k ∈ Finset.range j, T^[k] b))) +
        (T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b) := by
      rw [map_sub]
      abel
    rw [hsplit, h2]
    exact Submodule.add_mem _ (Submodule.sub_mem _ h3 h1) (Submodule.neg_mem _ (hiter j))
  · induction j with
    | zero => exact hmem0 m
    | succ j ih =>
      have h := hT j m ih
      rwa [hm] at h

theorem mem_span_pow_smul_top {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x : A) (j : ℕ) (m : M) :
    m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M) ↔ ∃ y, x ^ j • y = m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

theorem contracting_of_semi {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x c : A) (T : M →+ M)
    (h1 : ∀ m, T (x • m) = (c * x) • T m) (h2 : ∀ m, ∃ y, x • y = T m) (j : ℕ) (m : M)
    (hm : m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M)) :
    T m ∈ (Ideal.span {x} ^ (j + 1) • ⊤ : Submodule A M) := by
  rw [mem_span_pow_smul_top] at hm ⊢
  obtain ⟨y, rfl⟩ := hm
  obtain ⟨z, hz⟩ := h2 y
  have hpow : ∀ (i : ℕ) (m : M), T (x ^ i • m) = (c * x) ^ i • T m := by
    intro i
    induction i with
    | zero => intro m; simp
    | succ i ih => intro m; rw [pow_succ, mul_smul, ih, h1, smul_smul, ← pow_succ]
  refine ⟨c ^ j • z, ?_⟩
  rw [hpow, ← hz, smul_smul, smul_smul]
  congr 1
  ring

theorem one_sub_frob_bij : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (P : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (P i)) → (∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ sh 1 (P i)) → (∀ b : ZMod n → V, (∀ i, b i ∈ P i) → ∃ m : ZMod n → V, (∀ i, m i ∈ P i) ∧ ∀ i, D.φ i (m (i - 1)) - m i = b i) ∧ ∀ m : ZMod n → V, (∀ i, m i ∈ P i) → (∀ i, D.φ i (m (i - 1)) = m i) → m = 0 := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D P hP hφ

  have hcoe : ∀ (a : k⟦X⟧) (y : V), a • y = ((a : k⟦X⟧) : k⸨X⸩) • y := by
    intro a y
    rw [← algebraMap_smul k⸨X⸩ a y]
    rfl
  have hφP : ∀ i, ∀ x ∈ P (i - 1), ∃ y ∈ P i, (PowerSeries.X : k⟦X⟧) • y = D.φ i x := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := mem_sh_iff_exists.mp (hφ i x hx)
    exact ⟨y, hy, by rw [hcoe, ← vv_eq_coe_X, ← hyx, zpow_one]⟩
  have hφmem : ∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ P i := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := hφP i x hx
    rw [← hyx]
    exact (P i).smul_mem _ hy

  let T : ((i : ZMod n) → P i) →+ ((i : ZMod n) → P i) :=
    { toFun := fun m i => ⟨D.φ i (m (i - 1)), hφmem i _ (m (i - 1)).2⟩
      map_zero' := by
        funext i
        apply Subtype.ext
        simp
      map_add' := by
        intro a b
        funext i
        apply Subtype.ext
        simp [map_add] }
  have : ∀ i, Module.Finite k⟦X⟧ (P i) := fun i => Module.Finite.iff_fg.mpr (hP i).1
  have hXtop : Ideal.span {(PowerSeries.X : k⟦X⟧)} ≠ ⊤ := by
    intro h
    have h1 := (Ideal.span_singleton_eq_top.mp h).map (PowerSeries.constantCoeff (R := k))
    simp at h1
  have : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    IsHausdorff.of_isLocalRing _ _ hXtop
  have : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _

  obtain ⟨u, hu⟩ := R.φ_v
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have h1 : ∀ m : ((i : ZMod n) → P i), T ((PowerSeries.X : k⟦X⟧) • m) =
      (((u : k⟦X⟧) * PowerSeries.X ^ (l - 1)) * PowerSeries.X) • T m := by
    intro m
    funext i
    apply Subtype.ext
    simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, Submodule.coe_smul]
    rw [hcoe, hcoe, ← vv_eq_coe_X, D.φ_semi, hu, PowerSeries.coe_mul, PowerSeries.coe_mul,
      PowerSeries.coe_pow, ← vv_eq_coe_X, mul_assoc, pow_sub_one_mul hl]
  have h2 : ∀ m : ((i : ZMod n) → P i), ∃ y : ((i : ZMod n) → P i),
      (PowerSeries.X : k⟦X⟧) • y = T m := by
    intro m
    choose y hy hyx using fun i => hφP i _ (m (i - 1)).2
    exact ⟨fun i => ⟨y i, hy i⟩, funext fun i => Subtype.ext (hyx i)⟩
  obtain ⟨hsurj, hinj⟩ := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T
    (fun j m hm => contracting_of_semi _ _ T h1 h2 j m hm)
  refine ⟨fun b hb => ?_, fun m hm hfix => ?_⟩
  · obtain ⟨m, hm⟩ := hsurj (fun i => ⟨b i, hb i⟩)
    refine ⟨fun i => (m i : V), fun i => (m i).2, fun i => ?_⟩
    have h := congrArg (fun z => ((z i : P i) : V)) hm
    simpa [T] using h
  · have h := hinj (fun i => ⟨m i, hm i⟩) (funext fun i => Subtype.ext (hfix i))
    funext i
    have hi := congrArg (fun z => ((z i : P i) : V)) h
    simpa using hi

end GlobalTheory.PhiGam
