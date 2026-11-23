import Formalism.FormalGroupWitt.SubstInjectiveV
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

universe u v w

namespace Formalism.FG.InvIntVAux

open Formalism.G Formalism.G.LogCR

variable {K : Type u} [NormedField K]

def Low {σ : Type*} (m : ℕ) (x : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0

section Basic

variable {σ : Type*}

theorem Low.mono {m k : ℕ} {x : MvPowerSeries σ K} (h : Low m x) (hk : k ≤ m) : Low k x := by
  intro d hd
  exact h d (lt_of_lt_of_le hd hk)

theorem Low.mul {m k : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = d := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | exact (_root_.Finset.mem_antidiagonal).mp hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by
    rw [← hp']
    first
      | exact (Finsupp.degree_add p.1 p.2).symm
      | exact (map_add Finsupp.degree p.1 p.2).symm
      | simp
  by_cases h1 : p.1.degree < m
  · rw [hx _ h1, zero_mul]
  · rw [hy _ (by omega), mul_zero]

theorem Low.add {m : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low m y) :
    Low m (x + y) := by
  intro d hd
  rw [map_add, hx d hd, hy d hd, add_zero]

theorem Low.sum {α : Type*} {m : ℕ} (s : Finset α) (x : α → MvPowerSeries σ K)
    (h : ∀ a ∈ s, Low m (x a)) : Low m (∑ a ∈ s, x a) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha d hd

theorem low_one {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by
  intro d hd
  have h0 : d = 0 := by
    first
      | exact (Finsupp.degree_eq_zero_iff d).1 (by omega)
      | exact Finsupp.degree_eq_zero_iff.1 (by omega)
      | simpa using (show d.degree = 0 by omega)
  subst h0
  first
    | exact hx
    | simpa using hx

theorem low_of_agree {N : ℕ} {a b : MvPowerSeries σ K} (hab : Agree N a b) : Low N (a - b) := by
  intro d hd
  rw [map_sub, hab d hd, sub_self]

end Basic

theorem eq_single_of_degree_eq_one {ι : Type*} [Fintype ι] (e : ι →₀ ℕ)
    (he : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  have hd : e.degree = ∑ j ∈ e.support, e j := by
    first
      | rfl
      | simp [Finsupp.degree]
  rw [hd] at he
  have hcard : e.support.card ≤ 1 := by
    have h1 : ∑ j ∈ e.support, (1 : ℕ) ≤ ∑ j ∈ e.support, e j :=
      Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    rw [he, Finset.sum_const, smul_eq_mul, mul_one] at h1
    exact h1
  have hpos : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.sum_empty] at he
    omega
  have hc1 : e.support.card = 1 := by
    have := Finset.card_pos.mpr hpos
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc1
  refine ⟨i, ?_⟩
  rw [hi, Finset.sum_singleton] at he
  ext j
  by_cases hj : j = i
  · rw [hj, he, Finsupp.single_eq_same]
  · have hz : e j = 0 := by
      by_contra hne
      have hmem : j ∈ e.support := Finsupp.mem_support_iff.mpr hne
      rw [hi, Finset.mem_singleton] at hmem
      exact hj hmem
    rw [hz]
    simp [Finsupp.single_apply, Ne.symm hj]

theorem decomp {σ : Type*} [Fintype σ] [LinearOrder σ] (m : ℕ) (x : MvPowerSeries σ K)
    (hx : Low (m + 1) x) :
    ∃ y : σ → MvPowerSeries σ K, (∀ i, Low m (y i)) ∧ x = ∑ i, MvPowerSeries.X i * y i := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : σ → MvPowerSeries σ K, ∀ i e, MvPowerSeries.coeff e (y i) =
      if (e + Finsupp.single i 1).support.min = (i : WithTop σ) then
        MvPowerSeries.coeff (e + Finsupp.single i 1) x else 0 :=
    ⟨fun i e => if (e + Finsupp.single i 1).support.min = (i : WithTop σ) then
        MvPowerSeries.coeff (e + Finsupp.single i 1) x else 0, fun i e => rfl⟩
  have hd0 : (0 : σ →₀ ℕ).degree = 0 := by
    first | rfl | simp
  refine ⟨y, fun i e he => ?_, ?_⟩
  · rw [hy]
    split_ifs with hmin
    · have hdeg : (e + Finsupp.single i 1).degree = e.degree + 1 := by
        first
          | rw [Finsupp.degree_add, Finsupp.degree_single]
          | simp
      exact hx _ (by omega)
    · rfl
  · ext d
    rw [map_sum]
    have hXm : ∀ i (φ : MvPowerSeries σ K), MvPowerSeries.coeff d (MvPowerSeries.X i * φ) =
        if Finsupp.single i 1 ≤ d then MvPowerSeries.coeff (d - Finsupp.single i 1) φ else 0 := by
      intro i φ
      first
        | rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, one_mul]
        | rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
        | simp [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
    simp only [hXm]
    by_cases hdz : d = 0
    · subst hdz
      have h0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) x = 0 := hx 0 (by rw [hd0]; omega)
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      have hnle : ¬ Finsupp.single i 1 ≤ (0 : σ →₀ ℕ) := by
        intro hle
        have := hle i
        simp at this
      rw [if_neg hnle]
    · have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hdz
      obtain ⟨i0, hmin⟩ := Finset.min_of_nonempty hne
      have hi0m : i0 ∈ d.support := Finset.mem_of_min hmin
      have hd1 : 1 ≤ d i0 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0m)
      have hle : Finsupp.single i0 1 ≤ d := by
        first
          | exact Finsupp.single_le_iff.mpr hd1
          | (intro j; by_cases hj : i0 = j; (subst hj; simpa using hd1); simp [Finsupp.single_apply, hj])
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hle, hy, tsub_add_cancel_of_le hle, if_pos hmin]
      · intro i _ hi
        split_ifs with hle'
        · have hc : ¬ d.support.min = (i : WithTop σ) := by
            rw [hmin]
            intro h
            exact hi (WithTop.coe_injective h).symm
          rw [hy, tsub_add_cancel_of_le hle', if_neg hc]
        · rfl
      · intro h
        exact absurd (Finset.mem_univ i0) h

private theorem subst_diff_lemma {σ τ : Type*} [Fintype σ] [Finite τ] (N : ℕ) :
    ∀ (z : MvPowerSeries σ K) (a b : σ → MvPowerSeries τ K),
      (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
      (∀ i, MvPowerSeries.constantCoeff (b i) = 0) → (∀ i, Agree N (a i) (b i)) →
      Low N (MvPowerSeries.subst a z - MvPowerSeries.subst b z) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  induction N with
  | zero => intro z a b _ _ _ d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ N ih =>
    intro z a b ha hb hab
    have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
    have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
    have hφb : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst b w = MvPowerSeries.substAlgHom (R := K) hsb w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsb) w).symm
        | rfl
    obtain ⟨c, hc⟩ : ∃ c, c = MvPowerSeries.constantCoeff z := ⟨_, rfl⟩
    have hcz : MvPowerSeries.constantCoeff (algebraMap K (MvPowerSeries σ K) c) = c := by
      first
        | (simp; done)
        | (simp [MvPowerSeries.algebraMap_apply]; done)
        | (simp [← MvPowerSeries.c_eq_algebraMap]; done)
        | (rw [Algebra.algebraMap_eq_smul_one]; simp; done)
        | (rw [Algebra.algebraMap_eq_smul_one, MvPowerSeries.constantCoeff_smul]; simp; done)
        | rfl
    have hw : Low 1 (z - algebraMap K (MvPowerSeries σ K) c) := by
      apply low_one
      rw [map_sub, hcz, hc, sub_self]
    obtain ⟨y, -, hy⟩ := decomp 0 (z - algebraMap K (MvPowerSeries σ K) c) hw
    have hz : z = algebraMap K (MvPowerSeries σ K) c + ∑ i, MvPowerSeries.X i * y i := by
      rw [← hy]
      abel
    have hab' : ∀ i, Agree N (a i) (b i) := fun i e he => hab i e (by omega)
    rw [hz, hφa, hφb, map_add, map_add, AlgHom.commutes, AlgHom.commutes, map_sum, map_sum,
      add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Low.sum
    intro i _
    beta_reduce
    rw [map_mul, map_mul, ← hφa, ← hφa, ← hφb, ← hφb, MvPowerSeries.subst_X hsa,
      MvPowerSeries.subst_X hsb]
    have hsplit : a i * MvPowerSeries.subst a (y i) - b i * MvPowerSeries.subst b (y i) =
        (a i - b i) * MvPowerSeries.subst a (y i) +
          b i * (MvPowerSeries.subst a (y i) - MvPowerSeries.subst b (y i)) := by ring
    rw [hsplit]
    apply Low.add
    · have h1 := Low.mul (low_of_agree (hab i))
        (show Low 0 (MvPowerSeries.subst a (y i)) from fun e he => absurd he (Nat.not_lt_zero _))
      rwa [add_zero] at h1
    · have h2 := Low.mul (low_one (hb i)) (ih (y i) a b ha hb hab')
      rwa [add_comm] at h2

private theorem low_one_subst_lemma_2 {σ τ : Type*} [Fintype σ] [Finite τ] (w : MvPowerSeries σ K)
    (hw : Low 1 w) (a : σ → MvPowerSeries τ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    Low 1 (MvPowerSeries.subst a w) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
  obtain ⟨y, -, hy⟩ := decomp 0 w hw
  rw [hy, hφa, map_sum]
  apply Low.sum
  intro i _
  beta_reduce
  rw [map_mul, ← hφa, ← hφa, MvPowerSeries.subst_X hsa]
  have h1 := Low.mul (low_one (ha i))
    (show Low 0 (MvPowerSeries.subst a (y i)) from fun e he => absurd he (Nat.not_lt_zero _))
  rwa [add_zero] at h1

theorem low_subst_diff {σ τ : Type*} [Fintype σ] [Finite τ] (g : MvPowerSeries σ K)
    (hg : Low 2 g) {N : ℕ} {a b : σ → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hab : ∀ i, Agree N (a i) (b i)) :
    Low (N + 1) (MvPowerSeries.subst a g - MvPowerSeries.subst b g) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
  have hφb : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst b w = MvPowerSeries.substAlgHom (R := K) hsb w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsb) w).symm
        | rfl
  obtain ⟨y, hy1, hy⟩ := decomp 1 g hg
  rw [hy, hφa, hφb, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Low.sum
  intro i _
  beta_reduce
  rw [map_mul, map_mul, ← hφa, ← hφa, ← hφb, ← hφb, MvPowerSeries.subst_X hsa,
    MvPowerSeries.subst_X hsb]
  have hsplit : a i * MvPowerSeries.subst a (y i) - b i * MvPowerSeries.subst b (y i) =
      (a i - b i) * MvPowerSeries.subst a (y i) +
        b i * (MvPowerSeries.subst a (y i) - MvPowerSeries.subst b (y i)) := by ring
  rw [hsplit]
  apply Low.add
  · exact Low.mul (low_of_agree (hab i)) (low_one_subst_lemma_2 (y i) (hy1 i) a ha)
  · have h2 := Low.mul (low_one (hb i)) (subst_diff_lemma N (y i) a b ha hb hab)
    rwa [add_comm] at h2

theorem tail_low {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f) (j : ι) : Low 2 (f j - MvPowerSeries.X j) := by
  intro d hd
  obtain h0 | h1 : d.degree = 0 ∨ d.degree = 1 := by omega
  · have hL : Low 1 (f j - MvPowerSeries.X j) := low_one (by simp [hf.1 j])
    exact hL d (by omega)
  · obtain ⟨i, rfl⟩ := eq_single_of_degree_eq_one d h1
    rw [map_sub, hf.2 j i, MvPowerSeries.coeff_X]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : Finsupp.single i 1 ≠ Finsupp.single j 1 := by
        intro heq
        exact hij (Finsupp.single_left_injective one_ne_zero heq)
      rw [if_neg hij, if_neg hne, sub_zero]

theorem main (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (P i) = 0) →
      (∀ i, IntegralMv (P i)) → C (fun j => MvPowerSeries.subst P (f j)))
    (hlowC : ∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1)
    (h : ι → MvPowerSeries τ K) (hh0 : ∀ i, MvPowerSeries.constantCoeff (h i) = 0)
    (hCh : C (fun j => MvPowerSeries.subst h (f j))) : ∀ i, IntegralMv (h i) := by
  classical
  have hcc : ∀ x : MvPowerSeries τ K, MvPowerSeries.constantCoeff x = MvPowerSeries.coeff 0 x :=
    fun x => by first | rfl | simp
  have hdz : ∀ e : τ →₀ ℕ, e.degree = 0 → e = 0 := fun e he => by
    first
      | exact (Finsupp.degree_eq_zero_iff e).1 he
      | exact Finsupp.degree_eq_zero_iff.1 he
      | simpa using he
  have hd0 : (0 : τ →₀ ℕ).degree = 0 := by
    first | rfl | simp
  have hsubX : ∀ (a : ι → MvPowerSeries τ K), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) →
      ∀ j, MvPowerSeries.subst a (f j) =
        a j + MvPowerSeries.subst a (f j - MvPowerSeries.X j) := by
    intro a ha j
    have hs : MvPowerSeries.HasSubst a := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
            (fun s => by rw [ha s]; exact IsNilpotent.zero)
        | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩
    have hsub' : MvPowerSeries.subst a (f j - MvPowerSeries.X j) =
        MvPowerSeries.subst a (f j) -
          MvPowerSeries.subst a (MvPowerSeries.X j : MvPowerSeries ι K) := by
      first
        | exact MvPowerSeries.subst_sub hs _ _
        | rw [eq_sub_iff_add_eq, ← MvPowerSeries.subst_add hs, sub_add_cancel]
        | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_sub _ _ _)
    rw [hsub', MvPowerSeries.subst_X hs]
    abel
  have key : ∀ N : ℕ, ∀ i (d : τ →₀ ℕ), d.degree < N →
      ‖MvPowerSeries.coeff d (h i)‖ ≤ 1 := by
    intro N
    induction N with
    | zero => intro i d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ N ih =>
      intro i d hd
      rcases Nat.lt_or_ge d.degree N with hlt | hge
      · exact ih i d hlt
      have hdN : d.degree = N := by omega
      rcases Nat.eq_zero_or_pos N with hN | hN
      · have hd00 : d = 0 := hdz d (by omega)
        subst hd00
        rw [← hcc, hh0 i, norm_zero]
        exact zero_le_one
      obtain ⟨P, hPc⟩ : ∃ P : ι → MvPowerSeries τ K, ∀ j e,
          MvPowerSeries.coeff e (P j) =
            if e.degree < N then MvPowerSeries.coeff e (h j) else 0 :=
        ⟨fun j e => if e.degree < N then MvPowerSeries.coeff e (h j) else 0, fun j e => rfl⟩
      have h0N : (0 : τ →₀ ℕ).degree < N := by rw [hd0]; exact hN
      have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := by
        intro j
        rw [hcc, hPc, if_pos h0N, ← hcc, hh0 j]
      have hPint : ∀ j, IntegralMv (P j) := by
        intro j e
        rw [hPc]
        split_ifs with he
        · exact ih j e he
        · rw [norm_zero]
          exact zero_le_one
      have hagree : ∀ j, Agree N (h j) (P j) := by
        intro j e he
        rw [hPc, if_pos he]
      have hCP := hP P hP0 hPint
      have hCD := hsub _ _ hCh hCP
      have hDc : ∀ j (e : τ →₀ ℕ), e.degree ≤ N →
          MvPowerSeries.coeff e (((fun j : ι => MvPowerSeries.subst h (f j)) -
            (fun j : ι => MvPowerSeries.subst P (f j))) j) =
          if e.degree < N then 0 else MvPowerSeries.coeff e (h j) := by
        intro j e he
        have hL := low_subst_diff (f j - MvPowerSeries.X j) (tail_low f hf j) hh0 hP0 hagree
        simp only [Pi.sub_apply]
        rw [hsubX h hh0 j, hsubX P hP0 j]
        have hrw : h j + MvPowerSeries.subst h (f j - MvPowerSeries.X j) -
            (P j + MvPowerSeries.subst P (f j - MvPowerSeries.X j)) =
            (h j - P j) + (MvPowerSeries.subst h (f j - MvPowerSeries.X j) -
              MvPowerSeries.subst P (f j - MvPowerSeries.X j)) := by abel
        have he1 : e.degree < N + 1 := by omega
        rw [hrw, map_add, hL e he1, add_zero, map_sub, hPc]
        split_ifs with h1
        · exact sub_self _
        · exact sub_zero _
      have hvan : ∀ j (e : τ →₀ ℕ), e.degree < N →
          MvPowerSeries.coeff e (((fun j : ι => MvPowerSeries.subst h (f j)) -
            (fun j : ι => MvPowerSeries.subst P (f j))) j) = 0 := by
        intro j e he
        rw [hDc j e he.le, if_pos he]
      have hN1 : 1 ≤ N := by omega
      have hb := hlowC _ hCD N hN1 hvan i d hdN
      have hnlt : ¬ d.degree < N := by omega
      rw [hDc i d hdN.le, if_neg hnlt] at hb
      exact hb
  intro i d
  exact key (d.degree + 1) i d (Nat.lt_succ_self _)

end Formalism.FG.InvIntVAux

theorem Formalism.FG.inverse_integral_vector : Formalism.FG.InvIntegralV.{u, v, w} := by
  intro K _ _ ι _ _ τ _ C f hf hsub hP hlowC h hh0 hCh
  exact Formalism.FG.InvIntVAux.main ι τ C f hf hsub hP hlowC h hh0 hCh
