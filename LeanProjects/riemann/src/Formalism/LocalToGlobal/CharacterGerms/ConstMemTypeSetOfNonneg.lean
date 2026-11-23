import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section TyS

variable {l : ℕ} (hl : 2 ≤ l)

include hl

theorem coeff_tyS_pow (a : ℕ → C) (s : ℕ) : PowerSeries.coeff (l ^ s) (tyS l a) = a s := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  have hinj : ∀ t, l ^ t = l ^ s ↔ t = s := fun t => (Nat.pow_right_injective hl).eq_iff
  simp only [hinj]
  rw [Finset.sum_ite_eq', if_pos]
  have hs : s < l ^ s := Nat.lt_pow_self (by omega)
  exact Finset.mem_range.2 (by omega)

omit hl in
theorem coeff_tyS_of_ne (a : ℕ → C) (m : ℕ) (hm : ∀ s, l ^ s ≠ m) : PowerSeries.coeff m (tyS l a) = 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun s _ => if_neg (hm s)

theorem tyS_eq (a : ℕ → C) (f : PowerSeries C) (h1 : ∀ s, PowerSeries.coeff (l ^ s) f = a s)
    (h2 : ∀ m, (∀ s, l ^ s ≠ m) → PowerSeries.coeff m f = 0) : tyS l a = f := by
  ext m
  by_cases h : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := h
    rw [coeff_tyS_pow hl, h1]
  · push_neg at h
    rw [coeff_tyS_of_ne a m h, h2 m h]

omit hl in
theorem tyS_zero : tyS l (fun _ => (0 : C)) = 0 := by
  ext m
  unfold tyS
  simp

end TyS

section Repar

theorem van_univ {τ : Type} {f : MvPowerSeries τ C} (h : MvPowerSeries.constantCoeff f = 0) :
    Van Set.univ f := by
  intro ν hν
  have hν0 : ν = 0 := by
    ext w
    by_contra hw
    exact hν w (Finsupp.mem_support_iff.2 hw) (Set.mem_univ w)
  subst hν0
  simpa using h

theorem constantCoeff_subst_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod]
  simp only [map_pow, ha]
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (∏ x ∈ d.support, (0 : C) ^ d x) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)
    rw [h0, smul_zero]

theorem alongCv_repar {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {τ : PowerSeries C} (hτ : PowerSeries.constantCoeff τ = 0)
    (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.subst τ (γ i)) f = PowerSeries.subst τ (alongCv γ f) := by
  unfold alongCv
  have hγs : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  have hτs : MvPowerSeries.HasSubst (fun _ : Unit => τ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hτ)
  exact (MvPowerSeries.subst_comp_subst_apply hγs hτs f).symm

theorem alongCv_zero {σ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    alongCv (fun _ : σ => (0 : PowerSeries C)) f = 0 := by
  unfold alongCv
  have ha : MvPowerSeries.HasSubst (fun _ : σ => (0 : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_subst ha, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (d.prod fun _ e => (0 : PowerSeries C) ^ e) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)
    simp only [h0, map_zero, smul_zero]

end Repar

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

private theorem ge_zero_lemma (V : VF C) : V.Ge 0 (0 : C) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top

private theorem ge_mul_lemma_2 (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) : V.Ge 0 (a * b) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul]
  have h := add_le_add (show ((0 : ℝ) : WithTop ℝ) ≤ V.v a from ha) (show ((0 : ℝ) : WithTop ℝ) ≤ V.v b from hb)
  simpa using h

private theorem ge_zero_pow' (V : VF C) {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero =>
    change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a ^ 0)
    rw [pow_zero, AddValuation.map_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    exact ge_mul_lemma_2 V ih ha

theorem TySet_repar {V : VF C} {g : Fin 2} (τ : PowerSeries C) (hτ : PowerSeries.constantCoeff τ = 0)
    (hint : ∀ f : PowerSeries C, (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.subst τ f)))
    {x x' : ℕ → I g ⊕ JJ I g → C} (hx : x ∈ X.TySet V g)
    (hxx : ∀ n, tyS V.l (fun s => x' s n) = PowerSeries.subst τ (tyS V.l fun s => x s n)) :
    x' ∈ X.TySet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  have hτs : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hs : ∀ f : PowerSeries C, PowerSeries.subst τ f = PowerSeries.substAlgHom hτs f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  refine ⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hγ i).1, hint _ (hγ i).2⟩
  · intro q
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hlam q).1, hint _ (hlam q).2⟩
  · intro i
    rw [alongCv_repar hγ0 hτ, h1 i]
    simp only [hxx, hs, map_sum, map_smul]
  · intro q
    rw [hxx, h2 q, alongCv_repar hγ0 hτ]
    simp only [hxx, hs, map_add, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> simp

private theorem coeff_subst_smul_X (c : C) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (c • (PowerSeries.X : PowerSeries C)) f) = c ^ n * PowerSeries.coeff n f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [PowerSeries.smul_eq_C_mul])),
    finsum_eq_single _ n]
  · rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_self, smul_eq_mul]
    ring
  · intro d hd
    rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero, smul_zero]

theorem teich_mem (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) (x : ℕ → I g ⊕ JJ I g → C)
    (hx : x ∈ X.TySet V g) : teich V.l c x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  refine X.TySet_repar (c • PowerSeries.X) (by simp [PowerSeries.smul_eq_C_mul]) (fun f hf n => ?_) hx (fun m => ?_)
  · rw [coeff_subst_smul_X]
    exact ge_mul_lemma_2 V (ge_zero_pow' V hc n) (hf n)
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · rw [coeff_subst_smul_X, coeff_tyS_pow hl]
      rfl
    · rw [coeff_subst_smul_X, coeff_tyS_of_ne _ _ hk, mul_zero]

end RawChart

theorem coeff_subst_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (q : ℕ) :
    PowerSeries.coeff (l * q) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = PowerSeries.coeff q f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])), finsum_eq_single _ q]
  · rw [← pow_mul, PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
  · intro d hd
    rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
    intro h
    exact hd (Nat.eq_of_mul_eq_mul_left hl h).symm

theorem coeff_subst_X_pow_of_not_dvd {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (m : ℕ) (hm : ¬ l ∣ m) :
    PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = 0 := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne']))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
  rintro rfl
  exact hm (dvd_mul_right l d)

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem V_mem (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow 1 x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  refine X.TySet_repar (PowerSeries.X ^ V.l) (by simp [hl0.ne']) (fun f hf m => ?_) hx (fun m => ?_)
  · by_cases hd : V.l ∣ m
    · obtain ⟨q, rfl⟩ := hd
      rw [coeff_subst_X_pow hl0]
      exact hf q
    · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]
      exact ge_zero_lemma V
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · cases s with
      | zero =>
        rw [pow_zero, coeff_subst_X_pow_of_not_dvd hl0 _ _ V.l_prime.not_dvd_one]
        simp [Vpow]
      | succ s =>
        rw [pow_succ', coeff_subst_X_pow hl0, coeff_tyS_pow hl]
        simp [Vpow]
    · by_cases hd : V.l ∣ k
      · obtain ⟨q, rfl⟩ := hd
        rw [coeff_subst_X_pow hl0, coeff_tyS_of_ne _ _ (fun s hs => hk (s + 1) (by rw [pow_succ', hs]))]
      · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]

theorem constantCoeff_sg (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (v : κ → C) : MvPowerSeries.constantCoeff (X.sg v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change -∑ i, v i * MvPowerSeries.coeff ((0 : κ →₀ ℕ).mapDomain (fun x : κ => ((0 : Fin 2), x)) +
    Finsupp.single ((1 : Fin 2), i) 1) X.h = 0
  simp only [Finsupp.mapDomain_zero, zero_add]
  rw [Finset.sum_eq_zero, neg_zero]
  intro i _
  rw [hh _ ?_, mul_zero]
  intro s hs
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hs
  rw [hs]
  simp

theorem const_mem_type_set_of_nonneg (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) (ζ : JJ I g → C) (hζ : ∀ q, V.Ge 0 (ζ q)) :
    const0 (Sum.elim 0 ζ) ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hinl : ∀ c : I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = 0 := by
    intro c
    rw [show (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = fun _ => (0 : C) by
      funext s
      simp [const0]]
    exact tyS_zero
  have hinr : ∀ q : JJ I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inr q : I g ⊕ JJ I g)) =
      ζ q • PowerSeries.X := by
    intro q
    refine tyS_eq hl _ _ (fun s => ?_) (fun m hm => ?_)
    · cases s with
      | zero => simp [const0]
      | succ s =>
        have h1 : 1 < V.l ^ (s + 1) :=
          calc 1 < V.l := by omega
            _ = V.l ^ 1 := (pow_one _).symm
            _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hl1 : V.l ≠ 1 := by omega
        simp [const0, PowerSeries.coeff_X, h1.ne', hl1]
    · have hm1 : m ≠ 1 := fun h => hm 0 (by simp [h])
      simp [PowerSeries.coeff_X, hm1]
  refine ⟨fun _ => 0, fun q => ζ q • PowerSeries.X, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    refine ⟨by simp, fun n => ?_⟩
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_X]
    split_ifs
    · simpa using hζ q
    · simpa using ge_zero_lemma V
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [hinl]
  · intro q
    rw [hinr, alongCv_zero (X.constantCoeff_sg hh _)]
    simp [hinl]

theorem zero_mem (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [tyS_zero]
  · intro q
    rw [alongCv_zero (X.constantCoeff_sg hh _)]
    simp [tyS_zero]

end RawChart

end Formalism.L2.FormalSeriesBounds
