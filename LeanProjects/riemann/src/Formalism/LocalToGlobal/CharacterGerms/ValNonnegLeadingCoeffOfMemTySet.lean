import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem finsupp_deg_one {σ : Type} (e : σ →₀ ℕ) (h : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  have hdeg : ∑ j ∈ e.support, e j = 1 := h
  have hne : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hdeg
    exact absurd hdeg (by norm_num)
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ j ∈ e.support, e j ≤ 1 := fun j hj =>
    hdeg ▸ Finset.single_le_sum (f := fun k => e k) (fun _ _ => Nat.zero_le _) hj
  have hei : e i = 1 := by
    have h1 := hle i hi
    have h2 := Finsupp.mem_support_iff.mp hi
    omega
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj
    simp [hei]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hj)]
    by_contra hc
    have hjs : j ∈ e.support := Finsupp.mem_support_iff.mpr hc
    have h2 : e i + e j ≤ ∑ k ∈ e.support, e k := by
      rw [← Finset.sum_pair (f := fun k => e k) (Ne.symm hj)]
      apply Finset.sum_le_sum_of_subset
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hjs
    omega

theorem coeff_alongCv_low {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := fun i => by
    have := hγ i 0 (by omega)
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0),
    finsum_eq_sum_of_support_subset (s := Finset.univ.image fun i : σ => Finsupp.single i 1)]
  · rw [Finset.sum_image (fun a _ b _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : (Finsupp.single i 1 : σ →₀ ℕ).prod (fun s e => γ s ^ e) = γ i := by
      rw [Finsupp.prod_single_index (h := fun s e => γ s ^ e) (pow_zero _), pow_one]
    show MvPowerSeries.coeff (Finsupp.single i 1) f •
      MvPowerSeries.coeff (Finsupp.single () n) ((Finsupp.single i 1 : σ →₀ ℕ).prod fun s e => γ s ^ e) = _
    rw [hp, smul_eq_mul]
    rfl
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.coe_image, Set.mem_image]
    by_contra hc
    apply he
    have hdeg : e.degree ≠ 1 := fun h => by
      obtain ⟨i, hi⟩ := finsupp_deg_one e h
      exact hc ⟨i, by simp, hi.symm⟩
    by_cases h0 : e.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have h2 : 2 ≤ e.degree := by omega
      have hdvd : (PowerSeries.X : PowerSeries C) ^ (n * e.degree) ∣ e.prod fun s m => γ s ^ m := by
        unfold Finsupp.prod
        rw [Finsupp.degree_apply, pow_mul, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_dvd_prod_of_dvd
        intro i _
        exact pow_dvd_pow_of_dvd (PowerSeries.X_pow_dvd_iff.2 (hγ i)) _
      have hz : PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 hdvd n (by nlinarith)
      show MvPowerSeries.coeff e f • PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0
      rw [hz, smul_zero]

theorem coeff_tyS_lt {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (s : ℕ) (ha : ∀ i < s, a i = 0) (m : ℕ) (hm : m < l ^ s) :
    PowerSeries.coeff m (tyS l a) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with ht
  · apply ha
    by_contra hc
    push_neg at hc
    have : l ^ s ≤ l ^ t := Nat.pow_le_pow_right (by omega) hc
    omega
  · rfl

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem val_nonneg_leading_coeff_of_mem_tySet (V : VF C) (g : Fin 2)
    (hlin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C))
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (hsat : ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (hmis : ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)))
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (s : ℕ) (h0 : ∀ i < s, x i = 0) (n : I g ⊕ JJ I g) :
    V.Ge 0 (x s n) := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨w, hw, huw⟩ := hsat
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hlin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have hpos : 1 ≤ V.l ^ s := Nat.one_le_pow _ _ (by omega)
  have hlow : ∀ (m : ℕ) (hm1 : 1 ≤ m), (∀ i, ∀ m' < m, PowerSeries.coeff m' (γ i) = 0) → ∀ i,
      PowerSeries.coeff m (γ i) = ∑ c : I g, X.u g c i * PowerSeries.coeff m (tyS V.l fun s => x s (Sum.inl c)) := by
    intro m hm1 hm i
    have e1 := coeff_alongCv_low hm1 hm (hlg0 i)
    rw [h1 i, map_sum] at e1
    simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      PowerSeries.coeff_smul, smul_eq_mul] at e1
    exact e1.symm
  have hord : ∀ m, m < V.l ^ s → ∀ i, PowerSeries.coeff m (γ i) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm i
      by_cases hm0 : m = 0
      · rw [hm0, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact (hγ i).1
      · rw [hlow m (by omega) (fun i m' hm' => ih m' hm' (by omega) i) i]
        apply Finset.sum_eq_zero
        intro c _
        rw [coeff_tyS_lt hl2 _ s (fun i hi => by rw [h0 i hi]; rfl) m hm, mul_zero]
  have hord' : ∀ i, ∀ m < V.l ^ s, PowerSeries.coeff m (γ i) = 0 := fun i m hm => hord m hm i
  have hlead : ∀ i, PowerSeries.coeff (V.l ^ s) (γ i) = ∑ c : I g, X.u g c i * x s (Sum.inl c) := by
    intro i
    rw [hlow _ hpos hord' i]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coeff_tyS_pow hl2]
  have hinl : ∀ c', x s (Sum.inl c') = ∑ i, PowerSeries.coeff (V.l ^ s) (γ i) * w i c' := by
    intro c'
    simp only [hlead, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ c : I g, ∑ i, X.u g c i * x s (Sum.inl c) * w i c' = (if c = c' then 1 else 0) * x s (Sum.inl c) := by
      intro c
      rw [← huw c c', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinlInt : ∀ c', V.Ge 0 (x s (Sum.inl c')) := by
    intro c'
    rw [hinl c']
    exact VF.Ge.sum fun i _ => ((hγ i).2 _).mul_int (hw i c')
  cases n with
  | inl c' => exact hinlInt c'
  | inr q =>
    have e2 := congrArg (PowerSeries.coeff (V.l ^ s)) (h2 q)
    rw [coeff_tyS_pow hl2, map_add, map_sub, coeff_alongCv_low hpos hord' (X.constantCoeff_sg hh _), map_sum] at e2
    have e3 : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (X.sg (X.u (1 - g) q)) * PowerSeries.coeff (V.l ^ s) (γ i) =
        ∑ c : I g, X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) := by
      simp only [hlead, sg1, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    have e4 : ∀ c : I g, PowerSeries.coeff (V.l ^ s) (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) =
        if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) else 0 := by
      intro c
      split_ifs
      · rw [PowerSeries.coeff_smul, coeff_tyS_pow hl2, smul_eq_mul]
      · rw [map_zero]
    simp only [e4] at e2
    rw [e3, sub_add, ← Finset.sum_sub_distrib] at e2
    rw [e2]
    refine ((hlam q).2 _).sub (VF.Ge.sum fun c _ => ?_)
    split_ifs with hc
    · rw [sub_self]
      exact VF.Ge.zero 0
    · rw [sub_zero]
      exact (hmis c q hc).mul_int (hinlInt c)

end RawChart

end Formalism.L2.FormalSeriesBounds
