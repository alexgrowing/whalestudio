import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOps

noncomputable section

open Classical

namespace PI.BeDiagZp.SubstW

def Rint (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]
    have := norm_nonneg a
    have := norm_nonneg b
    nlinarith
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

def SerS {K : Type*} [CommRing K] (S : Subring K) (σ : Type*) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map S.subtype).range

theorem mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by
  constructor
  · rintro ⟨g, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e g).2
  · intro h
    obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries σ S, ∀ e, MvPowerSeries.coeff e g = ⟨MvPowerSeries.coeff e f, h e⟩ :=
      ⟨fun e => ⟨MvPowerSeries.coeff e f, h e⟩, fun e => rfl⟩
    refine ⟨g, ?_⟩
    ext e
    rw [MvPowerSeries.coeff_map, hg]
    rfl

theorem constantCoeff_lift {K : Type*} [CommRing K] (S : Subring K) {σ : Type*}
    (g : MvPowerSeries σ S) {c : S}
    (h : MvPowerSeries.constantCoeff (MvPowerSeries.map S.subtype g) = (c : K)) :
    MvPowerSeries.constantCoeff g = c := by
  apply Subtype.ext
  rw [← h, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map]
  rfl

theorem mvsubst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ K} {f : MvPowerSeries σ K}
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, a i ∈ SerS S τ) (hf : f ∈ SerS S σ) : MvPowerSeries.subst a f ∈ SerS S τ := by
  choose b hb using ha
  obtain ⟨g, rfl⟩ := hf
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (b i) = 0 := by
    intro i
    exact constantCoeff_lift S (b i) (c := 0) (by rw [hb i, ha0 i]; rfl)
  have hsub : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  refine ⟨MvPowerSeries.subst b g, ?_⟩
  rw [MvPowerSeries.map_subst hsub]
  congr 1
  funext i
  exact hb i

theorem integral_iff {p : ℕ} [Fact p.Prime] {σ : Type*} (f : MvPowerSeries σ ℂ_[p]) :
    IntegralMv f ↔ f ∈ SerS (Rint p) σ := by
  rw [mem_SerS]
  exact Iff.rfl

end PI.BeDiagZp.SubstW

namespace PI.BeDiagZp

open SubstW

theorem intSubst_holds : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, IntegralMv (s i)) → IntegralMv f → IntegralMv (MvPowerSeries.subst s f) := by
  intro p _ σ τ _ f s h0 hs hf
  rw [integral_iff] at hf ⊢
  exact mvsubst_mem_SerS (Rint p) h0 (fun i => (integral_iff (s i)).1 (hs i)) hf

end PI.BeDiagZp

namespace PI.BeDiagZp.SubstW

variable {p : ℕ} [Fact p.Prime]

theorem deg_eq {σ : Type*} (α : σ →₀ ℕ) : (α.sum fun _ k => k) = α.degree := by
  rw [Finsupp.degree_apply]
  rfl

theorem coeff_pow_eq_zero {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) {n : ℕ} {d : σ →₀ ℕ} (h : d.degree < n) :
    MvPowerSeries.coeff d (F ^ n) = 0 :=
  MvPowerSeries.coeff_of_lt_order
    ((Nat.cast_lt.mpr h).trans_le (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hF))

theorem coeff_expMv_eq {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) (d : σ →₀ ℕ) {N : ℕ} (hN : d.degree < N) :
    MvPowerSeries.coeff d (expMv F) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by
  have e1 : MvPowerSeries.coeff d (expMv F) = ∑ n ∈ Finset.range ((d.sum fun _ k => k) + 1),
      MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := rfl
  rw [e1, deg_eq]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at *
    omega
  · intro n hn hn'
    simp only [Finset.mem_range, not_lt] at hn hn'
    rw [coeff_pow_eq_zero hF (by omega), zero_div]

def expTr {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • F ^ n

theorem coeff_expTr {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (N : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (expTr F N) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [expTr, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

theorem expMv_subst {σ τ : Type*} [Finite σ] {s : σ → MvPowerSeries τ ℂ_[p]}
    (hs0 : ∀ i, MvPowerSeries.constantCoeff (s i) = 0) {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv (MvPowerSeries.subst s F) = MvPowerSeries.subst s (expMv F) := by
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  have hE : MvPowerSeries.constantCoeff (MvPowerSeries.subst s F) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 hF
  ext e
  have hD : ((e.degree + 1 : ℕ) : ℕ∞) ≤ (expMv F - expTr F (e.degree + 1)).order := by
    apply MvPowerSeries.le_order
    intro d hd
    have hd' : d.degree < e.degree + 1 := by exact_mod_cast hd
    rw [map_sub, coeff_expMv_eq hF d hd', coeff_expTr, sub_self]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (s i).order :=
    le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hs0 i)
  have hsD : ((e.degree + 1 : ℕ) : ℕ∞) ≤
      (MvPowerSeries.subst s (expMv F - expTr F (e.degree + 1))).order := by
    refine le_trans ?_ (MvPowerSeries.le_order_subst hs _)
    calc ((e.degree + 1 : ℕ) : ℕ∞) ≤ (expMv F - expTr F (e.degree + 1)).order := hD
      _ = 1 * (expMv F - expTr F (e.degree + 1)).order := (one_mul _).symm
      _ ≤ _ := by
        first
          | exact mul_le_mul_right' h1 _
          | exact mul_le_mul_right h1 _
          | gcongr
  have h0 : MvPowerSeries.coeff e (MvPowerSeries.subst s (expMv F - expTr F (e.degree + 1))) = 0 :=
    MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hsD)
  rw [MvPowerSeries.subst_sub hs, map_sub, sub_eq_zero] at h0
  rw [h0, coeff_expMv_eq hE e (Nat.lt_succ_self _), expTr, ← MvPowerSeries.coe_substAlgHom hs]
  simp only [map_sum, map_smul, map_pow, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

end PI.BeDiagZp.SubstW

namespace PI.BeDiagZp

open SubstW

theorem power_series_diagonal_linear : S1 := by
  intro p _ σ τ _ f g s hs0 hsi hfg
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  obtain ⟨h0, hI⟩ := hfg
  unfold Simeq
  rw [← MvPowerSeries.subst_sub hs]
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 h0, ?_⟩
  rw [expMv_subst hs0 h0]
  exact intSubst_holds p σ τ (expMv (f - g)) s hs0 hsi hI

end PI.BeDiagZp
