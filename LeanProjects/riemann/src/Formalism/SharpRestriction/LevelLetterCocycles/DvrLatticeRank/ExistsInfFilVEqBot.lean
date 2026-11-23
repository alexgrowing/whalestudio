import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Module

section Ser

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def LB (m : ℤ) (f : ℤ → V) : Prop := ∀ k < m, f k = 0

def smulS (g : PowerSeries LL) (f : ℤ → V) : ℤ → V :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem smulS_eq_sum {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) (N : ℕ)
    (hN : k - m < N) : smulS g f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (k - j) := by
  unfold smulS
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjN
  push_neg at hjN
  apply hj
  rw [hf (k - j) (by omega), smul_zero]

theorem LB_smulS {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) : LB m (smulS g f) := by
  intro k hk
  unfold smulS
  exact finsum_eq_zero_of_forall_eq_zero fun j => by rw [hf _ (by omega), smul_zero]

theorem smulS_X_pow {m : ℤ} {f : ℤ → V} (hf : LB m f) (K : ℕ) :
    smulS ((PowerSeries.X : PowerSeries LL) ^ K) f = fun k => f (k - K) := by
  funext k
  unfold smulS
  rw [finsum_eq_single _ K]
  · rw [PowerSeries.coeff_X_pow_self, one_smul]
  · intro j hj
    rw [PowerSeries.coeff_X_pow, if_neg hj, zero_smul]

theorem smulS_mul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g h : PowerSeries LL) :
    smulS (g * h) f = smulS g (smulS h f) := by
  funext k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N := ⟨(k - m).toNat + 1, by omega⟩
  rw [smulS_eq_sum hf _ k N hN, smulS_eq_sum ((LB_smulS hf) h) _ k N hN]
  have h1 : ∀ n : ℕ, PowerSeries.coeff n (g * h) • f (k - n) =
      ∑ a ∈ Finset.Ico 0 (n + 1), (PowerSeries.coeff a g * PowerSeries.coeff (n - a) h) • f (k - n) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul,
      Finset.range_eq_Ico]
  simp_rw [h1]
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have haN : a < N := (Finset.mem_Ico.mp ha).2
  rw [smulS_eq_sum hf h (k - a) (N - a) (by push_cast [haN.le]; omega),
    Finset.sum_Ico_eq_sum_range, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul, Nat.add_sub_cancel_left, Nat.cast_add, sub_add_eq_sub_sub]

end Ser

section Cnt

variable {LL : Type} [Field LL] {E : Type} [AddCommGroup E] [Module LL E]

def sumAt {r : ℕ} (e : Fin r → ℤ → E) (j : ℤ) : (Fin r → LL) →ₗ[LL] E :=
  ∑ m, (LinearMap.proj m : (Fin r → LL) →ₗ[LL] LL).smulRight (e m j)

theorem sumAt_apply {r : ℕ} (e : Fin r → ℤ → E) (j : ℤ) (c : Fin r → LL) :
    sumAt e j c = ∑ m, c m • e m j := by
  simp [sumAt]

def Ub {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) (j : ℤ) :
    Submodule LL (Fin r → LL) :=
  ⨅ (i : ℤ) (_ : i < j), (Fil (-i + 1)).comap (sumAt e i)

theorem mem_Ub {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) (j : ℤ) (c : Fin r → LL) :
    c ∈ Ub Fil e j ↔ ∀ i < j, ∑ m, c m • e m i ∈ Fil (-i + 1) := by
  simp only [Ub, Submodule.mem_iInf, Submodule.mem_comap, sumAt_apply]

private theorem Ub_succ_eq_inf_comap_sumAt {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) (j : ℤ) :
    Ub Fil e (j + 1) =
      Ub Fil e j ⊓ (Fil (-j + 1)).comap (sumAt e j) := by
  ext c
  rw [Submodule.mem_inf, Submodule.mem_comap, mem_Ub, mem_Ub,
    sumAt_apply]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp hi) with hlt | rfl
    · exact h1 i hlt
    · exact h2

private theorem finrank_comap_subtype_eq_finrank_inf (S N : Submodule LL E) :
    finrank LL ↥(N.comap S.subtype) = finrank LL ↥(S ⊓ N) := by
  rw [← Submodule.finrank_map_subtype_eq S, Submodule.map_comap_subtype]

private theorem finrank_map_mkQ_add_finrank_inf (S N : Submodule LL E) [FiniteDimensional LL S] :
    finrank LL ↥(S.map N.mkQ) + finrank LL ↥(S ⊓ N) = finrank LL ↥S := by
  have h := LinearMap.finrank_range_add_finrank_ker (N.mkQ ∘ₗ S.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, Submodule.ker_mkQ,
    finrank_comap_subtype_eq_finrank_inf] at h
  exact h

theorem Ub_anti {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) {j j' : ℤ} (h : j ≤ j') :
    Ub Fil e j' ≤ Ub Fil e j := by
  intro c hc
  rw [mem_Ub] at hc ⊢
  exact fun i hi => hc i (lt_of_lt_of_le hi h)

variable {r : ℕ} {Fil : ℤ → Submodule LL E} (hFa : Antitone Fil) (D : Submodule LL E)
  [FiniteDimensional LL D] {e : Fin r → ℤ → E}

include hFa in

theorem count_step (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hS : ∀ k : ℤ, ∀ w ∈ D ⊓ Fil (-k), ∃ c : Fin r → LL,
      (∀ j < k, ∑ m, c m • e m j ∈ Fil (-j + 1)) ∧ ∑ m, c m • e m k - w ∈ Fil (-k + 1))
    (j : ℤ) :
    finrank LL ↥(Ub Fil e (j + 1)) + finrank LL ↥(D ⊓ Fil (-j)) =
      finrank LL ↥(Ub Fil e j) + finrank LL ↥(D ⊓ Fil (-j + 1)) := by
  have hQfin : FiniteDimensional LL ↥(D ⊓ Fil (-j)) := Submodule.finiteDimensional_of_le inf_le_left
  let Φ : ↥(Ub Fil e j) →ₗ[LL] E ⧸ Fil (-j + 1) :=
    (Fil (-j + 1)).mkQ ∘ₗ sumAt e j ∘ₗ (Ub Fil e j).subtype
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  have hker : LinearMap.ker Φ =
      (Ub Fil e (j + 1)).comap (Ub Fil e j).subtype := by
    ext ⟨c, hc⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Ub_succ_eq_inf_comap_sumAt, Submodule.mem_inf,
      Submodule.mem_comap]
    change Submodule.Quotient.mk (sumAt e j c) = (0 : E ⧸ Fil (-j + 1)) ↔ c ∈ _ ∧ sumAt e j c ∈ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  have hrange : LinearMap.range Φ = (D ⊓ Fil (-j)).map (Fil (-j + 1)).mkQ := by
    apply le_antisymm
    · rintro y ⟨⟨c, hc⟩, rfl⟩
      refine ⟨sumAt e j c, ?_, rfl⟩
      rw [sumAt_apply]
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (he m j)
    · rintro y ⟨w, hw, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := hS j w hw
      refine ⟨⟨c, (mem_Ub Fil e j c).mpr hc1⟩, ?_⟩
      change Submodule.Quotient.mk (sumAt e j c) = (Submodule.Quotient.mk w : E ⧸ Fil (-j + 1))
      rw [Submodule.Quotient.eq, sumAt_apply]
      exact hc2
  have hL1 := finrank_map_mkQ_add_finrank_inf (D ⊓ Fil (-j)) (Fil (-j + 1))
  have hinf : D ⊓ Fil (-j) ⊓ Fil (-j + 1) = D ⊓ Fil (-j + 1) := by
    rw [inf_assoc, inf_eq_right.mpr (hFa (by omega : -j ≤ -j + 1))]
  rw [hinf] at hL1
  rw [hrange, hker, finrank_comap_subtype_eq_finrank_inf,
    inf_eq_right.mpr (Ub_anti Fil e (by omega : j ≤ j + 1))] at hrk
  omega

include hFa in

theorem indep_of_span (a₀ a₁ : ℤ) (h₀ : D ≤ Fil a₀) (h₁ : D ⊓ Fil a₁ = ⊥)
    (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hS : ∀ k : ℤ, ∀ w ∈ D ⊓ Fil (-k), ∃ c : Fin r → LL,
      (∀ j < k, ∑ m, c m • e m j ∈ Fil (-j + 1)) ∧ ∑ m, c m • e m k - w ∈ Fil (-k + 1))
    (hr : r ≤ finrank LL ↥D) (c : Fin r → LL) (hc : ∀ j, ∑ m, c m • e m j ∈ Fil (-j + 1)) :
    c = 0 := by
  have hstep := count_step hFa D he hS
  have hconst : ∀ n : ℕ, finrank LL ↥(Ub Fil e (1 - a₁ + n)) +
      finrank LL ↥(D ⊓ Fil (-(1 - a₁ + n) + 1)) =
      finrank LL ↥(Ub Fil e (1 - a₁)) + finrank LL ↥(D ⊓ Fil (-(1 - a₁) + 1)) := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, add_zero]
    | succ n ih =>
      have h := hstep (1 - a₁ + n)
      have e1 : (1 - a₁ + ((n + 1 : ℕ) : ℤ)) = 1 - a₁ + n + 1 := by push_cast; ring
      have e2 : -(1 - a₁ + (n : ℤ) + 1) + 1 = -(1 - a₁ + (n : ℤ)) := by ring
      rw [e1, e2]
      omega
  have hJ := hconst (a₁ - a₀).toNat
  have hfa1 : -(1 - a₁) + 1 = a₁ := by ring
  rw [hfa1, h₁, finrank_bot] at hJ
  have hDle : D ⊓ Fil (-(1 - a₁ + ((a₁ - a₀).toNat : ℤ)) + 1) = D :=
    inf_eq_left.mpr (le_trans h₀ (hFa (by omega)))
  rw [hDle] at hJ
  have hle : finrank LL ↥(Ub Fil e (1 - a₁)) ≤ r :=
    (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun LL)
  have h0 : finrank LL ↥(Ub Fil e (1 - a₁ + ((a₁ - a₀).toNat : ℤ))) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have hcmem : c ∈ Ub Fil e (1 - a₁ + ((a₁ - a₀).toNat : ℤ)) :=
    (mem_Ub Fil e _ c).mpr fun i _ => hc i
  rw [h0, Submodule.mem_bot] at hcmem
  exact hcmem

include hFa in

theorem smulS_sub_cc {M : ℤ} {f : ℤ → E} (hf : LB M f) (hfF : ∀ k, f k ∈ Fil (-k))
    (g : PowerSeries LL) (j : ℤ) :
    smulS g f j - PowerSeries.constantCoeff g • f j ∈ Fil (-j + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, j - M < ((N + 1 : ℕ) : ℤ) := ⟨(j - M).toNat, by omega⟩
  rw [smulS_eq_sum hf g j (N + 1) hN, Finset.sum_range_succ',
    PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ ?_
  exact hFa (show -j + 1 ≤ -(j - ((n + 1 : ℕ) : ℤ)) by omega) (hfF _)

include hFa in

theorem dvd_of_dg (a₁ : ℤ) (h₁ : D ⊓ Fil a₁ = ⊥) (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hind : ∀ c : Fin r → LL, (∀ j, ∑ m, c m • e m j ∈ Fil (-j + 1)) → c = 0) :
    ∀ (k : ℕ) (g : Fin r → PowerSeries LL),
      (∀ j : ℤ, ∑ m, smulS (g m) (e m) j ∈ Fil ((k : ℤ) - j)) → ∀ m, PowerSeries.X ^ k ∣ g m := by
  have hvan : ∀ m, LB (1 - a₁) (e m) := by
    intro m k hk
    have h := Submodule.mem_inf.mp (he m k)
    have h' : e m k ∈ D ⊓ Fil a₁ :=
      Submodule.mem_inf.mpr ⟨h.1, hFa (show a₁ ≤ -k by omega) h.2⟩
    rw [h₁] at h'
    exact (Submodule.mem_bot LL).mp h'
  intro k
  induction k with
  | zero => intro g _ m; simp
  | succ k ih =>
    intro g hg
    have hk : ∀ m, PowerSeries.X ^ k ∣ g m :=
      ih g fun j => hFa (show (k : ℤ) - j ≤ ((k + 1 : ℕ) : ℤ) - j by omega) (hg j)
    choose q hq using hk
    have hshift : ∀ m i, smulS (g m) (e m) i = smulS (q m) (e m) (i - k) := by
      intro m i
      rw [hq m, smulS_mul (hvan m), smulS_X_pow ((LB_smulS (hvan m)) (q m))]
    have hc : ∀ j : ℤ, ∑ m, PowerSeries.constantCoeff (q m) • e m j ∈ Fil (-j + 1) := by
      intro j
      have h1 := hg (j + k)
      simp only [hshift, add_sub_cancel_right] at h1
      rw [show ((k + 1 : ℕ) : ℤ) - (j + k) = -j + 1 by push_cast; ring] at h1
      have h2 : ∑ m, (smulS (q m) (e m) j - PowerSeries.constantCoeff (q m) • e m j) ∈ Fil (-j + 1) :=
        Submodule.sum_mem _ fun m _ =>
          smulS_sub_cc hFa (hvan m) (fun i => (Submodule.mem_inf.mp (he m i)).2) (q m) j
      rw [Finset.sum_sub_distrib] at h2
      have h3 := Submodule.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at h3
    have h0 := hind (fun m => PowerSeries.constantCoeff (q m)) hc
    intro m
    have hm : PowerSeries.constantCoeff (q m) = 0 := by
      have := congrFun h0 m
      simpa using this
    obtain ⟨q', hq'⟩ := PowerSeries.X_dvd_iff.mpr hm
    exact ⟨q', by rw [hq m, hq', pow_succ, mul_assoc]⟩

end Cnt

section Quo

variable {LL : Type} [Field LL] {E : Type} [AddCommGroup E] [Module LL E]

theorem map_smulS {E' : Type} [AddCommGroup E'] [Module LL E'] (π : E →ₗ[LL] E') {M : ℤ}
    {f : ℤ → E} (hf : LB M f) (g : PowerSeries LL) (j : ℤ) :
    π (smulS g f j) = smulS g (fun k => π (f k)) j := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, j - M < N := ⟨(j - M).toNat + 1, by omega⟩
  have hf' : LB M (fun k => π (f k)) := fun k hk => by
    simp only [hf k hk, map_zero]
  rw [smulS_eq_sum hf g j N hN, smulS_eq_sum hf' g j N hN, map_sum]
  simp only [map_smul]

private theorem mkQ_mem_map_mkQ_iff_mem_sup (R S : Submodule LL E) (x : E) :
    R.mkQ x ∈ S.map R.mkQ ↔ x ∈ S ⊔ R := by
  rw [← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_comm]

theorem dvd_of_dg_mod {r : ℕ} {F : ℤ → Submodule LL E} (hFa : Antitone F) (D R : Submodule LL E)
    [FiniteDimensional LL D] (hFD : ∀ a, F a ≤ D) (hDR : D ⊓ R = ⊥) (a₀ a₁ : ℤ) (h₀ : D ≤ F a₀)
    (h₁ : F a₁ = ⊥) {e : Fin r → ℤ → E} (hLB : ∀ m, ∃ M, LB M (e m))
    (he : ∀ m k, e m k ∈ F (-k) ⊔ R)
    (hS : ∀ k : ℤ, ∀ w ∈ F (-k), ∃ c : Fin r → LL,
      (∀ j < k, ∑ m, c m • e m j ∈ F (-j + 1) ⊔ R) ∧ ∑ m, c m • e m k - w ∈ F (-k + 1) ⊔ R)
    (hr : r ≤ finrank LL ↥D) (k : ℕ) (g : Fin r → PowerSeries LL)
    (hg : ∀ j : ℤ, ∑ m, smulS (g m) (e m) j ∈ F ((k : ℤ) - j) ⊔ R) :
    ∀ m, PowerSeries.X ^ k ∣ g m := by
  have hFa' : Antitone (fun a => (F a).map R.mkQ) := fun a b h => Submodule.map_mono (hFa h)
  have hDfin : FiniteDimensional LL ↥(D.map R.mkQ) := by
    have hrg : D.map R.mkQ = LinearMap.range (R.mkQ ∘ₗ D.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [hrg]
    infer_instance
  have h₀' : D.map R.mkQ ≤ (F a₀).map R.mkQ := Submodule.map_mono h₀
  have h₁' : D.map R.mkQ ⊓ (F a₁).map R.mkQ = ⊥ := by
    rw [h₁, Submodule.map_bot, inf_bot_eq]
  have he' : ∀ m i, R.mkQ (e m i) ∈ D.map R.mkQ ⊓ (F (-i)).map R.mkQ := by
    intro m i
    have h := (mkQ_mem_map_mkQ_iff_mem_sup R (F (-i)) (e m i)).mpr (he m i)
    exact Submodule.mem_inf.mpr ⟨Submodule.map_mono (hFD _) h, h⟩
  have hπ : ∀ (c : Fin r → LL) (j : ℤ), ∑ m, c m • R.mkQ (e m j) = R.mkQ (∑ m, c m • e m j) := by
    intro c j
    rw [map_sum]
    simp only [map_smul]
  have hS' : ∀ i : ℤ, ∀ w ∈ D.map R.mkQ ⊓ (F (-i)).map R.mkQ, ∃ c : Fin r → LL,
      (∀ j < i, ∑ m, c m • R.mkQ (e m j) ∈ (F (-j + 1)).map R.mkQ) ∧
        ∑ m, c m • R.mkQ (e m i) - w ∈ (F (-i + 1)).map R.mkQ := by
    intro i w hw
    obtain ⟨w0, hw0, rfl⟩ := (Submodule.mem_inf.mp hw).2
    obtain ⟨c, hc1, hc2⟩ := hS i w0 hw0
    refine ⟨c, fun j hj => ?_, ?_⟩
    · rw [hπ]
      exact (mkQ_mem_map_mkQ_iff_mem_sup R _ _).mpr (hc1 j hj)
    · rw [hπ, ← map_sub]
      exact (mkQ_mem_map_mkQ_iff_mem_sup R _ _).mpr hc2
  have hr' : r ≤ finrank LL ↥(D.map R.mkQ) := by
    have h := finrank_map_mkQ_add_finrank_inf D R
    rw [hDR, finrank_bot] at h
    omega
  have hind : ∀ c : Fin r → LL, (∀ j, ∑ m, c m • R.mkQ (e m j) ∈ (F (-j + 1)).map R.mkQ) → c = 0 :=
    fun c hc => indep_of_span (Fil := fun a => (F a).map R.mkQ)
      (e := fun m i => R.mkQ (e m i)) hFa' (D.map R.mkQ) a₀ a₁ h₀' h₁' he' hS' hr' c hc
  have hg' : ∀ j : ℤ, ∑ m, smulS (g m) (fun i => R.mkQ (e m i)) j ∈ (F ((k : ℤ) - j)).map R.mkQ := by
    intro j
    have hsum : ∑ m, smulS (g m) (fun i => R.mkQ (e m i)) j = R.mkQ (∑ m, smulS (g m) (e m) j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      obtain ⟨M, hM⟩ := hLB m
      exact (map_smulS R.mkQ hM (g m) j).symm
    rw [hsum]
    exact (mkQ_mem_map_mkQ_iff_mem_sup R _ _).mpr (hg j)
  exact dvd_of_dg (Fil := fun a => (F a).map R.mkQ) (e := fun m i => R.mkQ (e m i))
    hFa' (D.map R.mkQ) a₁ h₁' he' hind k g hg'

end Quo

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filB_anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

private theorem tmul_mem_FilV_of_mem_Fil (a : ℤ) (x : V) {y : BdR} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  refine LinearMap.mem_range.mpr ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : (PD.Fil a).restrictScalars Qp), ?_⟩
  rw [AlgebraTensorModule.map_tmul]
  rfl

theorem filVB_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab z hz
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hz
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul x y =>
    rw [AlgebraTensorModule.map_tmul]
    exact tmul_mem_FilV_of_mem_Fil PD a _ (filB_anti PD hab y.2)
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv

theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_FilV_of_mem_Fil PD a x ha⟩
  | add u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨min a b, Submodule.add_mem _ (filVB_anti PD (min_le_left a b) ha)
      (filVB_anti PD (min_le_right a b) hb)⟩

theorem coord_mem {ι : Type} (b : Basis ι Qp V) (a : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V) a) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b z i ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hz
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [AlgebraTensorModule.map_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    exact Submodule.smul_of_tower_mem _ _ y.2
  | add u v hu hv =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hu hv

theorem filV_sep (z : V ⊗[Qp] BdR) (hz : ∀ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  obtain ⟨ι, b⟩ : Σ ι : Type, Basis ι Qp V := ⟨_, Basis.ofVectorSpace Qp V⟩
  have key : ∀ i, TensorProduct.equivFinsuppOfBasisLeft b z i = 0 := fun i =>
    PD.Fil_sep _ fun a => coord_mem PD (LL := LL) b a z (hz a) i
  have key2 : TensorProduct.equivFinsuppOfBasisLeft b z = 0 := Finsupp.ext key
  exact (LinearEquiv.map_eq_zero_iff _).mp key2

theorem exists_le_filV (D : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL D] :
    ∃ a : ℤ, D ≤ FilV PD (LL := LL) (V := V) a := by
  have key : ∀ S : Finset (V ⊗[Qp] BdR), ∃ a : ℤ, ∀ x ∈ S, x ∈ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
    intro S
    refine Finset.induction_on S ⟨0, by simp⟩ ?_
    intro x S hx ih
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := filV_exh PD (LL := LL) x
    refine ⟨min a b, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact filVB_anti PD (min_le_right a b) hb
    · exact filVB_anti PD (min_le_left a b) (ha y hy)
  obtain ⟨S, hS⟩ := Module.Finite.iff_fg.mp (inferInstance : FiniteDimensional LL D)
  obtain ⟨a, ha⟩ := key S
  refine ⟨a, ?_⟩
  rw [← hS]
  exact Submodule.span_le.mpr ha

theorem exists_inf_filV_eq_bot (D : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL D] :
    ∃ a : ℤ, D ⊓ FilV PD (LL := LL) (V := V) a = ⊥ := by
  have hex : ∃ n : ℕ, ∃ a : ℤ, finrank LL ↥(D ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a) = n :=
    ⟨_, 0, rfl⟩
  obtain ⟨a, ha⟩ := Nat.find_spec hex
  refine ⟨a, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine filV_sep PD (LL := LL) x fun b => ?_
  rcases le_total b a with hba | hab
  · exact filVB_anti PD hba (Submodule.mem_inf.mp hx).2
  · have hle : D ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b ≤ D ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a :=
      inf_le_inf_left D (filVB_anti PD hab)
    have hfin : FiniteDimensional LL ↥(D ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have heq : D ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b = D ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [ha]; exact Nat.find_min' hex ⟨b, rfl⟩)
    rw [← heq] at hx
    exact (Submodule.mem_inf.mp hx).2

end Fil

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
