import Formalism.LocalToGlobal.PairingIndexBounds.LatticeNormPowers.CloseUnitNorms.TestVectorMemSchwartzBruhat

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Places

variable (D : D7)

def cjK : D.host.K →+* D.host.K :=
  ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E)).codRestrict D.host.K
    (fun a => conj_mem D a.2)

theorem cjK_cjK (a : D.host.K) : cjK D (cjK D a) = a := Subtype.ext (conj_conj D _)

def fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

theorem fK_cjK (a : D.host.K) : fK D (cjK D a) = starRingEnd ℂ (fK D a) :=
  Formalism.BasicNotions.Examples₂.emb_conj _ _ _

variable {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def tK : D.host.K →+* ℂ_[p] := (Lp D lam).comp (algebraMap D.host.K D.host.E)

def tKc : D.host.K →+* ℂ_[p] := (tK D lam).comp (cjK D)

theorem tK_apply (a : D.host.K) : tK D lam a = Lp D lam (a : D.host.E) := rfl

theorem tKc_apply (a : D.host.K) : tKc D lam a = Lp D lam (D.host.conj (a : D.host.E)) := rfl

theorem tKc_cjK (a : D.host.K) : tKc D lam (cjK D a) = tK D lam a := by
  show tK D lam (cjK D (cjK D a)) = _
  rw [cjK_cjK]

theorem tK_cjK (a : D.host.K) : tK D lam (cjK D a) = tKc D lam a := rfl

def Ip (a : D.host.K) : Prop := ‖tK D lam a‖ ≤ 1 ∧ ‖tKc D lam a‖ ≤ 1

theorem Ip_O (u : 𝓞 D.host.K) : Ip D lam (u : D.host.K) := by
  obtain ⟨u', hu'⟩ := conj_O D u
  refine ⟨norm_Lp_le_one D lam u, ?_⟩
  rw [tKc_apply]
  have := norm_Lp_le_one D lam u'
  rwa [hu'] at this

theorem norm_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

theorem norm_sub_le' {x y : ℂ_[p]} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x - y‖ ≤ C := by
  rw [sub_eq_add_neg]
  exact (norm_max _ _).trans (max_le hx (by rwa [norm_neg]))

theorem norm_add_le' {x y : ℂ_[p]} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C :=
  (norm_max _ _).trans (max_le hx hy)

theorem locInt (a : D.host.K) (h : Ip D lam a) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : 𝓞 D.host.K, (s : D.host.K) * a = (u : D.host.K) := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.K).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  obtain ⟨e, s, hs, hes⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hy0) p hp.out.ne_one
  have hz : IsIntegral ℤ ((y.natAbs : D.host.K) * a) := by
    rcases Int.natAbs_eq y with h' | h'
    · have : (y.natAbs : D.host.K) * a = y • a := by
        rw [zsmul_eq_mul]; congr 1; conv_rhs => rw [h']
        simp
      rw [this]; exact hy
    · have : (y.natAbs : D.host.K) * a = -(y • a) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1; conv_rhs => rw [h']
        simp
      rw [this]; exact hy.neg
  have hsc : Nat.Coprime s p := ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hs).symm
  set z : 𝓞 D.host.K := ⟨(y.natAbs : D.host.K) * a, hz⟩ with hzdef
  have hzE : oE D z = (p : D.host.E) ^ e * ((s : D.host.E) * (a : D.host.E)) := by
    show (((y.natAbs : D.host.K) * a : D.host.K) : D.host.E) = _
    rw [hes]; push_cast; ring
  have hb : ∀ x : ℂ_[p], ‖x‖ ≤ 1 → ‖(p : ℂ_[p]) ^ e * ((s : ℂ_[p]) * x)‖ ≤ (p : ℝ) ^ (-(e : ℤ)) := by
    intro x hx
    rw [norm_mul, norm_mul, normC_p_pow, normC_nat_coprime hsc, one_mul]
    calc _ ≤ (p : ℝ) ^ (-(e : ℤ)) * 1 := mul_le_mul_of_nonneg_left hx (by positivity)
      _ = _ := mul_one _
  obtain ⟨u, hu⟩ := lemT D lam z (le_refl e)
    (by simp only [hzE, map_mul, map_pow, map_natCast]; exact hb _ h.1)
    (by simp only [hzE, map_mul, map_pow, map_natCast]; exact hb _ h.2)
  refine ⟨s, hsc, u, ?_⟩
  apply (algebraMap D.host.K D.host.E).injective
  have hp0E : (p : D.host.E) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  apply mul_left_cancel₀ hp0E
  show (p : D.host.E) ^ e * (((s : D.host.K) * a : D.host.K) : D.host.E) = (p : D.host.E) ^ e * oE D u
  rw [← hu, hzE]; push_cast; ring

theorem locIntVec {ι : Type*} [Fintype ι] (a : ι → D.host.K) (h : ∀ i, Ip D lam (a i)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : ι → 𝓞 D.host.K, ∀ i, (s : D.host.K) * a i = (u i : D.host.K) := by
  classical
  choose s hs u hu using fun i => locInt D lam (a i) (h i)
  refine ⟨∏ i, s i, Nat.Coprime.prod_left (fun i _ => hs i),
    fun i => ((∏ j ∈ Finset.univ.erase i, s j : ℕ) : 𝓞 D.host.K) * u i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  push_cast
  rw [mul_assoc, hu i]

theorem int_of_coprime {t : ℝ} {s N : ℕ} (hs : Nat.Coprime s p) {k1 k2 : ℤ} (h1 : (s : ℝ) * t = k1)
    (h2 : (p : ℝ) ^ N * t = k2) : ∃ k : ℤ, t = k := by
  have hcop : IsCoprime (s : ℤ) ((p ^ N : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr (hs.pow_right N)
  obtain ⟨u, v, huv⟩ := hcop
  have huvR : (u : ℝ) * s + (v : ℝ) * (p : ℝ) ^ N = 1 := by exact_mod_cast huv
  refine ⟨u * k1 + v * k2, ?_⟩
  calc t = ((u : ℝ) * s + (v : ℝ) * (p : ℝ) ^ N) * t := by rw [huvR, one_mul]
    _ = _ := by push_cast; rw [← h1, ← h2]; ring

theorem mem_of_coprime {V : Type*} [AddCommGroup V] [Module ℂ V] (S : AddSubgroup V) {x : V} {s N : ℕ}
    (hs : Nat.Coprime s p) (h1 : (s : ℂ) • x ∈ S) (h2 : ((p : ℂ) ^ N) • x ∈ S) : x ∈ S := by
  have hcop : IsCoprime (s : ℤ) ((p ^ N : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr (hs.pow_right N)
  obtain ⟨u, v, huv⟩ := hcop
  have huvC : (u : ℂ) * s + (v : ℂ) * (p : ℂ) ^ N = 1 := by exact_mod_cast huv
  have : x = u • ((s : ℂ) • x) + v • (((p : ℂ) ^ N) • x) := by
    rw [← Int.cast_smul_eq_zsmul ℂ u, ← Int.cast_smul_eq_zsmul ℂ v, smul_smul, smul_smul, ← add_smul, huvC,
      one_smul]
  rw [this]
  exact add_mem (zsmul_mem h1 u) (zsmul_mem h2 v)

end Places

section Approx

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem idem_norm {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) :
    ‖tK D lam (ε : D.host.K) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) ∧ ‖tK D lam (ε : D.host.K)‖ = 1 ∧
      ‖tKc D lam (ε : D.host.K)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  obtain ⟨h1, h2⟩ := hId
  rw [lamC_phi_zero_eq] at h1 h2
  exact ⟨h1, norm_eq_one_of_close (lt_of_le_of_lt h1 (pzpow_lt_one hm)), h2⟩

theorem approxO {n : ℕ} {ε : 𝓞 D.host.K} (hId : IsIdem D lam (2 * n + 2) ε) (μ : 𝓞 D.host.K) :
    ∃ c0 : ℤ, ‖tKc D lam (μ : D.host.K) - c0‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨c0, w, hw⟩ := alg_step D lam ε n hId μ
  obtain ⟨-, he, -⟩ := idem_norm D lam (by omega) hId
  refine ⟨c0, ?_⟩
  have h := congrArg (Lp D lam) hw
  rw [map_mul, map_add, map_mul, map_mul, map_intCast, map_pow, map_natCast] at h
  have h2 : tK D lam (ε : D.host.K) * (tKc D lam (μ : D.host.K) - c0) = (p : ℂ_[p]) ^ n * Lp D lam (oE D w) := by
    rw [tK_apply, tKc_apply]
    linear_combination h
  have h3 := congrArg norm h2
  rw [norm_mul, he, one_mul, norm_mul, normC_p_pow] at h3
  rw [h3]
  calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left (norm_Lp_le_one D lam w) (by positivity)
    _ = _ := mul_one _

theorem approxKc {n : ℕ} {ε : 𝓞 D.host.K} (hId : IsIdem D lam (2 * n + 2) ε) (a : D.host.K)
    (ha : Ip D lam a) : ∃ m : Fin (p ^ n), ‖tKc D lam a - ((m : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨s, hs, u, hu⟩ := locInt D lam a ha
  obtain ⟨c0, hc0⟩ := approxO D lam hId u
  have hcop : IsCoprime (s : ℤ) ((p ^ n : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr (hs.pow_right n)
  obtain ⟨x, y, hxy⟩ := hcop
  have hpn : (0 : ℤ) < (p ^ n : ℕ) := by exact_mod_cast pow_pos hp.out.pos n
  set m : ℤ := (c0 * x) % ((p ^ n : ℕ) : ℤ) with hm
  have hm0 : 0 ≤ m := Int.emod_nonneg _ hpn.ne'
  have hm1 : m < (p ^ n : ℕ) := Int.emod_lt_of_pos _ hpn
  refine ⟨⟨m.toNat, by omega⟩, ?_⟩
  have hcast : ((m.toNat : ℕ) : ℂ_[p]) = (m : ℂ_[p]) := by
    have : (((m.toNat : ℕ) : ℤ) : ℂ_[p]) = (m : ℂ_[p]) := by rw [Int.toNat_of_nonneg hm0]
    rw [← this, Int.cast_natCast]
  show ‖tKc D lam a - ((m.toNat : ℕ) : ℂ_[p])‖ ≤ _
  rw [hcast]
  have hq : ((p ^ n : ℕ) : ℤ) ∣ c0 * x - m :=
    ⟨c0 * x / ((p ^ n : ℕ) : ℤ), by
      have := Int.mul_ediv_add_emod (c0 * x) ((p ^ n : ℕ) : ℤ)
      rw [hm]; linarith⟩
  obtain ⟨q, hq⟩ := hq
  have hs1 := normC_nat_coprime (p := p) hs
  have hxyC : (x : ℂ_[p]) * s + (y : ℂ_[p]) * (p : ℂ_[p]) ^ n = 1 := by exact_mod_cast hxy
  have hqC : (c0 : ℂ_[p]) * x - m = (p : ℂ_[p]) ^ n * q := by exact_mod_cast hq
  have huC : (s : ℂ_[p]) * tKc D lam a = tKc D lam (u : D.host.K) := by
    rw [← hu, map_mul, map_natCast]
  have key : (s : ℂ_[p]) * (tKc D lam a - m) =
      (tKc D lam (u : D.host.K) - c0) + (p : ℂ_[p]) ^ n * ((c0 : ℂ_[p]) * y + s * q) := by
    linear_combination huC - (c0 : ℂ_[p]) * hxyC + (s : ℂ_[p]) * hqC
  have h3 := congrArg norm key
  rw [norm_mul, hs1, one_mul] at h3
  rw [h3]
  refine norm_add_le' hc0 ?_
  rw [norm_mul, normC_p_pow]
  have : ‖(c0 : ℂ_[p]) * y + s * q‖ ≤ 1 := by
    have e : (c0 : ℂ_[p]) * y + s * q = ((c0 * y + s * q : ℤ) : ℂ_[p]) := by push_cast; ring
    rw [e]; exact normC_int_le_one _
  calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := mul_one _

theorem Ip_cjK {a : D.host.K} (ha : Ip D lam a) : Ip D lam (cjK D a) :=
  ⟨by rw [tK_cjK]; exact ha.2, by rw [tKc_cjK]; exact ha.1⟩

theorem approxK {n : ℕ} {ε : 𝓞 D.host.K} (hId : IsIdem D lam (2 * n + 2) ε) (a : D.host.K)
    (ha : Ip D lam a) : ∃ m : Fin (p ^ n), ‖tK D lam a - ((m : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨m, hm⟩ := approxKc D lam hId (cjK D a) (Ip_cjK D lam ha)
  exact ⟨m, by rwa [tKc_cjK] at hm⟩

theorem idem_step {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) :
    IsIdem D lam (m + 1) (3 * ε ^ 2 - 2 * ε ^ 3) := by
  obtain ⟨h1, he, h2⟩ := idem_norm D lam hm hId
  have hpp : (p : ℝ) ^ (-(m : ℤ)) * (p : ℝ) ^ (-(m : ℤ)) ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
    apply zpow_le_zpow_right₀
    · exact_mod_cast hp.out.one_lt.le
    · push_cast; omega
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(m : ℤ)) := by positivity
  have hc1 : ‖tKc D lam (ε : D.host.K)‖ ≤ 1 := (Ip_O D lam ε).2
  constructor
  · rw [lamC_phi_zero_eq]
    have e : Lp D lam (((3 * ε ^ 2 - 2 * ε ^ 3 : 𝓞 D.host.K) : D.host.K) : D.host.E) - 1 =
        (tK D lam (ε : D.host.K) - 1) * (tK D lam (ε : D.host.K) - 1) *
          (((-2 : ℤ) : ℂ_[p]) * tK D lam (ε : D.host.K) - ((1 : ℤ) : ℂ_[p])) := by
      have ht : tK D lam (algebraMap (𝓞 D.host.K) D.host.K ε) = tK D lam (ε : D.host.K) := rfl
      change (tK D lam) (algebraMap (𝓞 D.host.K) D.host.K (3 * ε ^ 2 - 2 * ε ^ 3)) - 1 = _
      simp only [map_sub, map_mul, map_pow, map_ofNat, ht]
      push_cast
      ring
    rw [e, norm_mul, norm_mul]
    have h3 : ‖((-2 : ℤ) : ℂ_[p]) * tK D lam (ε : D.host.K) - ((1 : ℤ) : ℂ_[p])‖ ≤ 1 := by
      refine norm_sub_le' ?_ (normC_int_le_one _)
      rw [norm_mul, he, mul_one]; exact normC_int_le_one _
    calc _ ≤ (p : ℝ) ^ (-(m : ℤ)) * (p : ℝ) ^ (-(m : ℤ)) * 1 :=
          mul_le_mul (mul_le_mul h1 h1 (norm_nonneg _) hpos) h3 (norm_nonneg _) (by positivity)
      _ ≤ _ := by rw [mul_one]; exact hpp
  · rw [lamC_phi_zero_eq]
    have e : Lp D lam (D.host.conj (((3 * ε ^ 2 - 2 * ε ^ 3 : 𝓞 D.host.K) : D.host.K) : D.host.E)) =
        tKc D lam (ε : D.host.K) * tKc D lam (ε : D.host.K) *
          (((3 : ℤ) : ℂ_[p]) - ((2 : ℤ) : ℂ_[p]) * tKc D lam (ε : D.host.K)) := by
      have ht : tKc D lam (algebraMap (𝓞 D.host.K) D.host.K ε) = tKc D lam (ε : D.host.K) := rfl
      change (tKc D lam) (algebraMap (𝓞 D.host.K) D.host.K (3 * ε ^ 2 - 2 * ε ^ 3)) = _
      simp only [map_sub, map_mul, map_pow, map_ofNat, ht]
      push_cast
      ring
    rw [e, norm_mul, norm_mul]
    have h3 : ‖((3 : ℤ) : ℂ_[p]) - ((2 : ℤ) : ℂ_[p]) * tKc D lam (ε : D.host.K)‖ ≤ 1 := by
      refine norm_sub_le' (normC_int_le_one _) ?_
      rw [norm_mul]
      calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (normC_int_le_one _) hc1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    calc _ ≤ (p : ℝ) ^ (-(m : ℤ)) * (p : ℝ) ^ (-(m : ℤ)) * 1 :=
          mul_le_mul (mul_le_mul h2 h2 (norm_nonneg _) hpos) h3 (norm_nonneg _) (by positivity)
      _ ≤ _ := by rw [mul_one]; exact hpp

theorem idem_all {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) (M : ℕ) :
    ∃ η : 𝓞 D.host.K, IsIdem D lam (m + M) η := by
  induction M with
  | zero => exact ⟨ε, hId⟩
  | succ M ih =>
    obtain ⟨η, hη⟩ := ih
    exact ⟨_, idem_step D lam (m := m + M) (by omega) hη⟩

end Approx

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Bounds

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def Bd (a : D.host.K) (e1 e2 : ℤ) : Prop :=
  ‖tK D lam a‖ ≤ (p : ℝ) ^ e1 ∧ ‖tKc D lam a‖ ≤ (p : ℝ) ^ e2

variable {D lam}

theorem Bd.ip {a : D.host.K} (h : Bd D lam a 0 0) : Ip D lam a := by
  simpa [Bd, Ip] using h

theorem Ip.bd {a : D.host.K} (h : Ip D lam a) : Bd D lam a 0 0 := by
  simpa [Bd, Ip] using h

theorem pz_mono {e f : ℤ} (h : e ≤ f) : (p : ℝ) ^ e ≤ (p : ℝ) ^ f :=
  zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) h

theorem pz_pos (e : ℤ) : (0 : ℝ) < (p : ℝ) ^ e := zpow_pos (by exact_mod_cast hp.out.pos) e

theorem Bd.mono {a : D.host.K} {e1 e2 f1 f2 : ℤ} (h : Bd D lam a e1 e2) (h1 : e1 ≤ f1) (h2 : e2 ≤ f2) :
    Bd D lam a f1 f2 := ⟨h.1.trans (pz_mono h1), h.2.trans (pz_mono h2)⟩

theorem Bd.mul {a b : D.host.K} {e1 e2 f1 f2 : ℤ} (ha : Bd D lam a e1 e2) (hb : Bd D lam b f1 f2) :
    Bd D lam (a * b) (e1 + f1) (e2 + f2) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rw [map_mul, norm_mul, zpow_add₀ hp0]
    exact mul_le_mul ha.1 hb.1 (norm_nonneg _) (pz_pos _).le
  · rw [map_mul, norm_mul, zpow_add₀ hp0]
    exact mul_le_mul ha.2 hb.2 (norm_nonneg _) (pz_pos _).le

theorem Bd.cj {a : D.host.K} {e1 e2 : ℤ} (ha : Bd D lam a e1 e2) : Bd D lam (cjK D a) e2 e1 :=
  ⟨by rw [tK_cjK]; exact ha.2, by rw [tKc_cjK]; exact ha.1⟩

theorem Bd.sub {a b : D.host.K} {e1 e2 : ℤ} (ha : Bd D lam a e1 e2) (hb : Bd D lam b e1 e2) :
    Bd D lam (a - b) e1 e2 :=
  ⟨by rw [map_sub]; exact norm_sub_le' ha.1 hb.1, by rw [map_sub]; exact norm_sub_le' ha.2 hb.2⟩

theorem Bd.sum {ι : Type*} (s : Finset ι) {a : ι → D.host.K} {e1 e2 : ℤ} (ha : ∀ i ∈ s, Bd D lam (a i) e1 e2) :
    Bd D lam (∑ i ∈ s, a i) e1 e2 :=
  ⟨by rw [map_sum]; exact norm_sum_le' _ _ (pz_pos _).le fun i hi => (ha i hi).1,
   by rw [map_sum]; exact norm_sum_le' _ _ (pz_pos _).le fun i hi => (ha i hi).2⟩

theorem Bd.nat (m : ℕ) : Bd D lam (m : D.host.K) 0 0 := by
  constructor <;> rw [map_natCast, zpow_zero] <;>
    exact (by simpa using normC_int_le_one (p := p) (m : ℤ))

theorem Bd.ppow (n : ℕ) : Bd D lam ((p : D.host.K) ^ n) (-(n : ℤ)) (-(n : ℤ)) := by
  constructor <;> rw [map_pow, map_natCast, normC_p_pow]

theorem Bd.ppow_inv (n : ℕ) : Bd D lam (((p : D.host.K) ^ n)⁻¹) (n : ℤ) (n : ℤ) := by
  constructor <;> rw [map_inv₀, map_pow, map_natCast, norm_inv, normC_p_pow, zpow_neg, inv_inv]

theorem Bd.idem {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) :
    Bd D lam (ε : D.host.K) 0 (-(m : ℤ)) := by
  obtain ⟨-, h1, h2⟩ := idem_norm D lam hm hId
  exact ⟨by rw [h1, zpow_zero], h2⟩

end Bounds

section LBs

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

variable (D cc δ) in

def cv {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ξ : Fin r → D.host.K) : VC D N N' :=
  ∑ i, fK D (ξ i) • ee D cc δ b i

theorem cv_sub {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ξ ξ' : Fin r → D.host.K) :
    cv D cc δ b (ξ - ξ') = cv D cc δ b ξ - cv D cc δ b ξ' := by
  simp only [cv, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem cv_smul {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (a : D.host.K) (ξ : Fin r → D.host.K) :
    cv D cc δ b (fun i => a * ξ i) = fK D a • cv D cc δ b ξ := by
  simp only [cv, map_mul, mul_smul, Finset.smul_sum]

theorem cv_change {r : ℕ} {f g : Fin r → Matrix (Fin N') (Fin N) D.host.E} {c : Fin r → Fin r → D.host.K}
    (hc : ∀ j, ee D cc δ g j = cv D cc δ f (fun i => c i j)) (ζ : Fin r → D.host.K) :
    cv D cc δ g ζ = cv D cc δ f (fun i => ∑ j, c i j * ζ j) := by
  simp only [cv, hc, Finset.smul_sum, map_sum, Finset.sum_smul, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

variable (D cc δ) in

structure LB (p : ℕ) (La' : AddSubgroup (VC D N N')) {r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop where
  int : ∀ x ∈ La', ∀ y ∈ La', ∃ k : ℤ, (Hf D (tor0 D cc δ) x y).im = k
  sd : ∀ v, (∀ y ∈ La', ∃ k : ℤ, (Hf D (tor0 D cc δ) v y).im = k) → v ∈ La'
  ok : ∀ (κ : 𝓞 D.host.K) (v : VC D N N'), v ∈ La' → fK D (κ : D.host.K) • v ∈ La'
  mem : ∀ i, ee D cc δ b i ∈ La'
  loc : ∀ v ∈ La', ∃ s : ℕ, Nat.Coprime s p ∧ ∃ κ : Fin r → 𝓞 D.host.K,
    (s : ℂ) • v = cv D cc δ b (fun i => (κ i : D.host.K))
  li : ∀ ξ : Fin r → D.host.K, cv D cc δ b ξ = 0 → ξ = 0

variable {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {La' : AddSubgroup (VC D N N')} {r : ℕ}
  {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}

theorem LB.cvO (h : LB D cc δ p La' b) (u : Fin r → 𝓞 D.host.K) :
    cv D cc δ b (fun i => (u i : D.host.K)) ∈ La' :=
  sum_mem fun i _ => h.ok (u i) _ (h.mem i)

theorem LB.coord (h : LB D cc δ p La' b) {v : VC D N N'} (hv : v ∈ La') :
    ∃ ζ : Fin r → D.host.K, v = cv D cc δ b ζ ∧ ∀ j, Ip D lam (ζ j) := by
  obtain ⟨s, hs, κ, hκ⟩ := h.loc v hv
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hp.out.ne_one (by simpa using hs)
  have hsK : (s : D.host.K) ≠ 0 := by exact_mod_cast hs0
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  refine ⟨fun j => (s : D.host.K)⁻¹ * (κ j : D.host.K), ?_, fun j => ?_⟩
  · rw [cv_smul, ← hκ, map_inv₀, map_natCast, smul_smul, inv_mul_cancel₀ hsC, one_smul]
  · have h1 := normC_nat_coprime (p := p) hs
    obtain ⟨h2, h3⟩ := Ip_O D lam (κ j)
    constructor
    · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, h1, inv_one, one_mul]; exact h2
    · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, h1, inv_one, one_mul]; exact h3

theorem LB.memOf (h : LB D cc δ p La' b) {ξ : Fin r → D.host.K} (hξ : ∀ i, Ip D lam (ξ i)) {Np : ℕ}
    (hN : ((p : ℂ) ^ Np) • cv D cc δ b ξ ∈ La') : cv D cc δ b ξ ∈ La' := by
  obtain ⟨s, hs, u, hu⟩ := locIntVec D lam ξ hξ
  refine mem_of_coprime La' hs ?_ hN
  have : (s : ℂ) • cv D cc δ b ξ = cv D cc δ b (fun i => (u i : D.host.K)) := by
    simp_rw [← hu]
    rw [cv_smul, map_natCast]
  rw [this]
  exact h.cvO u

theorem LB.ipOf (h : LB D cc δ p La' b) {ξ : Fin r → D.host.K} (hξ : cv D cc δ b ξ ∈ La') (i : Fin r) :
    Ip D lam (ξ i) := by
  obtain ⟨ζ, h1, h2⟩ := h.coord lam hξ
  have : ξ - ζ = 0 := h.li _ (by rw [cv_sub, h1, sub_self])
  rw [sub_eq_zero.mp this]
  exact h2 i

theorem LB.pairInt (h : LB D cc δ p La' b) {ξ ξ' : Fin r → D.host.K}
    (hn : ∀ i j, Ip D lam (ξ i * cjK D (ξ' j))) {Np : ℕ} {k : ℤ}
    (hk : (p : ℝ) ^ Np * (Hf D (tor0 D cc δ) (cv D cc δ b ξ) (cv D cc δ b ξ')).im = k) :
    ∃ k' : ℤ, (Hf D (tor0 D cc δ) (cv D cc δ b ξ) (cv D cc δ b ξ')).im = k' := by
  obtain ⟨s, hs, u, hu⟩ := locIntVec D lam (fun ij : Fin r × Fin r => ξ ij.1 * cjK D (ξ' ij.2))
    (fun ij => hn ij.1 ij.2)
  have hterm : ∀ j, ∃ kj : ℤ, (s : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b ξ)
      (fK D (ξ' j) • ee D cc δ b j)).im = kj := by
    intro j
    obtain ⟨kj, hkj⟩ := h.int _ (h.cvO (fun i => u (i, j))) _ (h.mem j)
    refine ⟨kj, ?_⟩
    rw [← hkj, ← im_natCast_mul, Hf_smul_right, ← fK_cjK, ← mul_assoc, ← Hf_smul_left]
    congr 2
    have : ∀ i, ((u (i, j) : 𝓞 D.host.K) : D.host.K) = ((s : D.host.K) * cjK D (ξ' j)) * ξ i := by
      intro i; rw [← hu (i, j)]; ring
    simp_rw [this]
    rw [cv_smul, map_mul, map_natCast]
  choose kj hkj using hterm
  refine int_of_coprime (p := p) hs (k1 := ∑ j, kj j) ?_ hk
  conv_lhs => rw [cv.eq_1 D cc δ b ξ']
  rw [Hf_sum_right, Complex.im_sum, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => hkj j

end LBs

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Dual

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
variable {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {r : ℕ}

theorem dual {A B : AddSubgroup (VC D N N')} {f g : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hA : LB D cc δ p A f) (hB : LB D cc δ p B g) {m0 : ℕ} (hm0 : 1 ≤ m0) {ε : 𝓞 D.host.K}
    (hId : IsIdem D lam m0 ε) {Np : ℕ} (hcom : ∀ v ∈ B, ((p : ℂ) ^ Np) • v ∈ A)
    {c d : Fin r → Fin r → D.host.K} (hc : ∀ j, ee D cc δ g j = cv D cc δ f (fun i => c i j))
    (hd : ∀ i, ee D cc δ f i = cv D cc δ g (fun j => d j i)) (t : ℕ)
    (hbd : ∀ i j, ‖tKc D lam (c i j)‖ ≤ (p : ℝ) ^ (t : ℤ)) (i j : Fin r) :
    ‖tK D lam (d j i)‖ ≤ (p : ℝ) ^ (t : ℤ) := by
  have hp0K : (p : D.host.K) ^ Np ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hc1 : ∀ i j, Bd D lam (c i j) Np t := by
    intro i j
    have hmem : cv D cc δ f (fun i => (p : D.host.K) ^ Np * c i j) ∈ A := by
      rw [cv_smul, ← hc, map_pow, map_natCast]; exact hcom _ (hB.mem j)
    have h2 := (Bd.ppow_inv (D := D) (lam := lam) Np).mul (hA.ipOf lam hmem i).bd
    refine ⟨?_, hbd i j⟩
    have e : ((p : D.host.K) ^ Np)⁻¹ * ((p : D.host.K) ^ Np * c i j) = c i j := by field_simp
    rw [e] at h2
    simpa using h2.1
  obtain ⟨η, hη⟩ := idem_all D lam hm0 hId Np
  obtain ⟨η', hη'⟩ := conj_O D η
  have hηK : (η' : D.host.K) = cjK D (η : D.host.K) := Subtype.ext hη'
  have hbη := Bd.idem (m := m0 + Np) (by omega) hη
  have hbη' : Bd D lam (η' : D.host.K) (-((m0 + Np : ℕ) : ℤ)) 0 := hηK ▸ hbη.cj
  have hκ : (((p : 𝓞 D.host.K) ^ t * η : 𝓞 D.host.K) : D.host.K) = (p : D.host.K) ^ t * (η : D.host.K) := by
    push_cast; rfl
  have hκ' : (((p : 𝓞 D.host.K) ^ t * η' : 𝓞 D.host.K) : D.host.K) = (p : D.host.K) ^ t * (η' : D.host.K) := by
    push_cast; rfl
  have hx : fK D ((p : D.host.K) ^ t * (η : D.host.K)) • ee D cc δ f i ∈ B := by
    apply hB.sd
    intro v hv
    obtain ⟨ζ, hvζ, hζ⟩ := hB.coord lam hv
    have e1 : Hf D (tor0 D cc δ) (fK D ((p : D.host.K) ^ t * (η : D.host.K)) • ee D cc δ f i) v =
        Hf D (tor0 D cc δ) (ee D cc δ f i) (fK D ((p : D.host.K) ^ t * (η' : D.host.K)) • v) := by
      rw [Hf_smul_left, Hf_smul_right]
      congr 1
      rw [hηK, map_mul, map_mul, map_mul, fK_cjK, Complex.conj_conj, map_pow, map_pow, map_natCast,
        Complex.conj_natCast]
    rw [e1]
    apply hA.int _ (hA.mem i)
    have e2 : fK D ((p : D.host.K) ^ t * (η' : D.host.K)) • v =
        cv D cc δ f (fun i' => ((p : D.host.K) ^ t * (η' : D.host.K)) * ∑ j', c i' j' * ζ j') := by
      rw [cv_smul, ← cv_change hc, ← hvζ]
    rw [e2]
    apply hA.memOf lam (Np := Np)
    · intro i'
      have h3 : Bd D lam (∑ j', c i' j' * ζ j') (Np + 0) (t + 0) :=
        Bd.sum _ fun j' _ => (hc1 i' j').mul (hζ j').bd
      exact ((((Bd.ppow t).mul hbη').mul h3).mono (by push_cast; omega) (by omega)).ip
    · rw [← e2, smul_comm, ← hκ']
      exact hA.ok _ _ (hcom _ hv)
  rw [hd, ← cv_smul] at hx
  have h4 := (hB.ipOf lam hx j).1
  obtain ⟨-, h5, -⟩ := idem_norm D lam (m := m0 + Np) (by omega) hη
  rw [map_mul, map_mul, norm_mul, norm_mul, h5, mul_one, map_pow, map_natCast, normC_p_pow] at h4
  have hpos := pz_pos (p := p) (t : ℤ)
  calc ‖tK D lam (d j i)‖ = (p : ℝ) ^ (t : ℤ) * ((p : ℝ) ^ (-(t : ℤ)) * ‖tK D lam (d j i)‖) := by
        rw [← mul_assoc, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; simp
    _ ≤ (p : ℝ) ^ (t : ℤ) * 1 := mul_le_mul_of_nonneg_left h4 hpos.le
    _ = _ := mul_one _

end Dual

section Comm

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

end Comm

section Rat

variable {p : ℕ} [hp : Fact p.Prime] {r : ℕ}

theorem norm_zc (a : ℤ_[p]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [show (algebraMap ℚ_[p] ℂ_[p]) (a : ℚ_[p]) = ((a : ℚ_[p]) : ℂ_[p]) from rfl, PadicComplex.norm_extends']
  rfl

theorem rat_of_inv (Cm : Matrix (Fin r) (Fin r) ℂ_[p]) (X : Fin r → Fin r → ℤ_[p]) (n : ℕ)
    (h : ∀ i l, ∑ j, Cm i j * zc (X j l) = if i = l then (p : ℂ_[p]) ^ n else 0)
    (hC : ∀ i j, ‖Cm i j‖ ≤ 1) : ∃ Y : Fin r → Fin r → ℤ_[p], ∀ i j, Cm i j = zc (Y i j) := by
  let al := algebraMap ℚ_[p] ℂ_[p]
  let Xq : Matrix (Fin r) (Fin r) ℚ_[p] := fun j l => (X j l : ℚ_[p])
  have hp0 : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hmul : Cm * Xq.map al = ((p : ℂ_[p]) ^ n) • (1 : Matrix (Fin r) (Fin r) ℂ_[p]) := by
    ext i l
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact h i l
  have hdet : Xq.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    have h2 : (Xq.map al).det = al Xq.det := (RingHom.map_det al Xq).symm
    rw [h2, h0, map_zero, mul_zero] at h1
    exact pow_ne_zero _ hp0 h1.symm
  have hinv : Xq * Xq⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hinv' : Xq.map al * (Xq⁻¹).map al = 1 := by
    rw [← Matrix.map_mul, hinv, Matrix.map_one al (map_zero al) (map_one al)]
  have hCm : Cm = ((p : ℂ_[p]) ^ n) • (Xq⁻¹).map al := by
    calc Cm = Cm * (Xq.map al * (Xq⁻¹).map al) := by rw [hinv', mul_one]
      _ = _ := by rw [← mul_assoc, hmul, Matrix.smul_mul, one_mul]
  have hval : ∀ i j, Cm i j = al ((p : ℚ_[p]) ^ n * Xq⁻¹ i j) := by
    intro i j
    rw [hCm, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
  have hnorm : ∀ i j, ‖(p : ℚ_[p]) ^ n * Xq⁻¹ i j‖ ≤ 1 := by
    intro i j
    have := hC i j
    rw [hval] at this
    rwa [show al ((p : ℚ_[p]) ^ n * Xq⁻¹ i j) = (((p : ℚ_[p]) ^ n * Xq⁻¹ i j : ℚ_[p]) : ℂ_[p]) from rfl,
      PadicComplex.norm_extends'] at this
  exact ⟨fun i j => ⟨_, hnorm i j⟩, fun i j => hval i j⟩

end Rat

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section ZC

variable {p : ℕ} [hp : Fact p.Prime]

def zcH : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom

theorem norm_zcH (a : ℤ_[p]) : ‖zcH a‖ = ‖a‖ := norm_zc a

theorem norm_zcH_le_one (a : ℤ_[p]) : ‖zcH a‖ ≤ 1 := by rw [norm_zcH]; exact PadicInt.norm_le_one a

theorem appr_close (x : ℤ_[p]) (n : ℕ) : ‖zcH x - ((x.appr n : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (x - ((x.appr n : ℕ) : ℤ_[p])) n).mpr (PadicInt.appr_spec n x)
  rw [← norm_zcH, map_sub, map_natCast] at h
  exact h

end ZC

section Ctxs

variable {N N' : ℕ}

structure Ctx (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (La₁ La : AddSubgroup (VC D N N')) {r : ℕ} (b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (c d : Fin r → Fin r → D.host.K) (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ)
    (Np : ℕ) : Prop where
  h₁ : LB D cc δ p La₁ b₁
  h : LB D cc δ p La b
  com1 : ∀ v ∈ La, ((p : ℂ) ^ Np) • v ∈ La₁
  com2 : ∀ v ∈ La₁, ((p : ℂ) ^ Np) • v ∈ La
  hc : ∀ j, ee D cc δ b j = cv D cc δ b₁ (fun i => c i j)
  hd : ∀ i, ee D cc δ b₁ i = cv D cc δ b (fun j => d j i)
  cb : ∀ i j, ‖tKc D lam (c i j)‖ ≤ 1
  id : IsIdem D lam (2 * n + 2) ε
  fm : FactorsMod n Φ
  phi1 : ∀ a, (∃ x : Fin r → ℤ_[p], ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j)) → Φ a = 1
  phi0 : ∀ a, (¬ ∃ x : Fin r → ℤ_[p], ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j)) → Φ a = 0

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {p : ℕ} [hp : Fact p.Prime] {lam : Qbar →+* ℂ_[p]}
  {La₁ La : AddSubgroup (VC D N N')} {r : ℕ} {b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
  {c d : Fin r → Fin r → D.host.K} {n : ℕ} {ε : 𝓞 D.host.K} {Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ} {Np : ℕ}

theorem Ctx.dc (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (ζ : Fin r → D.host.K) (j : Fin r) :
    ∑ i, d j i * ∑ l, c i l * ζ l = ζ j := by
  have := X.h.li ((fun j => ∑ i, d j i * ∑ l, c i l * ζ l) - ζ)
    (by rw [cv_sub, ← cv_change X.hd, ← cv_change X.hc, sub_self])
  exact congrFun (sub_eq_zero.mp this) j

theorem Ctx.dcm (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (j l : Fin r) :
    ∑ i, d j i * c i l = if j = l then 1 else 0 := by
  have := X.dc (fun l' => if l' = l then 1 else 0) j
  simpa [mul_ite] using this

theorem Ctx.phi_one (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {a : Fin r → ℤ_[p]}
    (x : Fin r → ℤ_[p]) (hx : ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j)) : Φ a = 1 := X.phi1 a ⟨x, hx⟩

theorem Ctx.of_phi_one (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {a : Fin r → ℤ_[p]}
    (ha : Φ a = 1) : ∃ x : Fin r → ℤ_[p], ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j) := by
  by_contra hne
  rw [X.phi0 a hne] at ha
  exact zero_ne_one ha

theorem Ctx.exX (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) :
    ∃ Xm : Fin r → Fin r → ℤ_[p], ∀ i l,
      ∑ j, tKc D lam (c i j) * zcH (Xm j l) = if i = l then (p : ℂ_[p]) ^ n else 0 := by
  have h0 : Φ 0 = 1 := X.phi_one 0 (by intro i; simp)
  have hl : ∀ l : Fin r, ∃ x : Fin r → ℤ_[p], ∀ i,
      zcH ((fun i => if i = l then (p : ℤ_[p]) ^ n else 0 : Fin r → ℤ_[p]) i) =
        ∑ j, tKc D lam (c i j) * zcH (x j) := by
    intro l
    apply X.of_phi_one
    rw [← h0]
    apply X.fm
    intro i
    simp only [Pi.zero_apply, sub_zero]
    split_ifs
    · rw [PadicInt.norm_p_pow]
    · rw [norm_zero]; positivity
  choose x hx using hl
  refine ⟨fun j l => x l j, fun i l => ?_⟩
  rw [← hx l i]
  by_cases hil : i = l <;> simp [hil]

theorem Ctx.dX (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {Xm : Fin r → Fin r → ℤ_[p]}
    (hX : ∀ i l, ∑ j, tKc D lam (c i j) * zcH (Xm j l) = if i = l then (p : ℂ_[p]) ^ n else 0)
    (j l : Fin r) : tKc D lam (d j l) * (p : ℂ_[p]) ^ n = zcH (Xm j l) := by
  have h1 : ∑ i, tKc D lam (d j i) * ∑ j', tKc D lam (c i j') * zcH (Xm j' l) =
      tKc D lam (d j l) * (p : ℂ_[p]) ^ n := by
    simp_rw [hX]
    simp [mul_ite]
  rw [← h1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum, X.dcm]
  simp [apply_ite (tKc D lam)]

theorem Ctx.norm_entry_le_prime_pow (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (j l : Fin r) :
    ‖tKc D lam (d j l)‖ ≤ (p : ℝ) ^ (n : ℤ) := by
  obtain ⟨Xm, hX⟩ := X.exX
  have h := congrArg norm (X.dX hX j l)
  rw [norm_mul, normC_p_pow] at h
  have h2 := norm_zcH_le_one (Xm j l)
  rw [← h] at h2
  calc ‖tKc D lam (d j l)‖ = (‖tKc D lam (d j l)‖ * (p : ℝ) ^ (-(n : ℤ))) * (p : ℝ) ^ (n : ℤ) := by
        rw [mul_assoc, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; simp
    _ ≤ 1 * (p : ℝ) ^ (n : ℤ) := mul_le_mul_of_nonneg_right h2 (pz_pos _).le
    _ = _ := one_mul _

theorem Ctx.exY (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) :
    ∃ Y : Fin r → Fin r → ℤ_[p], ∀ i j, tKc D lam (c i j) = zcH (Y i j) := by
  obtain ⟨Xm, hX⟩ := X.exX
  exact rat_of_inv (fun i j => tKc D lam (c i j)) Xm n hX X.cb

theorem Ctx.bd_d (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (j i : Fin r) :
    Bd D lam (d j i) 0 n :=
  ⟨by
    have := dual lam X.h₁ X.h (m0 := 2 * n + 2) (by omega) X.id X.com1 X.hc X.hd 0
      (by intro i j; simpa using X.cb i j) i j
    simpa using this, X.norm_entry_le_prime_pow j i⟩

theorem Ctx.bd_c (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (i j : Fin r) :
    Bd D lam (c i j) n 0 :=
  ⟨dual lam X.h X.h₁ (m0 := 2 * n + 2) (by omega) X.id X.com2 X.hd X.hc n (fun j i => X.norm_entry_le_prime_pow j i) j i,
    by simpa using X.cb i j⟩

end Ctxs

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section PTs

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def PT (p : ℕ) (S : AddSubgroup V) (x : V) : Prop := ∃ k : ℕ, ((p : ℂ) ^ k) • x ∈ S

theorem pow_smul_mem {p : ℕ} {S : AddSubgroup V} {v : V} (hv : v ∈ S) (k : ℕ) : ((p : ℂ) ^ k) • v ∈ S := by
  have : ((p : ℂ) ^ k) • v = (p ^ k : ℕ) • v := by
    rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl
  rw [this]; exact nsmul_mem hv _

theorem PT.of_mem {p : ℕ} {S : AddSubgroup V} {v : V} (hv : v ∈ S) : PT p S v := ⟨0, by simpa using hv⟩

theorem PT.sub {p : ℕ} {S : AddSubgroup V} {x y : V} (hx : PT p S x) (hy : PT p S y) : PT p S (x - y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  have : ((p : ℂ) ^ (a + b)) • (x - y) = ((p : ℂ) ^ b) • (((p : ℂ) ^ a) • x) - ((p : ℂ) ^ a) • (((p : ℂ) ^ b) • y) := by
    rw [smul_sub, smul_smul, smul_smul, pow_add, mul_comm]
  rw [this]
  exact sub_mem (pow_smul_mem ha _) (pow_smul_mem hb _)

theorem PT.trans {p : ℕ} {S S' : AddSubgroup V} {Np : ℕ} (h : ∀ v ∈ S, ((p : ℂ) ^ Np) • v ∈ S') {x : V}
    (hx : PT p S x) : PT p S' x := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨Np + a, by rw [pow_add, mul_smul]; exact h _ ha⟩

end PTs

section Claims

variable {N N' : ℕ}
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {p : ℕ} [hp : Fact p.Prime] {lam : Qbar →+* ℂ_[p]}
  {La₁ La : AddSubgroup (VC D N N')} {r : ℕ} {b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
  {c d : Fin r → Fin r → D.host.K} {n : ℕ} {ε : 𝓞 D.host.K} {Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ} {Np : ℕ}

theorem LB.memOf' (h : LB D cc δ p La b) (lam : Qbar →+* ℂ_[p]) {ξ : Fin r → D.host.K}
    (hξ : ∀ i, Ip D lam (ξ i)) (hN : PT p La (cv D cc δ b ξ)) : cv D cc δ b ξ ∈ La := by
  obtain ⟨k, hk⟩ := hN
  exact h.memOf lam hξ hk

theorem LB.pairInt' (h : LB D cc δ p La b) (lam : Qbar →+* ℂ_[p]) {ξ ξ' : Fin r → D.host.K}
    (hn : ∀ i j, Ip D lam (ξ i * cjK D (ξ' j))) (h1 : PT p La (cv D cc δ b ξ)) (h2 : PT p La (cv D cc δ b ξ')) :
    cv D cc δ b ξ' ∈ imIntSub (tor0 D cc δ) (cv D cc δ b ξ) := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  obtain ⟨k, hk⟩ := h.int _ hk1 _ hk2
  refine h.pairInt lam hn (Np := k1 + k2) (k := k) ?_
  rw [← hk, Hf_smul_left, Hf_smul_right, map_pow, Complex.conj_natCast, im_natCast_pow_mul, im_natCast_pow_mul,
    pow_add, mul_assoc]

variable (D) in

def lyc (p n : ℕ) (ε : 𝓞 D.host.K) (y : Fin r → Fin (p ^ n)) : Fin r → D.host.K :=
  fun i => ((ε : D.host.K) * ((p : D.host.K) ^ n)⁻¹) * ((y i : ℕ) : D.host.K)

variable (D) in

def vac {m : ℕ} (a : Fin r → Fin m) : Fin r → D.host.K := fun i => ((a i : ℕ) : D.host.K)

theorem bd_q (hId : IsIdem D lam (2 * n + 2) ε) :
    Bd D lam ((ε : D.host.K) * ((p : D.host.K) ^ n)⁻¹) n (-((n : ℤ) + 2)) :=
  ((Bd.idem (by omega) hId).mul (Bd.ppow_inv n)).mono (by omega) (by push_cast; omega)

theorem lyc₂ (hId : IsIdem D lam (2 * n + 2) ε) (y : Fin r → Fin (p ^ n)) (i : Fin r) :
    Bd D lam (lyc D p n ε y i) n (-((n : ℤ) + 2)) :=
  ((bd_q hId).mul (Bd.nat _)).mono (by omega) (by omega)

theorem vac_mem (h : LB D cc δ p La b) {m : ℕ} (a : Fin r → Fin m) : cv D cc δ b (vac D a) ∈ La := by
  have := h.cvO (fun j => ((a j : ℕ) : 𝓞 D.host.K))
  unfold vac
  simpa using this

theorem nat_mem (h : LB D cc δ p La b) (a : Fin r → ℕ) : cv D cc δ b (fun j => (a j : D.host.K)) ∈ La := by
  have := h.cvO (fun j => ((a j : ℕ) : 𝓞 D.host.K))
  simpa using this

theorem ly_PT (h : LB D cc δ p La b) (ε : 𝓞 D.host.K) (y : Fin r → Fin (p ^ n)) :
    PT p La (cv D cc δ b (lyc D p n ε y)) := by
  refine ⟨n, ?_⟩
  have hp0 : (p : D.host.K) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have := h.cvO (fun j => ε * ((y j : ℕ) : 𝓞 D.host.K))
  have e : (fun j => ((ε * ((y j : ℕ) : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)) =
      fun j => (p : D.host.K) ^ n * lyc D p n ε y j := by
    funext j
    simp only [lyc]
    push_cast
    field_simp
  rw [e, cv_smul, map_pow, map_natCast] at this
  exact this

theorem norm_le_one_of_pow {x : ℂ_[p]} (h : ‖(p : ℂ_[p]) ^ n * x‖ ≤ (p : ℝ) ^ (-(n : ℤ))) : ‖x‖ ≤ 1 := by
  rw [norm_mul, normC_p_pow] at h
  have hpos := pz_pos (p := p) (-(n : ℤ))
  by_contra hlt
  push Not at hlt
  have : (p : ℝ) ^ (-(n : ℤ)) * 1 < (p : ℝ) ^ (-(n : ℤ)) * ‖x‖ := mul_lt_mul_of_pos_left hlt hpos
  linarith

theorem norm_le_pow_of_inv {x : ℂ_[p]} (h : ‖((p : ℂ_[p]) ^ n)⁻¹ * x‖ ≤ 1) : ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [norm_mul, norm_inv, normC_p_pow] at h
  have hpos := pz_pos (p := p) (-(n : ℤ))
  calc ‖x‖ = (p : ℝ) ^ (-(n : ℤ)) * (((p : ℝ) ^ (-(n : ℤ)))⁻¹ * ‖x‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 := mul_le_mul_of_nonneg_left h hpos.le
    _ = _ := mul_one _

theorem Ctx.c1a (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {y : Fin r → Fin (p ^ n)}
    (hy : cv D cc δ b₁ (lyc D p n ε y) ∈ La) {a : Fin r → Fin (p ^ n)}
    (ha : Φ (fun i => ((a i : ℕ) : ℤ_[p])) = 1) :
    cv D cc δ b₁ (vac D a) ∈ imIntSub (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) := by
  obtain ⟨x, hx⟩ := X.of_phi_one ha
  set x' : Fin r → D.host.K := fun j => (((x j).appr n : ℕ) : D.host.K) with hx'
  have hv' : cv D cc δ b x' ∈ La := nat_mem X.h _
  have e : cv D cc δ b₁ (vac D a) =
      cv D cc δ b₁ (vac D a - fun i => ∑ j, c i j * x' j) + cv D cc δ b x' := by
    rw [cv_sub, ← cv_change X.hc, sub_add_cancel]
  have hPT : PT p La₁ (cv D cc δ b₁ (vac D a - fun i => ∑ j, c i j * x' j)) := by
    rw [cv_sub, ← cv_change X.hc]
    exact (PT.of_mem (vac_mem X.h₁ a)).sub (PT.trans X.com1 (PT.of_mem hv'))
  rw [e]
  refine add_mem ?_ (X.h.int _ hy _ hv')
  have hbν : ∀ i, Bd D lam ((vac D a - fun i => ∑ j, c i j * x' j) i) n (-(n : ℤ)) := by
    intro i
    constructor
    · have h1 : Bd D lam (vac D a i) n 0 := (Bd.nat _).mono (by omega) le_rfl
      have h2 : Bd D lam (∑ j, c i j * x' j) (n + 0) (0 + 0) :=
        Bd.sum _ fun j _ => (X.bd_c i j).mul (Bd.nat _)
      exact (h1.sub (h2.mono (by omega) (by omega))).1
    · have : tKc D lam ((vac D a - fun i => ∑ j, c i j * x' j) i) =
          ∑ j, tKc D lam (c i j) * (zcH (x j) - (((x j).appr n : ℕ) : ℂ_[p])) := by
        simp only [Pi.sub_apply, vac, map_sub, map_sum, map_mul, map_natCast, hx', mul_sub,
          Finset.sum_sub_distrib]
        rw [← hx i, map_natCast]
      rw [this]
      refine norm_sum_le' _ _ (pz_pos _).le fun j _ => ?_
      rw [norm_mul]
      calc _ ≤ 1 * (p : ℝ) ^ (-(n : ℤ)) :=
            mul_le_mul (X.cb i j) (appr_close _ _) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  exact X.h₁.pairInt' lam
    (fun i j => (((lyc₂ X.id y i).mul (hbν j).cj).mono (by omega) (by omega)).ip) (ly_PT X.h₁ ε y) hPT

theorem Ctx.c1b (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {y : Fin r → Fin (p ^ n)}
    (hy : ∀ a : Fin r → Fin (p ^ n), Φ (fun i => ((a i : ℕ) : ℤ_[p])) = 1 →
      cv D cc δ b₁ (vac D a) ∈ imIntSub (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y))) :
    cv D cc δ b₁ (lyc D p n ε y) ∈ La := by
  apply X.h.sd
  intro v hv
  obtain ⟨ζ, hvζ, hζ⟩ := X.h.coord lam hv
  choose x' hx' using fun j => approxKc D lam X.id (ζ j) (hζ j)
  obtain ⟨Y, hY⟩ := X.exY
  set a' : Fin r → ℤ_[p] := fun i => ∑ j, Y i j * ((x' j : ℕ) : ℤ_[p]) with ha'
  set a : Fin r → Fin (p ^ n) := fun i => ⟨(a' i).appr n, PadicInt.appr_lt _ _⟩ with ha
  have hΦ : Φ (fun i => ((a i : ℕ) : ℤ_[p])) = 1 := by
    have h1 : Φ a' = 1 := X.phi_one (fun j => ((x' j : ℕ) : ℤ_[p])) (by
      intro i
      simp only [ha', map_sum, map_mul, hY])
    rw [← h1]
    apply X.fm
    intro i
    rw [norm_sub_rev]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr (PadicInt.appr_spec n (a' i))
  have e : v = cv D cc δ b₁ ((fun i => ∑ j, c i j * ζ j) - vac D a) + cv D cc δ b₁ (vac D a) := by
    rw [cv_sub, ← cv_change X.hc, ← hvζ, sub_add_cancel]
  have hPT : PT p La₁ (cv D cc δ b₁ ((fun i => ∑ j, c i j * ζ j) - vac D a)) := by
    rw [cv_sub, ← cv_change X.hc, ← hvζ]
    exact (PT.trans X.com1 (PT.of_mem hv)).sub (PT.of_mem (vac_mem X.h₁ a))
  show v ∈ imIntSub (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y))
  rw [e]
  refine add_mem ?_ (hy a hΦ)
  have hbν : ∀ i, Bd D lam (((fun i => ∑ j, c i j * ζ j) - vac D a) i) n (-(n : ℤ)) := by
    intro i
    constructor
    · have h1 : Bd D lam (vac D a i) n 0 := (Bd.nat _).mono (by omega) le_rfl
      have h2 : Bd D lam (∑ j, c i j * ζ j) (n + 0) (0 + 0) :=
        Bd.sum _ fun j _ => (X.bd_c i j).mul (hζ j).bd
      exact ((h2.mono (by omega) (by omega)).sub h1).1
    · have : tKc D lam (((fun i => ∑ j, c i j * ζ j) - vac D a) i) =
          (∑ j, tKc D lam (c i j) * (tKc D lam (ζ j) - ((x' j : ℕ) : ℂ_[p]))) +
            (zcH (a' i) - (((a' i).appr n : ℕ) : ℂ_[p])) := by
        simp only [Pi.sub_apply, vac, map_sub, map_sum, map_mul, map_natCast, ha, ha', mul_sub,
          Finset.sum_sub_distrib, hY]
        ring
      rw [this]
      refine norm_add_le' (norm_sum_le' _ _ (pz_pos _).le fun j _ => ?_) (appr_close _ _)
      rw [norm_mul]
      calc _ ≤ 1 * (p : ℝ) ^ (-(n : ℤ)) :=
            mul_le_mul (X.cb i j) (hx' j) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  exact X.h₁.pairInt' lam
    (fun i j => (((lyc₂ X.id y i).mul (hbν j).cj).mono (by omega) (by omega)).ip) (ly_PT X.h₁ ε y) hPT

theorem fin_eq_of_norm {u v : Fin (p ^ n)} (h : ‖((u : ℕ) : ℂ_[p]) - ((v : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    u = v := by
  have h1 : ((p ^ n : ℤ)) ∣ ((u : ℕ) : ℤ) - ((v : ℕ) : ℤ) := by
    apply dvd_of_normC (p := p)
    push_cast
    exact h
  have hu := u.isLt
  have hv := v.isLt
  have h2 : |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| < (p ^ n : ℤ) := by
    rw [abs_lt]
    have hu' : ((u : ℕ) : ℤ) < (p ^ n : ℤ) := by exact_mod_cast hu
    have hv' : ((v : ℕ) : ℤ) < (p ^ n : ℤ) := by exact_mod_cast hv
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd h1 h2
  exact Fin.ext (by omega)

theorem lift_inj (h₁ : LB D cc δ p La₁ b₁) (hId : IsIdem D lam (2 * n + 2) ε) {y y' : Fin r → Fin (p ^ n)}
    (h : cv D cc δ b₁ (lyc D p n ε y) - cv D cc δ b₁ (lyc D p n ε y') ∈ La₁) : y = y' := by
  rw [← cv_sub] at h
  funext i
  have h1 := (h₁.ipOf lam h i).1
  obtain ⟨-, he, -⟩ := idem_norm D lam (by omega) hId
  apply fin_eq_of_norm
  apply norm_le_pow_of_inv
  have e : tK D lam ((lyc D p n ε y - lyc D p n ε y') i) = tK D lam (ε : D.host.K) *
      (((p : ℂ_[p]) ^ n)⁻¹ * (((y i : ℕ) : ℂ_[p]) - ((y' i : ℕ) : ℂ_[p]))) := by
    simp only [Pi.sub_apply, lyc, map_sub, map_mul, map_inv₀, map_pow, map_natCast]
    ring
  rw [e, norm_mul, he, one_mul] at h1
  exact h1

theorem Ctx.onto (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {q : VC D N N'} (hq : q ∈ La) :
    ∃ y : Fin r → Fin (p ^ n), q - cv D cc δ b₁ (lyc D p n ε y) ∈ La₁ ∧
      cv D cc δ b₁ (lyc D p n ε y) ∈ La := by
  obtain ⟨ζ, hqζ, hζ⟩ := X.h.coord lam hq
  set ξ : Fin r → D.host.K := fun i => ∑ j, c i j * ζ j with hξdef
  have hqξ : q = cv D cc δ b₁ ξ := by rw [hqζ, cv_change X.hc]
  have hξ : ∀ i, Bd D lam (ξ i) n 0 := fun i =>
    (Bd.sum _ fun j _ => (X.bd_c i j).mul (hζ j).bd).mono (by omega) (by omega)
  have hpξ : ∀ i, Ip D lam ((p : D.host.K) ^ n * ξ i) := fun i =>
    (((Bd.ppow n).mul (hξ i)).mono (by omega) (by omega)).ip
  choose y hy using fun i => approxK D lam X.id _ (hpξ i)
  obtain ⟨he1, he, -⟩ := idem_norm D lam (by omega) X.id
  have hp0 : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hρ : ∀ i, Ip D lam ((ξ - lyc D p n ε y) i) := by
    intro i
    constructor
    · apply norm_le_one_of_pow (n := n)
      have e : (p : ℂ_[p]) ^ n * tK D lam ((ξ - lyc D p n ε y) i) =
          (tK D lam ((p : D.host.K) ^ n * ξ i) - ((y i : ℕ) : ℂ_[p])) -
            (tK D lam (ε : D.host.K) - 1) * ((y i : ℕ) : ℂ_[p]) := by
        simp only [Pi.sub_apply, lyc, map_sub, map_mul, map_inv₀, map_pow, map_natCast]
        field_simp
        ring
      rw [e]
      refine norm_sub_le' (hy i) ?_
      rw [norm_mul]
      have hn1 : ‖((y i : ℕ) : ℂ_[p])‖ ≤ 1 := by simpa using normC_int_le_one (p := p) ((y i : ℕ) : ℤ)
      calc _ ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) * 1 :=
            mul_le_mul he1 hn1 (norm_nonneg _) (pz_pos _).le
        _ ≤ _ := by rw [mul_one]; exact pz_mono (by push_cast; omega)
    · exact (((hξ i).sub ((lyc₂ X.id y i).mono le_rfl (by omega))).mono le_rfl le_rfl).2.trans
        (by simp)
  refine ⟨y, ?_, ?_⟩
  · rw [hqξ, ← cv_sub]
    apply X.h₁.memOf' lam hρ
    rw [cv_sub, ← hqξ]
    exact (PT.trans X.com1 (PT.of_mem hq)).sub (ly_PT X.h₁ ε y)
  · have hPT : PT p La (cv D cc δ b₁ (lyc D p n ε y)) := PT.trans X.com2 (ly_PT X.h₁ ε y)
    rw [cv_change X.hd] at hPT ⊢
    apply X.h.memOf' lam _ hPT
    intro j
    constructor
    · have e : ∑ i, d j i * lyc D p n ε y i = ζ j - ∑ i, d j i * (ξ - lyc D p n ε y) i := by
        rw [← X.dc ζ j, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.sub_apply, hξdef]
        ring
      rw [e]
      have h2 : Bd D lam (∑ i, d j i * (ξ - lyc D p n ε y) i) (0 + 0) (n + 0) :=
        Bd.sum _ fun i _ => (X.bd_d j i).mul (hρ i).bd
      exact (((hζ j).bd.mono le_rfl (show (0 : ℤ) ≤ n + 0 by omega)).sub h2).1.trans (by simp)
    · have h2 : Bd D lam (∑ i, d j i * lyc D p n ε y i) (0 + n) (n + -((n : ℤ) + 2)) :=
        Bd.sum _ fun i _ => (X.bd_d j i).mul (lyc₂ X.id y i)
      exact (h2.mono le_rfl (show (n : ℤ) + -((n : ℤ) + 2) ≤ 0 by omega)).2.trans (by simp)

theorem nondeg (h₁ : LB D cc δ p La₁ b₁) (hId : IsIdem D lam (2 * n + 2) ε) {a : Fin r → Fin (p ^ n)}
    (ha : ∀ i, cv D cc δ b₁ (vac D a) ∈ imIntSub (tor0 D cc δ)
      (fK D ((ε : D.host.K) * ((p : D.host.K) ^ n)⁻¹) • ee D cc δ b₁ i)) (i : Fin r) : (a i : ℕ) = 0 := by
  set q : D.host.K := (ε : D.host.K) * ((p : D.host.K) ^ n)⁻¹ with hq
  set χ : Fin r → D.host.K := fun i => cjK D q * vac D a i with hχ
  have hbχ : ∀ i, Bd D lam (χ i) (-((n : ℤ) + 2)) n := fun i =>
    ((bd_q hId).cj.mul (Bd.nat _)).mono (by omega) (by omega)
  have hxe : cv D cc δ b₁ χ = fK D (cjK D q) • cv D cc δ b₁ (vac D a) := cv_smul _ _ _
  have hp0K : (p : D.host.K) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hPT : PT p La₁ (cv D cc δ b₁ χ) := by
    refine ⟨n, ?_⟩
    obtain ⟨ε', hε'⟩ := conj_O D ε
    have hεK : (ε' : D.host.K) = cjK D (ε : D.host.K) := Subtype.ext hε'
    have : ((p : ℂ) ^ n) • cv D cc δ b₁ χ = fK D (ε' : D.host.K) • cv D cc δ b₁ (vac D a) := by
      rw [hxe, smul_smul, hεK, hq, map_mul, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, map_natCast,
        map_natCast]
      congr 1
      have : (p : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      field_simp
    rw [this]
    exact h₁.ok _ _ (vac_mem h₁ a)
  have hmem : cv D cc δ b₁ χ ∈ La₁ := by
    apply h₁.sd
    intro w hw
    obtain ⟨ω, hwω, hω⟩ := h₁.coord lam hw
    choose m hm using fun j => approxK D lam hId (ω j) (hω j)
    have e : w = cv D cc δ b₁ (ω - vac D m) + cv D cc δ b₁ (vac D m) := by
      rw [cv_sub, ← hwω, sub_add_cancel]
    show w ∈ imIntSub (tor0 D cc δ) (cv D cc δ b₁ χ)
    rw [e]
    refine add_mem ?_ ?_
    · have hb : ∀ j, Bd D lam ((ω - vac D m) j) (-(n : ℤ)) 0 := by
        intro j
        refine ⟨?_, ((hω j).bd.sub (Bd.nat _)).2⟩
        simp only [Pi.sub_apply, vac, map_sub, map_natCast]
        exact hm j
      refine h₁.pairInt' lam
        (fun i j => (((hbχ i).mul (hb j).cj).mono (by omega) (by omega)).ip) hPT ?_
      rw [cv_sub, ← hwω]
      exact (PT.of_mem hw).sub (PT.of_mem (vac_mem h₁ m))
    · refine sum_mem fun j _ => ?_
      have e2 : fK D (vac D m j) • ee D cc δ b₁ j = (m j : ℕ) • ee D cc δ b₁ j := by
        rw [← Nat.cast_smul_eq_nsmul ℂ]; simp [vac]
      rw [e2]
      refine nsmul_mem ?_ _
      obtain ⟨k, hk⟩ := ha j
      refine ⟨-k, ?_⟩
      rw [hxe, Hf_smul_left, fK_cjK, ← Hf_smul_right, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IL.Hf_im_swap, hk]
      push_cast; rfl
  have h1 := (h₁.ipOf lam hmem i).2
  obtain ⟨-, he, -⟩ := idem_norm D lam (by omega) hId
  have e : tKc D lam (χ i) = tK D lam (ε : D.host.K) * (((p : ℂ_[p]) ^ n)⁻¹ * ((a i : ℕ) : ℂ_[p])) := by
    simp only [hχ, hq, vac, map_mul, tKc_cjK, map_inv₀, map_pow, map_natCast]
    ring
  rw [e, norm_mul, he, one_mul] at h1
  have h2 := norm_le_pow_of_inv h1
  have h3 : (p ^ n : ℤ) ∣ ((a i : ℕ) : ℤ) := dvd_of_normC (p := p) (by push_cast; exact h2)
  have h4 : p ^ n ∣ (a i : ℕ) := by exact_mod_cast h3
  exact Nat.eq_zero_of_dvd_of_lt h4 (a i).isLt

end Claims

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Exp

def Ex (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

theorem Ex_add (s t : ℝ) : Ex (s + t) = Ex s * Ex t := by
  unfold Ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem Ex_int (k : ℤ) : Ex (k : ℝ) = 1 := by
  unfold Ex
  have : 2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem Ex_sg_int (sg k : ℤ) : Ex ((sg : ℝ) * (k : ℝ)) = 1 := by
  have := Ex_int (sg * k)
  rwa [Int.cast_mul] at this

theorem int_of_sg {sg : ℤ} (hsg : sg = 1 ∨ sg = -1) {t : ℝ} (h : ∃ k : ℤ, (sg : ℝ) * t = k) :
    ∃ k : ℤ, t = k := by
  obtain ⟨k, hk⟩ := h
  rcases hsg with rfl | rfl
  · exact ⟨k, by simpa using hk⟩
  · exact ⟨-k, by push_cast at hk ⊢; linarith⟩

theorem int_of_Ex {t : ℝ} (h : Ex t = 1) : ∃ k : ℤ, t = k := by
  unfold Ex at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (t : ℂ) = (m : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hm]; ring
  exact_mod_cast this

end Exp

section CharSums

variable {N N' : ℕ}
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {p : ℕ} [hp : Fact p.Prime] {lam : Qbar →+* ℂ_[p]}
  {La₁ La : AddSubgroup (VC D N N')} {r : ℕ} {b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
  {c d : Fin r → Fin r → D.host.K} {n : ℕ} {ε : 𝓞 D.host.K} {Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ} {Np : ℕ}

theorem cv_add (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ξ ξ' : Fin r → D.host.K) :
    cv D cc δ b (ξ + ξ') = cv D cc δ b ξ + cv D cc δ b ξ' := by
  simp only [cv, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem Hf_sum_left (T : Tor D) {ι : Type*} (s : Finset ι) (f : ι → VC D N N') (y : VC D N N') :
    Hf D T (∑ i ∈ s, f i) y = ∑ i ∈ s, Hf D T (f i) y := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T y, Hf_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T y (f i)).symm

def PhiR (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ) (a : Fin r → Fin (p ^ n)) : ℂ :=
  Φ (fun i => ((a i : ℕ) : ℤ_[p]))

theorem Ctx.PhiR_cases (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (a : Fin r → Fin (p ^ n)) :
    PhiR Φ a = 1 ∨ PhiR Φ a = 0 := by
  by_cases h : ∃ x : Fin r → ℤ_[p], ∀ i, zcH ((fun i => ((a i : ℕ) : ℤ_[p])) i) =
      ∑ j, tKc D lam (c i j) * zcH (x j)
  · exact Or.inl (X.phi1 _ h)
  · exact Or.inr (X.phi0 _ h)

theorem Ctx.shiftPhi (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {a₀ : Fin r → Fin (p ^ n)}
    (h₀ : PhiR Φ a₀ = 1) (a : Fin r → Fin (p ^ n)) : PhiR Φ (a + a₀) = PhiR Φ a := by
  obtain ⟨x₀, hx₀⟩ := X.of_phi_one h₀
  have h1 : PhiR Φ (a + a₀) = Φ (fun i => ((a i : ℕ) : ℤ_[p]) + ((a₀ i : ℕ) : ℤ_[p])) := by
    apply X.fm
    intro i
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    refine ⟨-((((a i : ℕ) + (a₀ i : ℕ)) / p ^ n : ℕ) : ℤ_[p]), ?_⟩
    have h2 := Nat.mod_add_div ((a i : ℕ) + (a₀ i : ℕ)) (p ^ n)
    have h3 : (((a + a₀) i : Fin (p ^ n)) : ℕ) = ((a i : ℕ) + (a₀ i : ℕ)) % p ^ n := by
      rw [Pi.add_apply, Fin.val_add]
    rw [h3]
    have h4 : (((((a i : ℕ) + (a₀ i : ℕ)) % p ^ n : ℕ) : ℤ_[p])) +
        (p : ℤ_[p]) ^ n * ((((a i : ℕ) + (a₀ i : ℕ)) / p ^ n : ℕ) : ℤ_[p]) =
        ((a i : ℕ) : ℤ_[p]) + ((a₀ i : ℕ) : ℤ_[p]) := by exact_mod_cast h2
    linear_combination h4
  rw [h1]
  by_cases h : ∃ x : Fin r → ℤ_[p], ∀ i, zcH ((fun i => ((a i : ℕ) : ℤ_[p])) i) =
      ∑ j, tKc D lam (c i j) * zcH (x j)
  · obtain ⟨x, hx⟩ := h
    rw [show PhiR Φ a = 1 from X.phi1 _ ⟨x, hx⟩]
    refine X.phi1 _ ⟨x + x₀, fun i => ?_⟩
    have e1 := hx i
    have e2 := hx₀ i
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib] at e1 e2 ⊢
    rw [e1, e2]
  · rw [show PhiR Φ a = 0 from X.phi0 _ h]
    refine X.phi0 _ fun ⟨x, hx⟩ => h ⟨x - x₀, fun i => ?_⟩
    have e1 := hx i
    have e2 := hx₀ i
    simp only [Pi.sub_apply, map_sub, map_add, mul_sub, Finset.sum_sub_distrib] at e1 e2 ⊢
    rw [← e1, ← e2]
    ring

theorem shiftEx (h₁ : LB D cc δ p La₁ b₁) (ε : 𝓞 D.host.K) (sg : ℤ) (y a a₀ : Fin r → Fin (p ^ n)) :
    Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D (a + a₀)))).im) =
      Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D a))).im) *
        Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D a₀))).im) := by
  set x := cv D cc δ b₁ (lyc D p n ε y) with hx
  set t : Fin r → ℕ := fun i => ((a i : ℕ) + (a₀ i : ℕ)) / p ^ n with ht
  have hw : cv D cc δ b₁ (fun j => (t j : D.host.K)) ∈ La₁ := nat_mem h₁ t
  have e : cv D cc δ b₁ (vac D (a + a₀)) + ((p : ℂ) ^ n) • cv D cc δ b₁ (fun j => (t j : D.host.K)) =
      cv D cc δ b₁ (vac D a) + cv D cc δ b₁ (vac D a₀) := by
    have : ((p : ℂ) ^ n) = fK D ((p : D.host.K) ^ n) := by rw [map_pow, map_natCast]
    rw [this, ← cv_smul, ← cv_add, ← cv_add]
    congr 1
    funext i
    have h2 := Nat.mod_add_div ((a i : ℕ) + (a₀ i : ℕ)) (p ^ n)
    have h3 : (((a + a₀) i : Fin (p ^ n)) : ℕ) = ((a i : ℕ) + (a₀ i : ℕ)) % p ^ n := by
      rw [Pi.add_apply, Fin.val_add]
    simp only [Pi.add_apply, vac, ht]
    rw [← Pi.add_apply a a₀ i, h3]
    exact_mod_cast h2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (Hf D (tor0 D cc δ) x
      (((p : ℂ) ^ n) • cv D cc δ b₁ (fun j => (t j : D.host.K)))).im = k := by
    have hmem : ((p : ℂ) ^ n) • x ∈ La₁ := by
      have hp0 : (p : D.host.K) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      have := h₁.cvO (fun j => ε * ((y j : ℕ) : 𝓞 D.host.K))
      have e : (fun j => ((ε * ((y j : ℕ) : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)) =
          fun j => (p : D.host.K) ^ n * lyc D p n ε y j := by
        funext j
        simp only [lyc]
        push_cast
        field_simp
      rw [e, cv_smul, map_pow, map_natCast] at this
      exact this
    obtain ⟨k, hk⟩ := h₁.int _ hmem _ hw
    refine ⟨k, ?_⟩
    rw [← hk, Hf_smul_left, Hf_smul_right, map_pow, Complex.conj_natCast]
  have h5 := congrArg (fun v => (Hf D (tor0 D cc δ) x v).im) e
  simp only [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right, Complex.add_im] at h5
  rw [hk] at h5
  rw [← Ex_add, ← mul_add, ← h5, mul_add, Ex_add, Ex_sg_int, mul_one]

def Ssum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (b₁ : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ) (sg : ℤ) (y : Fin r → Fin (p ^ n)) : ℂ :=
  ∑ a : Fin r → Fin (p ^ n), PhiR Φ a *
    Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D a))).im)

theorem Ctx.S_in (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (sg : ℤ) {y : Fin r → Fin (p ^ n)}
    (hy : cv D cc δ b₁ (lyc D p n ε y) ∈ La) :
    Ssum D cc δ b₁ ε Φ sg y = ∑ a : Fin r → Fin (p ^ n), PhiR Φ a := by
  unfold Ssum
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases X.PhiR_cases a with h | h
  · obtain ⟨k, hk⟩ := X.c1a hy h
    rw [hk, Ex_sg_int, mul_one]
  · rw [h, zero_mul]

theorem Ctx.S_out (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {sg : ℤ} (hsg : sg = 1 ∨ sg = -1)
    {y : Fin r → Fin (p ^ n)} (hy : cv D cc δ b₁ (lyc D p n ε y) ∉ La) : Ssum D cc δ b₁ ε Φ sg y = 0 := by
  have hex : ∃ a₀ : Fin r → Fin (p ^ n), PhiR Φ a₀ = 1 ∧
      Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D a₀))).im) ≠ 1 := by
    by_contra hne
    push Not at hne
    exact hy (X.c1b fun a ha => int_of_sg hsg (int_of_Ex (hne a ha)))
  obtain ⟨a₀, h₀, hE⟩ := hex
  have hS : Ssum D cc δ b₁ ε Φ sg y =
      Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D a₀))).im) *
        Ssum D cc δ b₁ ε Φ sg y := by
    conv_lhs => unfold Ssum
    rw [← Equiv.sum_comp (Equiv.addRight a₀)]
    unfold Ssum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_addRight]
    rw [X.shiftPhi h₀, shiftEx X.h₁]
    ring
  have : (1 - Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y))
      (cv D cc δ b₁ (vac D a₀))).im)) * Ssum D cc δ b₁ ε Φ sg y = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hE
  · exact h

theorem sum_y (h₁ : LB D cc δ p La₁ b₁) (hId : IsIdem D lam (2 * n + 2) ε) {sg : ℤ} (hsg : sg = 1 ∨ sg = -1)
    (a : Fin r → Fin (p ^ n)) :
    ∑ y : Fin r → Fin (p ^ n),
      Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D a))).im) =
      if a = 0 then ((p : ℂ) ^ (n * r)) else 0 := by
  set q : D.host.K := (ε : D.host.K) * ((p : D.host.K) ^ n)⁻¹ with hq
  set v := cv D cc δ b₁ (vac D a) with hv
  set t : Fin r → ℝ := fun i => (sg : ℝ) * (Hf D (tor0 D cc δ) (fK D q • ee D cc δ b₁ i) v).im with ht
  have hterm : ∀ y : Fin r → Fin (p ^ n),
      Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) v).im) =
      ∏ i, Complex.exp (2 * Real.pi * Complex.I * (((y i : ℕ) : ℂ) * ((t i : ℝ) : ℂ))) := by
    intro y
    have e : (sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) v).im =
        ∑ i, ((y i : ℕ) : ℝ) * t i := by
      unfold cv
      rw [Hf_sum_left, Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [lyc, ht]
      rw [← hq, mul_comm q, map_mul, mul_smul, Hf_smul_left, map_natCast, im_natCast_mul]
      ring
    rw [e, ← Complex.exp_sum]
    unfold Ex
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i (j : Fin (p ^ n)) => Complex.exp (2 * Real.pi * Complex.I *
    (((j : ℕ) : ℂ) * ((t i : ℝ) : ℂ))))]
  split_ifs with ha
  · have ht0 : ∀ i, t i = 0 := by
      intro i
      simp only [ht, hv, ha]
      have : cv D cc δ b₁ (vac D (0 : Fin r → Fin (p ^ n))) = 0 := by
        simp [cv, vac]
      rw [this, Hf_zero_right]; simp
    simp only [ht0]
    simp [Finset.prod_const, ← pow_mul]
  · have hne : ¬ ∀ i, ∃ k : ℤ, t i = k := by
      intro hall
      apply ha
      funext i
      exact Fin.ext (by simpa using nondeg h₁ hId (a := a) (fun i => int_of_sg hsg (hall i)) i)
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hmem : ((p : ℂ) ^ n) • (fK D q • ee D cc δ b₁ i) ∈ La₁ := by
      have hp0 : (p : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      rw [smul_smul, hq, map_mul, map_inv₀, map_pow, map_natCast, mul_comm, mul_assoc,
        inv_mul_cancel₀ hp0, mul_one]
      exact h₁.ok ε _ (h₁.mem i)
    obtain ⟨k, hk⟩ := h₁.int _ hmem _ (vac_mem h₁ a)
    rw [Hf_smul_left, im_natCast_pow_mul] at hk
    refine geom_zero p n _ (sg * k) ?_ hi
    simp only [ht]
    push_cast
    rw [← hk]
    ring

theorem Ctx.count (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {sg : ℤ} (hsg : sg = 1 ∨ sg = -1) :
    ∑ y : Fin r → Fin (p ^ n), Ssum D cc δ b₁ ε Φ sg y = (p : ℂ) ^ (n * r) := by
  unfold Ssum
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_y X.h₁ X.id hsg]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have : PhiR Φ (0 : Fin r → Fin (p ^ n)) = 1 := X.phi1 _ ⟨0, by intro i; simp⟩
  rw [this, one_mul]

end CharSums

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Final

theorem final_alg {G : Type*} [Fintype G] (P : G → Prop) [DecidablePred P] (S F : G → ℂ) (m Q : ℂ)
    (hQ : Q ≠ 0) (h1 : ∀ y, P y → S y = m) (h0 : ∀ y, ¬ P y → S y = 0) (hs : ∑ y, S y = Q) :
    ((Real.sqrt ((Finset.univ.filter P).card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ y ∈ Finset.univ.filter P, F y =
      ((Real.sqrt ((Finset.univ.filter P).card : ℝ) : ℝ) : ℂ) * (Q⁻¹ * ∑ y, S y * F y) := by
  set k : ℕ := (Finset.univ.filter P).card with hk
  have e1 : ∑ y, S y * F y = m * ∑ y ∈ Finset.univ.filter P, F y := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with h
    · rw [h1 y h]
    · rw [h0 y h, zero_mul]
  have e2 : (k : ℂ) * m = Q := by
    rw [← hs, hk, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with h
    · rw [h1 y h]
    · rw [h0 y h]
  have hk0 : (k : ℂ) ≠ 0 := fun h => hQ (by rw [← e2, h, zero_mul])
  have hm0 : m ≠ 0 := fun h => hQ (by rw [← e2, h, mul_zero])
  have hss : ((Real.sqrt (k : ℝ) : ℝ) : ℂ) * ((Real.sqrt (k : ℝ) : ℝ) : ℂ) = (k : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg k)]; simp
  have hs0 : ((Real.sqrt (k : ℝ) : ℝ) : ℂ) ≠ 0 := fun h => hk0 (by rw [← hss, h, zero_mul])
  rw [e1, ← e2, ← hss]
  field_simp

variable {N N' : ℕ}
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {p : ℕ} [hp : Fact p.Prime] {lam : Qbar →+* ℂ_[p]}
  {La₁ La : AddSubgroup (VC D N N')} {r : ℕ} {b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
  {c d : Fin r → Fin r → D.host.K} {n : ℕ} {ε : 𝓞 D.host.K} {Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ} {Np : ℕ}

theorem Ctx.main (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {sg : ℤ} (hsg : sg = 1 ∨ sg = -1)
    (hS : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.SemiChar (tor0 D cc δ) La) {th : VC D N N' → ℂ}
    (hth : th ∈ ThSp D (tor0 D cc δ) La₁)
    (hW : ∀ x ∈ La, wPh D (tor0 D cc δ) p x = al D (tor0 D cc δ) x) (z : VC D N N') :
    Iop D (tor0 D cc δ) La₁ La th z =
      ((Real.sqrt ((La₁.addSubgroupOf La).index : ℝ) : ℝ) : ℂ) * (((p : ℂ) ^ (n * r))⁻¹ *
        ∑ a : Fin r → Fin (p ^ n), PhiR Φ a * ∑ y : Fin r → Fin (p ^ n),
          Ex ((sg : ℝ) * (Hf D (tor0 D cc δ) (cv D cc δ b₁ (lyc D p n ε y)) (cv D cc δ b₁ (vac D a))).im) *
            Wop D (tor0 D cc δ) p (cv D cc δ b₁ (lyc D p n ε y)) th z) := by
  classical
  set P : (Fin r → Fin (p ^ n)) → Prop := fun y => cv D cc δ b₁ (lyc D p n ε y) ∈ La with hP
  let f : {y // P y} → La ⧸ La₁.addSubgroupOf La := fun y =>
    ((⟨cv D cc δ b₁ (lyc D p n ε y.1), y.2⟩ : La) : La ⧸ La₁.addSubgroupOf La)
  have hbij : Function.Bijective f := by
    constructor
    · intro y y' hyy
      simp only [f] at hyy
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hyy
      apply Subtype.ext
      symm
      apply lift_inj X.h₁ X.id
      have : cv D cc δ b₁ (lyc D p n ε y'.1) - cv D cc δ b₁ (lyc D p n ε y.1) =
          -cv D cc δ b₁ (lyc D p n ε y.1) + cv D cc δ b₁ (lyc D p n ε y'.1) := by abel
      rw [this]
      exact hyy
    · intro q
      induction q using QuotientAddGroup.induction_on with | H v => ?_
      obtain ⟨y, hy1, hy2⟩ := X.onto v.2
      refine ⟨⟨y, hy2⟩, ?_⟩
      simp only [f]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have : (v : VC D N N') - cv D cc δ b₁ (lyc D p n ε y) =
          -cv D cc δ b₁ (lyc D p n ε y) + (v : VC D N N') := by abel
      rw [this] at hy1
      exact hy1
  have hidx : (La₁.addSubgroupOf La).index = (Finset.univ.filter P).card := by
    unfold AddSubgroup.index
    rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum : ∑ᶠ q : La ⧸ La₁.addSubgroupOf La,
      al D (tor0 D cc δ) ((Quotient.out q : La) : VC D N N') *
        U D (tor0 D cc δ) ((Quotient.out q : La) : VC D N N') th z =
      ∑ y ∈ Finset.univ.filter P, Wop D (tor0 D cc δ) p (cv D cc δ b₁ (lyc D p n ε y)) th z := by
    rw [← finsum_eq_of_bijective (f := fun y : {y // P y} =>
      Wop D (tor0 D cc δ) p (cv D cc δ b₁ (lyc D p n ε y.1)) th z) f hbij (fun y => by
        simp only [f]
        rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.term_out (tor0 D cc δ) hS hth]
        unfold Wop
        rw [hW _ y.2]), finsum_eq_sum_of_fintype]
    exact (Finset.sum_subtype (Finset.univ.filter P) (by simp)
      (fun y => Wop D (tor0 D cc δ) p (cv D cc δ b₁ (lyc D p n ε y)) th z)).symm
  have hp0 : (p : ℂ) ^ (n * r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hfin := final_alg P (Ssum D cc δ b₁ ε Φ sg)
    (fun y => Wop D (tor0 D cc δ) p (cv D cc δ b₁ (lyc D p n ε y)) th z)
    (∑ a : Fin r → Fin (p ^ n), PhiR Φ a) ((p : ℂ) ^ (n * r)) hp0 (fun y hy => X.S_in sg hy)
    (fun y hy => X.S_out hsg hy) (X.count hsg)
  unfold Iop
  rw [hsum, hidx]
  refine Eq.trans ?_ (hfin.trans ?_)
  · rfl
  · congr 2
    unfold Ssum
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    ring

end Final

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP Formalism.L2.PairingIndexBounds.Xf.XiMoveP

end Formalism.L2.PairingIndexBounds.Xf
