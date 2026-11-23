import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubIdBijOfContracting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

private theorem coe_powerSeries_smul_eq_smul {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := by
  rw [← algebraMap_smul (k⸨X⸩) a x, LaurentSeries.coe_algebraMap]

private theorem powerSeries_smul_mem_of_mem {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (N : Submodule k⟦X⟧ V) {x : V} (hx : x ∈ N)
    (a : k⟦X⟧) : (a : k⸨X⸩) • x ∈ N := by
  rw [coe_powerSeries_smul_eq_smul]; exact N.smul_mem a hx

private theorem mem_of_gmult_eq_zero_of_sub_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U]
    (T : Module.End k U) (P Q : Submodule k U) (x : k) (s : Set U) (hs : s.Finite)
    (hP : P ≤ Submodule.span k s ⊔ Q) (h0 : gmult T P Q x = 0) (y : U) (hy : y ∈ P)
    (hT : (T - algebraMap k (Module.End k U) x) y ∈ Q) : y ∈ Q := by
  set E : Submodule k U := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hE
  have hyE : y ∈ E := by
    refine Submodule.mem_inf.mpr ⟨hy, Submodule.mem_iSup_of_mem 1 ?_⟩
    rw [Submodule.mem_comap, pow_one]; exact hT
  let f : E →ₗ[k] U ⧸ Q := Q.mkQ ∘ₗ E.subtype
  let W : Submodule k (U ⧸ Q) := (Submodule.span k s).map Q.mkQ
  have hWfg : W.FG := (Submodule.fg_span hs).map _
  have : Module.Finite k W := Module.Finite.iff_fg.mpr hWfg
  have hrange : ∀ z : E, f z ∈ W := by
    intro z
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (hP z.2.1)
    refine ⟨a, ha, ?_⟩
    show Q.mkQ a = Q.mkQ (z : U)
    have hc0 : Q.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hc
    rw [← hac, map_add, hc0, add_zero]
  have hker : LinearMap.ker f = Q.submoduleOf E := by
    ext z
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap]
  have hker' : LinearMap.ker (f.codRestrict W hrange) = Q.submoduleOf E := by
    rw [LinearMap.ker_codRestrict, hker]
  let g := (Q.submoduleOf E).liftQ (f.codRestrict W hrange) hker'.ge
  have hg : LinearMap.ker g = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ hker'.le
  have : IsNoetherian k W := IsNoetherian.iff_fg.mpr inferInstance
  have : Module.Finite k (E ⧸ Q.submoduleOf E) := Module.Finite.of_injective g (LinearMap.ker_eq_bot.mp hg)
  have hq : Module.finrank k (E ⧸ Q.submoduleOf E) = 0 := h0
  have := Module.finrank_zero_iff.mp hq
  have h1 : (Submodule.Quotient.mk (⟨y, hyE⟩ : E) : E ⧸ Q.submoduleOf E) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1

private theorem exists_finite_span_sup_shift_of_isLat {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (N : Submodule k⟦X⟧ V) (hN : IsLat N) :
    ∃ s : Set V, s.Finite ∧ N.restrictScalars k ≤ Submodule.span k s ⊔ (sh 1 N).restrictScalars k := by
  obtain ⟨t, ht⟩ := hN.1
  refine ⟨↑t, t.finite_toSet, ?_⟩
  intro x hx
  rw [Submodule.restrictScalars_mem, ← ht] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_sup_left (Submodule.subset_span hy)
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y hy0 hy =>
    have hyN : y ∈ N := by rw [ht] at hy0; exact hy0
    obtain ⟨a', ha'⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
      rw [PowerSeries.X_dvd_iff]; simp
    have hsplit : a = PowerSeries.C (PowerSeries.constantCoeff a) + PowerSeries.X * a' := by
      rw [← ha']; ring
    rw [hsplit, add_smul, mul_smul]
    refine add_mem ?_ (Submodule.mem_sup_right ?_)
    · have hc : (PowerSeries.C (PowerSeries.constantCoeff a) : k⟦X⟧) • y = (PowerSeries.constantCoeff a) • y := by
        rw [← algebraMap_smul (k⟦X⟧) (PowerSeries.constantCoeff a) y]; rfl
      rw [hc]; exact Submodule.smul_mem _ _ hy
    · rw [Submodule.restrictScalars_mem, mem_sh_iff_exists]
      exact ⟨a' • y, N.smul_mem a' hyN, by rw [zpow_one, vv_eq_coe_X, coe_powerSeries_smul_eq_smul]⟩

private theorem vv_pow_smul_mem_of_sen_eq_zero {k : Type} [Field k] {l : ℕ} (R : RingPG k l) {V : Type} [AddCommGroup V]
    [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V) (hN : IsLat N)
    (s : ℕ) (hsen : sen g N (-((s + 1 : ℕ) : k)) = 0) (b : V) (hb : vv k ^ (s + 1) • b ∈ N)
    (hw : g b - b ∈ sh 1 N) : vv k ^ s • b ∈ N := by
  have hv : vv k ≠ 0 := vv_ne_zero k
  obtain ⟨κ, hκ0, hκ⟩ := R.γ_v
  obtain ⟨κ₁, hκ₁⟩ : PowerSeries.X ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ0]
  have hE : ∀ t : ℕ, ∃ e : k⟦X⟧,
      (1 - κ * PowerSeries.X) ^ t - 1 + (t : k⟦X⟧) * PowerSeries.X = PowerSeries.X ^ 2 * e := by
    intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | succ t ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c * (1 - κ * PowerSeries.X) - κ₁ + (t : k⟦X⟧) * κ, ?_⟩
      push_cast
      linear_combination (1 - κ * PowerSeries.X) * hc - PowerSeries.X * hκ₁
  obtain ⟨e, he⟩ := hE (s + 1)
  have he' : (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) - 1 + ((s + 1 : ℕ) : k⸨X⸩) * vv k
      = vv k ^ 2 * (e : k⸨X⸩) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ k) he
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_natCast] at h
    rw [← vv_eq_coe_X] at h
    exact h
  have hw' : (vv k)⁻¹ • (g b - b) ∈ N := by
    have h := (mem_sh_iff_smul_mem (a := 1)).mp hw
    rwa [zpow_neg_one] at h
  have hgy : g (vv k ^ (s + 1) • b) = (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1) • g b := by
    rw [show g (vv k ^ (s + 1) • b) = R.γ (vv k ^ (s + 1)) • g b from hg _ _, map_pow, hκ]
  have hz : nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b) ∈ sh 1 N := by
    rw [mem_sh_iff_smul_mem]
    have hid : vv k ^ (-(1 : ℤ)) • (nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b))
        = (e : k⸨X⸩) • (vv k ^ (s + 1) • b) + (((1 - κ * PowerSeries.X) ^ (s + 1) * PowerSeries.X ^ s : k⟦X⟧) : k⸨X⸩) • ((vv k)⁻¹ • (g b - b)) := by
      rw [nab_apply_eq, hgy, Nat.cast_smul_eq_nsmul k, ← Nat.cast_smul_eq_nsmul k⸨X⸩]
      simp only [map_mul, map_pow, map_sub, map_one]
      rw [← vv_eq_coe_X, zpow_neg_one]
      have hvi : vv k * (vv k)⁻¹ = 1 := mul_inv_cancel₀ hv
      set vi := (vv k)⁻¹
      generalize ((s + 1 : ℕ) : k⸨X⸩) = c' at he' ⊢
      generalize (e : k⸨X⸩) = E at he' ⊢
      have hA : vi * (vi * (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1))
          = (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        rw [mul_pow]
        linear_combination (vi * (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s) * hvi
      have hB : E * vv k ^ (s + 1) = -(vi * (vi * vv k ^ (s + 1))) + vi * (c' * vv k ^ (s + 1))
          + (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        linear_combination (-(vv k ^ s * vi)) * he' - (E * vv k ^ (s + 1) - vi * vv k ^ s) * hvi
      simp only [smul_add, smul_sub, smul_smul]
      rw [hA, hB]
      simp only [add_smul, neg_smul]
      abel
    rw [hid]
    exact add_mem (powerSeries_smul_mem_of_mem N hb _) (powerSeries_smul_mem_of_mem N hw' _)
  have hkey : vv k ^ (s + 1) • b ∈ sh 1 N := by
    obtain ⟨t, ht, hsp⟩ := exists_finite_span_sup_shift_of_isLat N hN
    exact mem_of_gmult_eq_zero_of_sub_mem (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
      (-((s + 1 : ℕ) : k)) t ht hsp hsen _ hb (by
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply, neg_smul, sub_neg_eq_add]; exact hz)
  have h := (mem_sh_iff_smul_mem (a := 1)).mp hkey
  rw [smul_smul, zpow_neg_one, pow_succ', inv_mul_cancel_left₀ hv] at h
  exact h

theorem cocycle_split_of_contracting : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (N : ZMod n → Submodule k⟦X⟧ V) (J : ZMod n → ℕ), (∀ i, IsLat (N i)) → (∀ i, CondC (D.γ i) (N i)) → (∀ i, pull (D.φ i) (N (i - 1)) ≤ sh 1 (N i)) → (∀ i (j : ℕ), 1 ≤ j → j ≤ J i → sen (D.γ i) (N i) (-(j : k)) = 0) → ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i) → (∀ i, g i ∈ sh 1 (N i)) → (∀ i, b i ∈ sh (-(J i)) (N i)) → ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧ g i = D.γ i (m i) - m i := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D N J hlat hC hφ hsen b g hcoc hg hb
  have hsub : ∀ i, sh 1 (N i) ≤ N i := by
    intro i
    have h := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) (N i)
    rwa [sh_zero_eq] at h
  have hφ' : ∀ i, ∀ x ∈ N (i - 1), D.φ i x ∈ sh 1 (N i) := fun i x hx =>
    hφ i (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hw : ∀ i, D.γ i (b i) - b i ∈ sh 1 (N i) := by
    intro i
    rw [hcoc i]
    exact sub_mem (hφ' i _ (hsub (i - 1) (hg (i - 1)))) (hg i)
  have hbN : ∀ i, b i ∈ N i := by
    intro i
    have key : ∀ d, d ≤ J i → vv k ^ (J i - d) • b i ∈ N i := by
      intro d
      induction d with
      | zero => intro _; simpa using (mem_sh_iff_smul_mem).mp (hb i)
      | succ d ih =>
        intro hd
        have e : J i - d = (J i - (d + 1)) + 1 := by omega
        have h1 := ih (by omega)
        rw [e] at h1
        have h2 := hsen i (J i - d) (by omega) (by omega)
        rw [e] at h2
        exact vv_pow_smul_mem_of_sen_eq_zero R (D.γ i) (D.γ_semi i) (N i) (hlat i) _ h2 (b i) h1 (hw i)
    simpa using key (J i) le_rfl
  obtain ⟨m, hmN, hm⟩ := (one_sub_frob_bij R D N hlat hφ').1 b hbN
  have hhN : ∀ i, D.γ i (m i) - m i - g i ∈ N i := fun i =>
    sub_mem (hsub i (hC i (m i) (hmN i))) (hsub i (hg i))
  have hhφ : ∀ i, D.φ i (D.γ (i - 1) (m (i - 1)) - m (i - 1) - g (i - 1)) = D.γ i (m i) - m i - g i := by
    intro i
    have e1 : D.φ i (m (i - 1)) = b i + m i := by rw [← hm i]; abel
    have e2 : D.φ i (g (i - 1)) = D.γ i (b i) - b i + g i := by rw [hcoc i]; abel
    rw [map_sub, map_sub, D.comm, e1, e2, map_add]
    abel
  have h0 := (one_sub_frob_bij R D N hlat hφ').2 (fun i => D.γ i (m i) - m i - g i) hhN hhφ
  refine ⟨m, hmN, fun i => ⟨(hm i).symm, ?_⟩⟩
  have h3 := congrFun h0 i
  simp only [Pi.zero_apply] at h3
  exact (sub_eq_zero.mp h3).symm

end GlobalTheory.PhiGam
