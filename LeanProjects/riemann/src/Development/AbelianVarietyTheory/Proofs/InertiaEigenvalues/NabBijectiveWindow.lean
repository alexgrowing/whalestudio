import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

noncomputable section
namespace GlobalTheory.PhiGam.Window
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem bij_of_gmult_zero {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] (x : k) (h : gmult T P Q x = 0) :
    (∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q) ∧ ∀ y ∈ P, ∃ p ∈ P, y - (T p - x • p) ∈ Q := by
  have hinj : ∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q := by
    intro p hp hq
    unfold gmult at h
    set P' := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hP'
    have hker : LinearMap.ker (Q.mkQ ∘ₗ P'.subtype) = Q.submoduleOf P' := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
    have hle : LinearMap.range (Q.mkQ ∘ₗ P'.subtype) ≤ P.map Q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact Submodule.map_mono inf_le_left
    haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P'.subtype)) :=
      Submodule.finiteDimensional_of_le hle
    haveI : FiniteDimensional k (↥P' ⧸ Q.submoduleOf P') := by
      rw [← hker]
      exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm
    have hsub : Subsingleton (↥P' ⧸ Q.submoduleOf P') := Module.finrank_zero_iff.mp h
    have hmem : p ∈ P' := by
      refine ⟨hp, ?_⟩
      refine Submodule.mem_iSup_of_mem 1 ?_
      simpa [Module.algebraMap_end_apply] using hq
    have : (Submodule.Quotient.mk (⟨p, hmem⟩ : P') : ↥P' ⧸ Q.submoduleOf P') = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero (Q.submoduleOf P')).mp this
  refine ⟨hinj, ?_⟩
  let S : U →ₗ[k] U := T - x • LinearMap.id
  have hS : ∀ p, S p = T p - x • p := fun p => rfl
  have hSQ : Q ≤ Q.comap S := fun p hp => by
    rw [Submodule.mem_comap, hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, P.sub_mem (hP p hp) (P.smul_mem _ hp), rfl⟩
  have hi : Function.Injective (Sq.restrict hSq) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, p, hp, rfl⟩ hz
    have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
    have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
  have hs := LinearMap.injective_iff_surjective.mp hi
  intro y hy
  obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
  have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
  exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩

variable {k : Type} [Field k]

theorem vv_coe : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by
  simp [vv]

theorem vv_ne_zero : vv k ≠ 0 := by
  simp [vv]

theorem gam_zpow {l : ℕ} (R : RingPG k l) (b : ℤ) :
    ∃ c : k⟦X⟧, R.γ (vv k ^ b) = vv k ^ b * (1 - (b : k⸨X⸩) * vv k + (c : k⸨X⸩) * vv k ^ 2) := by
  obtain ⟨κ, hκ, hγ⟩ := R.γ_v
  obtain ⟨c0, hc0⟩ : (PowerSeries.X : k⟦X⟧) ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ]
  have hκ' : κ = 1 + PowerSeries.X * c0 := by rw [← hc0]; ring
  have hu : IsUnit (1 - κ * PowerSeries.X : k⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  obtain ⟨w', hw'⟩ := hu.exists_right_inv
  let ι : k⟦X⟧ →+* k⸨X⸩ := HahnSeries.ofPowerSeries ℤ k
  have hι : ∀ c : k⟦X⟧, (c : k⸨X⸩) = ι c := fun _ => rfl
  have hv : vv k = ι PowerSeries.X := vv_coe
  set w : k⸨X⸩ := 1 - (κ : k⸨X⸩) * vv k with hw
  have hw1 : w = 1 - vv k - ι c0 * vv k ^ 2 := by
    rw [hw, hι, hκ', hv]; simp only [map_add, map_mul, map_one]; ring
  have hww : w * ι w' = 1 := by
    have := congrArg ι hw'
    simp only [map_mul, map_sub, map_one] at this
    rw [hw, hv, hι]; exact this
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  have hinv : w⁻¹ = ι w' := (eq_inv_of_mul_eq_one_right hww).symm
  have key : ∃ c : k⟦X⟧, w ^ b = 1 - (b : k⸨X⸩) * vv k + ι c * vv k ^ 2 := by
    induction b using Int.induction_on with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(n : k⟦X⟧) - c0 + (n : k⟦X⟧) * c0 * PowerSeries.X + c * (1 - PowerSeries.X - c0 * PowerSeries.X ^ 2), ?_⟩
      rw [zpow_add_one₀ hw0, hc, hw1]
      simp only [map_add, map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      ring
    | pred n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨w' * (c + ((n : k⟦X⟧) + 1) + c0 + ((n : k⟦X⟧) + 1) * c0 * PowerSeries.X), ?_⟩
      rw [zpow_sub_one₀ hw0, hc, hinv]
      simp only [map_add, map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      rw [hw1] at hww
      linear_combination (1 + ((n : k⸨X⸩) + 1) * vv k) * hww
  obtain ⟨c, hc⟩ := key
  exact ⟨c, by rw [map_zpow₀, hγ, mul_zpow, hc]⟩

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem mem_sh_iff {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ ∃ n ∈ N, vv k ^ a • n = x := Iff.rfl

theorem coe_smul_eq (c : k⟦X⟧) (x : V) : (c : k⸨X⸩) • x = c • x :=
  algebraMap_smul k⸨X⸩ c x

theorem v_smul_mem {N : Submodule k⟦X⟧ V} {n : V} (hn : n ∈ N) : vv k • n ∈ N := by
  rw [vv_coe, coe_smul_eq]; exact N.smul_mem _ hn

theorem sh_succ_le (a : ℤ) (N : Submodule k⟦X⟧ V) : sh (a + 1) N ≤ sh a N := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_sh_iff.mpr ⟨vv k • n, v_smul_mem hn, ?_⟩
  show _ = vv k ^ (a + 1) • n
  rw [smul_smul, zpow_add_one₀ vv_ne_zero]

theorem sh_add_le (a : ℤ) (m : ℕ) (N : Submodule k⟦X⟧ V) : sh (a + m) N ≤ sh a N := by
  induction m with
  | zero => simp
  | succ m ih =>
    refine le_trans ?_ ih
    rw [Nat.cast_succ, ← add_assoc]; exact sh_succ_le _ _

theorem nab_eq (g : V →ₗ[k] V) (x : V) : nab g x = (vv k)⁻¹ • (g x - x) := rfl

theorem nab_mem {g : V →ₗ[k] V} {N : Submodule k⟦X⟧ V} (hC : CondC g N) {n : V} (hn : n ∈ N) :
    nab g n ∈ N := by
  obtain ⟨n', hn', h⟩ := mem_sh_iff.mp (hC n hn)
  rw [nab_eq, ← h, smul_smul, zpow_one, inv_mul_cancel₀ vv_ne_zero, one_smul]; exact hn'

theorem shift_identity {K W : Type} [Field K] [AddCommGroup W] [Module K W] {v : K} (hv : v ≠ 0)
    (u b c : K) (n t : W) :
    v⁻¹ • ((u * (1 - b * v + c * v ^ 2)) • (n + v • t) - u • n) =
      u • (t - b • n + v • (c • (n + v • t) - b • t)) := by
  match_scalars <;> field_simp <;> ring

theorem nab_shift {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {n : V} (hn : n ∈ N) :
    ∃ n' ∈ N, nab g (vv k ^ b • n) = vv k ^ b • (nab g n - (b : k) • n + vv k • n') := by
  obtain ⟨c, hc⟩ := gam_zpow R b
  have hv : vv k ≠ 0 := vv_ne_zero
  have hgn : g n = n + vv k • nab g n := by
    rw [nab_eq, smul_smul, mul_inv_cancel₀ hv, one_smul]; abel
  have hm := nab_mem hC hn
  refine ⟨c • (n + vv k • nab g n) - b • nab g n,
    N.sub_mem (N.smul_mem _ (N.add_mem hn (v_smul_mem hm))) (zsmul_mem hm _), ?_⟩
  rw [nab_eq g (vv k ^ b • n), hg, hc, hgn, Int.cast_smul_eq_zsmul, ← coe_smul_eq,
    ← Int.cast_smul_eq_zsmul k⸨X⸩ b n, ← Int.cast_smul_eq_zsmul k⸨X⸩ b (nab g n)]
  exact shift_identity hv _ _ _ _ _

theorem nab_mem_sh {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {x : V} (hx : x ∈ sh b N) : nab g x ∈ sh b N := by
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
  obtain ⟨n', hn', h⟩ := nab_shift R hg hC b hn
  refine mem_sh_iff.mpr ⟨_, ?_, h.symm⟩
  exact N.add_mem (N.sub_mem (nab_mem hC hn) ((N.restrictScalars k).smul_mem _ hn)) (v_smul_mem hn')

theorem finite_quot {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    FiniteDimensional k ((N.restrictScalars k).map ((sh 1 N).restrictScalars k).mkQ) := by
  obtain ⟨s, hs⟩ := hN
  set Q := (sh 1 N).restrictScalars k with hQ
  have hle : (N.restrictScalars k).map Q.mkQ ≤ Submodule.span k (Q.mkQ '' (s : Set V)) := by
    rintro _ ⟨n, hn, rfl⟩
    have hn' : n ∈ Submodule.span k⟦X⟧ (s : Set V) := by rw [hs]; exact hn
    clear hn
    induction hn' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x hx ih =>
      have hxN : x ∈ N := by rw [← hs]; exact hx
      obtain ⟨c', hc'⟩ : (PowerSeries.X : k⟦X⟧) ∣ c - algebraMap k k⟦X⟧ (PowerSeries.constantCoeff c) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have : Q.mkQ (c • x) = PowerSeries.constantCoeff c • Q.mkQ x := by
        rw [← map_smul]
        refine (Submodule.Quotient.eq _).mpr ?_
        refine mem_sh_iff.mpr ⟨c' • x, N.smul_mem _ hxN, ?_⟩
        rw [zpow_one, vv_coe, coe_smul_eq, smul_smul, ← hc', sub_smul, algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ ih
  haveI : FiniteDimensional k (Submodule.span k (Q.mkQ '' (s : Set V))) :=
    FiniteDimensional.span_of_finite k (s.finite_toSet.image _)
  exact Submodule.finiteDimensional_of_le hle

theorem graded {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (h : sen g N (b : k) = 0) :
    (∀ x ∈ sh b N, nab g x ∈ sh (b + 1) N → x ∈ sh (b + 1) N) ∧
      ∀ y ∈ sh b N, ∃ x ∈ sh b N, y - nab g x ∈ sh (b + 1) N := by
  haveI := finite_quot hN
  obtain ⟨h1, h2⟩ := bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => nab_mem hC hp) (fun p hp => nab_mem_sh R hg hC 1 hp) (b : k) h
  have hv : vv k ≠ 0 := vv_ne_zero
  constructor
  · intro x hx hx'
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hn
    obtain ⟨t, ht, e'⟩ := mem_sh_iff.mp hx'
    rw [e, zpow_add_one₀ hv, mul_smul] at e'
    have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
    have : n ∈ sh 1 N := h1 n hn (mem_sh_iff.mpr ⟨t - n', N.sub_mem ht hn', by
      rw [zpow_one, smul_sub, e2]; abel⟩)
    obtain ⟨r, hr, rfl⟩ := mem_sh_iff.mp this
    exact mem_sh_iff.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hy
    obtain ⟨p, hp, hq⟩ := h2 n hn
    obtain ⟨r, hr, e'⟩ := mem_sh_iff.mp hq
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hp
    refine ⟨vv k ^ b • p, mem_sh_iff.mpr ⟨p, hp, rfl⟩, mem_sh_iff.mpr ⟨r - n', N.sub_mem hr hn', ?_⟩⟩
    rw [zpow_one] at e'
    rw [e, zpow_add_one₀ hv, mul_smul, ← smul_sub, smul_sub (vv k), e']
    congr 1; abel

theorem nab_bijective_window : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ), (∀ j : ℕ, j < m → sen g N ((a + j : ℤ) : k) = 0) → (∀ x ∈ sh a N, nab g x ∈ sh (a + m) N → x ∈ sh (a + m) N) ∧ ∀ y ∈ sh a N, ∃ x ∈ sh a N, y - nab g x ∈ sh (a + m) N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m
  induction m with
  | zero =>
    intro _
    refine ⟨fun x hx _ => by simpa using hx, fun y hy => ⟨0, Submodule.zero_mem _, by simpa using hy⟩⟩
  | succ m ih =>
    intro h
    obtain ⟨i1, i2⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    obtain ⟨g1, g2⟩ := graded R hg hN.1 hC (a + m) (h m (Nat.lt_succ_self m))
    rw [Nat.cast_succ, ← add_assoc]
    refine ⟨fun x hx hx' => g1 x (i1 x hx (sh_succ_le _ _ hx')) hx', fun y hy => ?_⟩
    obtain ⟨x, hx, hx'⟩ := i2 y hy
    obtain ⟨z, hz, hz'⟩ := g2 _ hx'
    refine ⟨x + z, Submodule.add_mem _ hx (sh_add_le a m N hz), ?_⟩
    rw [map_add, ← sub_sub]; exact hz'

end GlobalTheory.PhiGam.Window
