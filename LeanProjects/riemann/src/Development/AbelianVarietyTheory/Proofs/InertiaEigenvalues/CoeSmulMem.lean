import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubIdBijOfContracting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Gauge
section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem _root_.GlobalTheory.PhiGam.Gauge.phi_sh {l : ℕ} (R : _root_.GlobalTheory.PhiGam.RingPG k l)
    (f : V →ₗ[k] V) (hf : _root_.GlobalTheory.PhiGam.Semi R.φ f)
    (N N' : Submodule k⟦X⟧ V) (w : ℤ)
    (h : _root_.GlobalTheory.PhiGam.pull f N' ≤ _root_.GlobalTheory.PhiGam.sh (-w) N) (m : ℕ) {x : V}
    (hx : x ∈ _root_.GlobalTheory.PhiGam.sh m N') :
    f x ∈ _root_.GlobalTheory.PhiGam.sh (l * m - w) N := by
  obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := R.φ_v
  have hfy : f y ∈ _root_.GlobalTheory.PhiGam.sh (-w) N := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, hz'⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hfy
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_exists]
  refine ⟨((u : k⟦X⟧) ^ m) • z, N.smul_mem _ hz, ?_⟩
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [zpow_natCast, hf, map_pow, hu, ← hz', ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) ^ m) z, smul_smul,
    smul_smul, LaurentSeries.coe_algebraMap, map_pow, sub_eq_add_neg, zpow_add₀ hX, mul_pow, ← pow_mul]
  congr 1
  rw [show ((l : ℤ) * (m : ℤ)) = ((l * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  ring

end

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem vv_smul_mem_sh_succ_iff (a : ℤ) (N : Submodule k⟦X⟧ V) (y : V) :
    _root_.GlobalTheory.PhiGam.vv k • y ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) N ↔
      y ∈ _root_.GlobalTheory.PhiGam.sh a N := by
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, _root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, smul_smul, ← zpow_add_one₀ hX]
  rw [show -(a + 1) + 1 = -a by ring]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem apply_sub_self_eq_vv_smul_nab (f : V →ₗ[k] V) (x : V) :
    f x - x = _root_.GlobalTheory.PhiGam.vv k • _root_.GlobalTheory.PhiGam.nab f x := by
  rw [_root_.GlobalTheory.PhiGam.nab_apply_eq, smul_smul, mul_inv_cancel₀ (_root_.GlobalTheory.PhiGam.vv_ne_zero k),
    one_smul]

open scoped LaurentSeries PowerSeries in

theorem _root_.GlobalTheory.PhiGam.Gauge.main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l]
    (R : _root_.GlobalTheory.PhiGam.RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    [FiniteDimensional k⸨X⸩ V] (D : _root_.GlobalTheory.PhiGam.ModPG R n V), ∀ (w w' : ZMod n → ℤ) (s : ZMod n → ℕ)
    (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, _root_.GlobalTheory.PhiGam.IsLat (N i)) →
    _root_.GlobalTheory.PhiGam.CondAB D.φ w w' N →
    (∀ i, _root_.GlobalTheory.PhiGam.CondC (D.γ i) (N i)) →
    (∀ i, (s i : ℤ) + 1 ≤ l * (s (i - 1) + 1) - w i) →
    (∀ i (a : ℕ), a ≤ s i + 1 → _root_.GlobalTheory.PhiGam.sen (D.γ i) (N i) (a : k) = 0) →
    ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i =
      D.φ i (g (i - 1)) - g i) →
    (∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh 1 (N i)) →
    (∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧
      ∀ i, g i - (D.γ i (m i) - m i) ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) ∧
    ((∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) → (∀ i, b i ∈ N i) →
      ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧
        g i = D.γ i (m i) - m i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D w w' s N hN hAB hC hs hsen b g hcoc hg
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  have hl : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hW : ∀ i, _ := fun i => _root_.GlobalTheory.PhiGam.Window.nab_bijective_window R (D.γ i)
    (D.γ_semi i) (N i) (hN i) (hC i) 0 (s i + 2) (fun j hj => by
      simpa using hsen i j (by omega))
  refine ⟨?_, fun hg3 hb => ?_⟩
  · have key : ∀ i, ∃ x ∈ N i, g i - (D.γ i x - x) ∈
        _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i) := by
      intro i
      have hy : (_root_.GlobalTheory.PhiGam.vv k)⁻¹ • g i ∈ _root_.GlobalTheory.PhiGam.sh 0 (N i) := by
        rw [← vv_smul_mem_sh_succ_iff, smul_inv_smul₀ hX]
        simpa using hg i
      obtain ⟨x, hx, hxy⟩ := (hW i).2 _ hy
      refine ⟨x, by rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at hx, ?_⟩
      have h3 := (vv_smul_mem_sh_succ_iff _ _ _).2 hxy
      rw [smul_sub, smul_inv_smul₀ hX, ← apply_sub_self_eq_vv_smul_nab] at h3
      convert h3 using 2
      push_cast
      ring
    choose m hm1 hm2 using key
    exact ⟨m, hm1, hm2⟩
  · set φ := D.φ
    set γ := D.γ
    have hφ : ∀ i (a : ℕ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N (i - 1)) →
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh (l * a - w i) (N i) := fun i a x hx =>
      _root_.GlobalTheory.PhiGam.Gauge.phi_sh R (φ i) (D.φ_semi i) (N i)
        (N (i - 1)) (w i) (hAB i).1 a hx
    have hγ : ∀ i (a : ℤ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N i) →
        γ i x - x ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) (N i) := fun i a x hx => by
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff]
      exact _root_.GlobalTheory.PhiGam.Window.nab_mem_sh R (D.γ_semi i) (hC i) a hx
    have hb' : ∀ i, b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i) := by
      intro i
      have h1 : γ i (b i) - b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2 + 1) (N i) := by
        rw [hcoc i]
        refine sub_mem ?_ (by convert hg3 i using 2; ring)
        have h2 := hφ i (s (i - 1) + 3) (by push_cast; exact hg3 (i - 1))
        refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ h2
        have := hs i
        push_cast
        nlinarith
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff] at h1
      have := (hW i).1 (b i) (by rw [_root_.GlobalTheory.PhiGam.sh_zero_eq]; exact hb i) (by convert h1 using 2; push_cast; ring)
      convert this using 2
      push_cast
      ring
    have hP : ∀ i, ∀ x ∈ _root_.GlobalTheory.PhiGam.sh ((s (i - 1) : ℤ) + 2) (N (i - 1)),
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh 1
          (_root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) := by
      intro i x hx
      rw [_root_.GlobalTheory.PhiGam.sh_sh_eq]
      refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ (hφ i (s (i - 1) + 2) (by push_cast; exact hx))
      have := hs i
      push_cast
      nlinarith
    have hF := _root_.GlobalTheory.PhiGam.one_sub_frob_bij R D
      (fun i => _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) (fun i => (hN i).shift _) hP
    obtain ⟨m, hmP, hmb⟩ := hF.1 b hb'
    change ∀ i, φ i (m (i - 1)) - m i = b i at hmb
    have hg0 := hF.2 (fun i => g i - (γ i (m i) - m i))
      (fun i => sub_mem (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hg3 i))
        (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hγ i _ (hmP i))))
      (fun i => by
        show φ i (g (i - 1) - (γ (i - 1) (m (i - 1)) - m (i - 1))) = g i - (γ i (m i) - m i)
        have e := hcoc i
        rw [← hmb i, map_sub] at e
        have e2 := sub_eq_iff_eq_add.1 e.symm
        have hcomm : ∀ x, φ i (γ (i - 1) x) = γ i (φ i x) := D.comm i
        simp only [map_sub, hcomm]
        rw [e2]
        abel)
    refine ⟨m, fun i => ?_, fun i => ⟨(hmb i).symm, ?_⟩⟩
    · have := _root_.GlobalTheory.PhiGam.sh_le_sh_of_le (show (0 : ℤ) ≤ (s i : ℤ) + 2 by positivity) _ (hmP i)
      rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at this
    · exact sub_eq_zero.1 (congrFun hg0 i)

end GlobalTheory.PhiGam.Gauge
