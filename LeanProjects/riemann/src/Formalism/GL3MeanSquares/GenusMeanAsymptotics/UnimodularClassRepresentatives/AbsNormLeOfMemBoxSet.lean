import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumBoxIdeal
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaNOfVdZeroUnit
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LValEtaEqLValEtaF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinitePrimesOfMem

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem boxSet_finite (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => algebraMap F K (n : F)) ?_
    (fun a _ b _ hab => RingOfIntegers.ext ((algebraMap F K).injective hab))
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ T).subset ?_
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨map_isIntegral_int (algebraMap F K) (RingOfIntegers.isIntegral_coe n), fun φ => ?_⟩
  have hst : star (algebraMap F K (n : F)) = algebraMap F K (n : F) := (hF _).mpr ⟨_, rfl⟩
  have hc := hK.2.1 φ (algebraMap F K (n : F))
  rw [hst] at hc
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hc.symm
  have h1 := hn φ
  simp only at h1 ⊢
  rw [hr] at h1 ⊢
  rw [Complex.ofReal_re] at h1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1.1]
  exact h1.2

theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  have := (hn φ).1
  simp at this

theorem absNorm_le_of_mem_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  by_contra hlt
  have := box_inter_eq_empty hK hF (b := Ideal.span {n}) (not_le.mp hlt)
  have hmem : n ∈ {n' : 𝓞 F | n' ∈ boxSet K F T ∧ n' ∈ Ideal.span {n}} :=
    ⟨hn, Ideal.mem_span_singleton_self n⟩
  rw [this] at hmem
  exact hmem

def eFac (K : Type) {F : Type} [Field K] [Field F] [NumberField F] [Algebra F K] (m : ℕ)
    (𝔭 : Ideal (𝓞 F)) : ℝ :=
  1 - etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ))

theorem eFac_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : 1 ≤ m) : 0 < eFac K m 𝔭 := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast two_le_absNorm h𝔭
  have h1 := IdealNormInequalities.zpow_neg_lt_one hq hm
  have h0 : 0 ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := zpow_nonneg (by linarith) _
  have hη : |etaF K F 𝔭 ^ m| = 1 := by
    rw [abs_pow]
    unfold etaF
    split_ifs <;> simp
  have h2 : etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) ≤
      (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := by
    calc _ ≤ |etaF K F 𝔭 ^ m| * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ = _ := by rw [hη, one_mul]
  unfold eFac
  linarith

theorem alphaN_eq_stage (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    ∃ k : ℕ, alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  set k0 := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2
  refine ⟨k0, ?_⟩
  refine Tendsto.limUnder_eq (tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_)
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih, nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk]
    generalize 2 * finrank K V - 1 = r
    rw [add_mul, one_mul, pow_add]
    push_cast
    field_simp

theorem alphaN_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 → 0 ≤ alphaN h L 𝔭 n ∧ alphaN h L 𝔭 n ≤ C := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := alphaN_eq_stage hK hF hs hd hL hLi h𝔭 hn
  rw [hk]
  exact ⟨by positivity, (div_le_iff₀ (by positivity)).mpr (hC k n)⟩

end Formalism.HermitianLattices.Ext.L3.A5
