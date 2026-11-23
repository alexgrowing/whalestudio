import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeVdLeOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySeventh
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinF

open idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

omit [FiniteDimensional K V] in
theorem exists_norm_int (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {y : V} (hy : y ∈ L) :
    ∃ a : 𝓞 F, h y y = algebraMap (𝓞 K) K (ι a) := by
  obtain ⟨z, hz⟩ := (Submodule.mem_one).1 (hLi y hy y hy)
  have hzc : conjO K z = z := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [WA.algebraMap_conjO, hz, Cell.form_self_star hs y]
  obtain ⟨a, ha⟩ := (conjO_eq_iff_mem_range hF z).1 hzc
  exact ⟨a, by rw [ha, hz]⟩

theorem newton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {N : ℕ} (hN : 1 ≤ N) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ N) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (N + 1) ∧
      y' - y ∈ (extP K 𝔭 ^ N • L : Submodule (𝓞 K) V) := by
  obtain ⟨c, hc⟩ := traceDeterminantCongruences.exists_trace_one hK hF h𝔭 1
  have hc' : c + conjO K c - 1 ∈ extP K 𝔭 ^ 1 := hc
  rw [pow_one] at hc'
  have hEm : ι (a - 1) ∈ extP K 𝔭 ^ N := localizedQuotients.ι_mem_pow ha1
  have hEc : conjO K (ι (a - 1)) = ι (a - 1) := idealPowerSpanBounds.conjO_map hF (a - 1)
  obtain ⟨ν, hν⟩ : ∃ ν : 𝓞 F, ι ν = conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
    have : conjO K (conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c)) =
        conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
      rw [map_mul, WA.conjO_conjO, mul_comm]
    exact (conjO_eq_iff_mem_range hF _).1 this
  have ha' : ι a = 1 + ι (a - 1) := by rw [map_sub, map_one]; ring
  refine ⟨(1 - ι (a - 1) * c) • y, L.smul_mem _ hy, ν * a, ?_, ?_, ?_⟩
  · rw [← algebraMap_smul K (1 - ι (a - 1) * c) y]
    simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply]
    rw [ha, map_mul, hν, map_mul, map_mul, WA.algebraMap_conjO]
    ring
  · rw [← idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 (N + 1) (ν * a - 1)]
    have key : ι (ν * a - 1) = ι (a - 1) * (-(c + conjO K c - 1)) +
        ι (a - 1) * ι (a - 1) * (conjO K c * c - (c + conjO K c) + ι (a - 1) * conjO K c * c) := by
      rw [map_sub (algebraMap (𝓞 F) (𝓞 K)) (ν * a) 1, map_mul, hν, ha', map_one, map_sub, map_one,
        map_mul, hEc]
      ring
    rw [key]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ]
      exact Ideal.mul_mem_mul hEm ((Ideal.neg_mem_iff _).2 hc')
    · refine Ideal.mul_mem_right _ _ ?_
      refine Ideal.pow_le_pow_right (by omega : N + 1 ≤ N + N) ?_
      rw [pow_add]
      exact Ideal.mul_mem_mul hEm hEm
  · have : (1 - ι (a - 1) * c) • y - y = (-(ι (a - 1) * c)) • y := by
      rw [sub_smul, one_smul, neg_smul]; abel
    rw [this]
    exact Submodule.smul_mem_smul ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hEm)) hy

theorem newton_iter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ k) (j : ℕ) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (k + j) ∧
      y' - y ∈ (extP K 𝔭 ^ k • L : Submodule (𝓞 K) V) := by
  induction j with
  | zero => exact ⟨y, hy, a, ha, by simpa using ha1, by simp⟩
  | succ j ih =>
    obtain ⟨y1, hy1, a1, hh1, h1, hd1⟩ := ih
    obtain ⟨y2, hy2, a2, hh2, h2, hd2⟩ := newton hK hF h𝔭 (by omega : 1 ≤ k + j) hy1 hh1 h1
    refine ⟨y2, hy2, a2, hh2, by simpa only [add_assoc] using h2, ?_⟩
    have : y2 - y = (y2 - y1) + (y1 - y) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hd2) hd1

theorem exists_exact_lift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} (h1 : h x₀ x₀ = 1) {k : ℕ} (hk : 1 ≤ k) {y : V} (hy : y ∈ L)
    (hyy : CongrP 𝔭 k (h y y) 1) :
    ∃ z ∈ locF 𝔭 L, h z z = 1 ∧ z - y ∈ (extP K 𝔭 ^ k • locF 𝔭 L : Submodule (𝓞 K) V) := by
  haveI := h𝔭.isPrime
  obtain ⟨a, ha⟩ := exists_norm_int hF hs hLi hy
  have hI0 : WCA.InI 𝔭 k (algebraMap (𝓞 K) K (ι (a - 1))) := by
    have := Cell.congrP_iff_inI.1 hyy
    rwa [ha, ← map_one (algebraMap (𝓞 K) K), ← map_sub, ← map_one (algebraMap (𝓞 F) (𝓞 K)),
      ← map_sub] at this
  have ha1 : a - 1 ∈ 𝔭 ^ k := (Cell.inI_ι h𝔭).1 hI0
  obtain ⟨v, hv⟩ := Cell.exists_near h𝔭 hF hs hL hLi (n := 1) one_ne_zero
    ⟨x₀, by rw [h1, map_one, map_one]⟩
  obtain ⟨y', hy', a', ha', ha1', hd'⟩ := newton_iter hK hF h𝔭 hk hy ha ha1 v
  have hI : WCA.InI 𝔭 (v + k) (h y' y' - algebraMap (𝓞 K) K (ι 1)) := by
    rw [ha', ← map_sub, ← map_sub]
    exact (Cell.inI_ι h𝔭).2 (by rw [add_comm]; exact ha1')
  obtain ⟨z, hz0, hz1, hzd⟩ :=
    hv k hk y' ((WCA.inL_zero_iff h𝔭.isPrime).2 (localizedQuotients.le_locF 𝔭 L hy')) hI
  refine ⟨z, (WCA.inL_zero_iff h𝔭.isPrime).1 hz0, by rw [hz1, map_one, map_one], ?_⟩
  have : z - y = (z - y') + (y' - y) := by abel
  rw [this]
  exact Submodule.add_mem _ (WCA.InL.mem h𝔭.isPrime hzd)
    (Submodule.smul_mono le_rfl (localizedQuotients.le_locF 𝔭 L) hd')

end Formalism.HermitianLattices.Ext.L3.PinF
