import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEleventh

open NumberField Module Matrix Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd

open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration hermitianFormColumns vectorCountBounds

theorem limUnder_of_step {u : ℕ → ℕ} {q e k₀ : ℕ} (hq : 0 < q)
    (h : ∀ k, k₀ ≤ k → u (k + 1) = q ^ e * u k) {k : ℕ} (hk : k₀ ≤ k) :
    limUnder atTop (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) = (u k : ℝ) / (q : ℝ) ^ (k * e) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hstep : ∀ j, k₀ ≤ j → (u (j + 1) : ℝ) / (q : ℝ) ^ ((j + 1) * e) =
      (u j : ℝ) / (q : ℝ) ^ (j * e) := by
    intro j hj
    rw [h j hj, Nat.cast_mul, Nat.cast_pow, div_eq_div_iff (pow_ne_zero _ hq') (pow_ne_zero _ hq'),
      add_mul, one_mul, pow_add]
    ring
  have hconst : ∀ j, k₀ ≤ j → (u j : ℝ) / (q : ℝ) ^ (j * e) = (u k₀ : ℝ) / (q : ℝ) ^ (k₀ * e) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [hstep j hj, ih]
  have ht : Tendsto (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) atTop
      (𝓝 ((u k : ℝ) / (q : ℝ) ^ (k * e))) := by
    rw [hconst k hk]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with j hj
    exact (hconst j hj).symm
  exact ht.limUnder_eq

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem nkCount_succ_fine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} {v : ℕ} (hn : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    (hk : vd h L 𝔭 + v + 1 ≤ k) :
    nkCount h L 𝔭 (k + 1) n = Ideal.absNorm 𝔭 ^ (2 * finrank K V - 1) * nkCount h L 𝔭 k n := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  change nkM 𝔭 (k + 1) H n = _ * nkM 𝔭 k H n
  rw [hv] at hk
  have key := nkM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hn hk
  rw [Fintype.card_fin] at key
  have hN := absNorm_pos h𝔭
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hpos
  · have e0 : 2 * finrank K V = 0 := by omega
    have e1 : 2 * finrank K V - 1 = 0 := by omega
    rw [e0, pow_zero, one_mul] at key
    rw [e1, pow_zero, one_mul]
    have h2 := two_le_absNorm h𝔭
    have hB : nkM 𝔭 k H n ≤ 1 :=
      (card_sub_le hK h𝔭 k _).trans (by rw [Fintype.card_fin, e0, mul_zero, pow_zero])
    have hAN : 2 * nkM 𝔭 (k + 1) H n ≤ nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ h2
    have hA0 : nkM 𝔭 (k + 1) H n = 0 := by
      rw [key] at hAN
      omega
    rw [hA0, zero_mul] at key
    omega
  · have e : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
    rw [e, pow_succ] at key
    apply Nat.eq_of_mul_eq_mul_right hN
    rw [key]
    ring

theorem alphaN_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} {v : ℕ} (hn : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    (hk : vd h L 𝔭 + v + 1 ≤ k) :
    alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  unfold alphaN
  exact limUnder_of_step (absNorm_pos h𝔭)
    (fun j hj => nkCount_succ_fine hK hF hs hd hL hLi h𝔭 hn hj) hk

theorem nkCount_congr (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} {k : ℕ} (hc : n - n' ∈ 𝔭 ^ k) :
    nkCount h L 𝔭 k n = nkCount h L 𝔭 k n' := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  have e : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n) = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n') := by
    rw [Ideal.Quotient.eq, ← map_sub]
    exact (mem_pow_iff 𝔭 k _).mpr hc
  rw [e]

theorem akCount_succ_fine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 1 ≤ k) :
    akCount h L 𝔭 (k + 1) = Ideal.absNorm 𝔭 ^ (finrank K V ^ 2) * akCount h L 𝔭 k := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [akCount_eq h h𝔭 b hb hH, akCount_eq h h𝔭 b hb hH]
  rw [hv] at hk
  have key := akM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hk
  rw [Fintype.card_fin, ← sq] at key
  exact key

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 1 ≤ k) :
    alphaL h L 𝔭 = (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  unfold alphaL
  exact limUnder_of_step (absNorm_pos h𝔭)
    (fun j hj => akCount_succ_fine hK hF hs hd hL hLi h𝔭 (le_trans hk hj)) le_rfl

theorem akCount_pos (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : 0 < akCount h L 𝔭 k := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [akCount_eq h h𝔭 b hb hH]
  haveI := finite_quot (K := K) h𝔭 k
  haveI : Nonempty {X : Matrix (Fin (finrank K V)) (Fin (finrank K V)) (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} :=
    ⟨⟨1, by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]⟩⟩
  exact Nat.card_pos

theorem nkCount_le_nat (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) :
    nkCount h L 𝔭 k n ≤ 2 * Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭 + 1) *
      Ideal.absNorm 𝔭 ^ (k * (2 * finrank K V - 1)) := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, hv]
  have key := nkM_le hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) (by rw [Fintype.card_fin]; exact hm) k n
  rw [Fintype.card_fin] at key
  exact key

end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
