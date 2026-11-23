import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSingSSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanEqProd

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Step

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V V' : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem alphaStd_succ (𝔭 : Ideal (𝓞 F)) {m : ℕ} (hm : 1 ≤ m) :
    alphaStd K 𝔭 m = alphaStd K 𝔭 (m - 1) * A5.eFac K m 𝔭 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold alphaStd A5.eFac
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem factor_identity (q aS e aL aN : ℝ) (m a b : ℕ) (hm : 1 ≤ m) (hq : q ≠ 0) (he : e ≠ 0)
    (hL : aL ≠ 0) :
    q ^ ((m - 1) * (a + b)) * aS * aN / aL =
      (q ^ a) ^ (m - 1) * (aS * e * q ^ (m * b) / aL) * (q ^ b)⁻¹ * (aN / e) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

theorem tprod_localPsi_eq (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hn : h S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * lamG F h L * (normD h L)⁻¹ *
        singS F h L n := by
  classical
  set U : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hL hLi).toFinset ∪ (A5.finite_primes_of_mem hn0).toFinset
    with hU
  have hU1 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vd h L 𝔭.1 = 0 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset] at h𝔭
    exact not_not.mp h𝔭.1
  have hU2 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → n ∉ 𝔭.1 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at h𝔭
    exact h𝔭.2
  have hU3 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vF 𝔭.1 n = 0 := by
    intro 𝔭 h𝔭
    by_contra hne
    have := (A5.mem_pow_iff_le_vF 𝔭.2 hn0 1).mpr (Nat.one_le_iff_ne_zero.mpr hne)
    rw [pow_one] at this
    exact hU2 𝔭 h𝔭 this
  have hpt : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      ((Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n) ^ (finrank K V - 1) * lamP h L 𝔭.1 *
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1)⁻¹ *
        (alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))) := by
    intro 𝔭
    rw [hLI K F hK hF V V' h h' S L 𝔭.1 n hs hd 𝔭.2 hn0 hn hL hLi]
    unfold lamP
    rw [alphaStd_succ 𝔭.1 hm]
    have hq : (Ideal.absNorm 𝔭.1 : ℝ) ≠ 0 := by
      have := A5.two_le_absNorm 𝔭.2
      positivity
    exact factor_identity _ _ _ _ _ _ _ _ hm hq (A5.eFac_pos 𝔭.2 hm).ne'
      (alphaL_pos hK hF hs hd hL hLi 𝔭.2).ne'
  have e1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) =
      ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
    rw [absNorm_span_eq_prod n hn0]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU3 𝔭 h𝔭, pow_zero]
  have e2 : lamG F h L = ∏ 𝔭 ∈ U, lamP h L 𝔭.1 := by
    unfold lamG
    exact tprod_eq_prod fun 𝔭 h𝔭 => localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2 (hU1 𝔭 h𝔭)
  have e3 : normD h L = ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
    rw [normD_eq_prod hK hF hs hd hL hLi]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU1 𝔭 h𝔭, pow_zero]
  have h4 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U →
      alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) = 1 := by
    intro 𝔭 h𝔭
    rw [alphaN_of_vd_zero_unit hK hF hs hd hL hLi 𝔭.2 (hU1 𝔭 h𝔭) hm (hU2 𝔭 h𝔭)]
    exact div_self (A5.eFac_pos 𝔭.2 hm).ne'
  have e4 : singS F h L n = ∏ 𝔭 ∈ U, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) := by
    unfold singS
    exact tprod_eq_prod h4
  have e0 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 = ∏ 𝔭 ∈ U, psiP S L 𝔭.1 := by
    refine tprod_eq_prod fun 𝔭 h𝔭 => ?_
    rw [hpt 𝔭, hU3 𝔭 h𝔭, hU1 𝔭 h𝔭, h4 𝔭 h𝔭, localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2 (hU1 𝔭 h𝔭)]
    simp
  rw [e0, e1, e2, e3, e4, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun 𝔭 _ => hpt 𝔭

theorem repMass_eq (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    repMass h L (algebraMap F K (n : F)) = c * lamG F h L * (normD h L)⁻¹ *
      ((Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n) := by
  have hn0 : n ≠ 0 := A5.ne_zero_of_mem_boxSet hn
  obtain ⟨x₀, hx₀⟩ := exists_vec_of_hermRep hH hK hs hd hm (algebraMap F K (n : F))
    ((hF _).mpr ⟨_, rfl⟩) (fun φ => (hn φ).1)
  have hne : h x₀ x₀ ≠ 0 := by
    rw [hx₀]
    intro e
    apply hn0
    apply RingOfIntegers.ext
    exact (algebraMap F K).injective (by rw [e]; simp)
  have h1 := repMass_eq_prod_psi (F := F) hK hF hs hd (vecSplitPerp h hne) hL hLi hc
  have h2 := tprod_localPsi_eq hLI hK hF hs hd (vecSplitPerp h hne) hL hLi (by omega) hn0 hx₀
  rw [h2] at h1
  have h3 : h (vecSplitPerp h hne).x₀ (vecSplitPerp h hne).x₀ = algebraMap F K (n : F) := hx₀
  rw [h3] at h1
  rw [h1]
  ring

end Formalism.HermitianLattices.Ext.L3.Step
