import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartNakayamaGen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem homog_unique {p : MRingOver S ι} {a b : K → ℕ} (ha : IsMultiHomog p a) (hb : IsMultiHomog p b)
    (h0 : p ≠ 0) : a = b := by
  obtain ⟨μ, hμ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp h0)
  funext k
  exact (ha μ hμ k).symm.trans (hb μ hμ k)

theorem chartMon_ne_zero [Nontrivial S] (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ≠ 0 := by
  have h : chartMon (S := S) c e = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (e k)) 1 := by
    rw [MvPolynomial.monomial_sum_one, chartMon]
    exact Finset.prod_congr rfl fun k _ => MvPolynomial.X_pow_eq_monomial
  rw [h, Ne, MvPolynomial.monomial_eq_zero]
  exact one_ne_zero

theorem chartMon_one_pow (c : ∀ k, ι k) (n : ℕ) :
    chartMon (S := S) c (fun _ => 1) ^ n = chartMon c (fun _ => n) := by
  simp only [chartMon, pow_one, ← Finset.prod_pow]

theorem smul_mk_cancel' {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    (w : MRingOver S ι) (y : M) {s : MRingOver S ι} (hs : s ∈ T) :
    (w * s) • LocalizedModule.mk y (⟨s, hs⟩ : T) = LocalizedModule.mk (w • y) 1 :=
  smul_mk_cancel w y ⟨s, hs⟩

theorem exists_kill_of_res_eq_zero {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (c c' : ∀ k, ι k)
    (w : LocalizedModule (KH.cellMon S (chart c').1) M)
    (hw : KH.cellRes S M (chart c').1 (fun k => ({c k, c' k} : Finset (ι k))) w = 0) :
    ∃ e : ℕ, chartMon (S := S) c (fun _ => e) • w = 0 := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have hsub : ∀ k, (chart c').1 k ⊆ ({c k, c' k} : Finset (ι k)) := fun k => by simp [chart]
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono hsub)] at hw
    obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.mp
      (hw.trans (LocalizedModule.zero_mk (1 : KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k))))).symm)
    simp only [one_smul, smul_zero] at hv
    obtain ⟨e, w', hw'⟩ := dvd_of_mem_pair v.2
    have hz : (chartMon (S := S) c (fun _ => e) * chartMon c' (fun _ => e)) • m = 0 := by
      rw [hw', mul_comm, mul_smul, ← Submonoid.smul_def, hv, smul_zero]
    refine ⟨e, ?_⟩
    rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨chartMon c' (fun _ => e), chartMon_mem c' _⟩, ?_⟩
    show chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • chartMon (S := S) c (fun _ => e) • m =
      chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • (0 : M)
    rw [smul_zero, smul_zero, smul_comm (chartMon c' (fun _ => e)) (s : MRingOver S ι),
      smul_smul (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)) m,
      mul_comm (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)), hz, smul_zero]

theorem genNear_of_chart [Nontrivial S] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {d : K → ℤ} (h𝓜 : KH.IsMGraded S ι 𝓜)
    (c : ∀ k, ι k) {f₀ : MRingOver S ι} {δ₀ : K → ℕ} (hf₀ : IsMultiHomog f₀ δ₀)
    (hloc : ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ)
        (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
        t ∈ KH.cellMon S (chart c).1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) (a + δ₀)) ∧
        (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f₀ * t) • x = ∑ j, p j • z j (chart c)) :
    GenNear S ι 𝓜 d (f₀ * chartMon c (fun _ => 1)) (δ₀ + fun _ => 1) := by
  intro J
  obtain ⟨c', rfl⟩ : ∃ c', J = chart c' := ⟨_, eq_chart J⟩
  intro x hx
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx

  have hy : LocalizedModule.mk m (⟨chartMon c a, chartMon_mem c a⟩ : KH.cellMon S (chart c).1) ∈
      KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d :=
    GenSESStep.mk_mem_locPart _ _ a (isMultiHomog_chartMon c a) hm
  obtain ⟨t₁, a₁, r, p, z, ht₁T, ht₁, hp, hz, he⟩ := hloc _ hy
  obtain ⟨α₁, rfl⟩ := exists_chartMon ht₁T
  obtain rfl : a₁ = α₁ := homog_unique ht₁ (isMultiHomog_chartMon c α₁) (chartMon_ne_zero c α₁)

  set U : ∀ k, Finset (ι k) := fun k => {c k, c' k} with hU
  have hsub : ∀ k, (chart c).1 k ⊆ U k := fun k => by simp [chart, hU]
  have hsub' : ∀ k, (chart c').1 k ⊆ U k := fun k => by simp [chart, hU]
  have hle := GenTwistGenerated.cellMon_mono (S := S) hsub
  have hle' := GenTwistGenerated.cellMon_mono (S := S) hsub'
  have hagree : ∀ j, KH.cellRes S M (chart c').1 U (z j (chart c')) =
      KH.cellRes S M (chart c).1 U (z j (chart c)) := fun j =>
    (res_agree (z j) (LinearMap.mem_ker.mp (hz j).2) c c' U (fun k => by simp [hU])
      (fun k => by simp [hU])).symm
  have hD : KH.cellRes S M (chart c').1 U ((f₀ * chartMon c a₁ * (t : MRingOver S ι)) • LocalizedModule.mk m t -
      ∑ j, (chartMon c a * p j) • z j (chart c')) = 0 := by
    have h2 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
        LocalizedModule.mk ((f₀ * chartMon c a₁) • m) 1 := by
      have e1 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
          chartMon (S := S) c a • KH.cellRes S M (chart c).1 U (∑ j, p j • z j (chart c)) := by
        rw [map_sum, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hagree j, map_smul, mul_smul]
      rw [e1, ← he, map_smul, GenTwistGenerated.cellRes_mk hle, smul_smul,
        mul_comm (chartMon (S := S) c a) (f₀ * chartMon c a₁)]
      exact smul_mk_cancel' _ _ _
    rw [map_sub, h2, map_smul, GenTwistGenerated.cellRes_mk hle', sub_eq_zero]
    exact smul_mk_cancel' _ _ _
  obtain ⟨e, he0⟩ := exists_kill_of_res_eq_zero c c' _ hD
  rw [smul_sub, sub_eq_zero] at he0

  set E : ℕ := ∑ k, a₁ k with hE
  have haE : ∀ k, a₁ k ≤ E := fun k =>
    Finset.single_le_sum (f := a₁) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hexp : (fun _ : K => e + E + 1) = (fun _ => 1) + (fun k => E - a₁ k) + (fun _ => e) + a₁ := by
    funext k
    simp only [Pi.add_apply]
    have := haE k
    omega
  have hring : (f₀ * chartMon c (fun _ => 1)) ^ (e + E + 1) * (t : MRingOver S ι) =
      (f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k)) *
        (chartMon c (fun _ => e) * (f₀ * chartMon c a₁ * (t : MRingOver S ι))) := by
    rw [mul_pow, chartMon_one_pow, hexp, chartMon_add, chartMon_add, chartMon_add]
    ring
  refine ⟨e + E + 1, t, a, r, fun j => f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k) *
    chartMon c (fun _ => e) * chartMon c a * p j, z, t.2, ht, fun j => ?_, hz, ?_⟩
  · have h := GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul
      (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (isMultiHomog_pow hf₀ (e + E))
        (isMultiHomog_chartMon c (fun _ => 1))) (isMultiHomog_chartMon c (fun k => E - a₁ k)))
        (isMultiHomog_chartMon c (fun _ => e))) (isMultiHomog_chartMon c a)) (hp j)
    convert h using 1
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := haE k
    zify [this] at *
    ring
  · rw [hring, mul_smul, mul_smul (chartMon (S := S) c (fun _ => e)), he0, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    simp only [smul_smul]
    congr 1
    ring

end ChartNakayamaGen

theorem ChartNakayamaGen.proof : ChartNakayamaGen.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d hS hM h𝓜 hP _ I hI hgen
  obtain ⟨c, rfl⟩ : ∃ c, I = ChartNakayamaGen.chart c := ⟨_, ChartNakayamaGen.eq_chart I⟩
  have h1 : (1 : S) ≠ 0 := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by
    have e : (1 : MRingOver S ι) = 0 := by rw [← C_1, h, C_0]
    rw [e]
    exact P.zero_mem))
  have : Nontrivial S := nontrivial_of_ne 1 0 h1
  have hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P := fun k => hI k (c k) (Finset.mem_singleton_self _)
  obtain ⟨f₀, δ₀, hf₀, hf₀P, hloc⟩ := ChartNakayamaGen.chart_nakayama hS hM h𝓜 hP c hc hgen
  refine ⟨f₀ * ChartNakayamaGen.chartMon c (fun _ => 1), δ₀ + fun _ => 1,
    GenSESStep.isMultiHomog_mul hf₀ (ChartNakayamaGen.isMultiHomog_chartMon c _), fun h => ?_,
    ChartNakayamaGen.genNear_of_chart h𝓜 c hf₀ hloc⟩
  rcases hP.mem_or_mem h with h | h
  · exact hf₀P h
  · exact ChartNakayamaGen.cellMon_notMem hP hc (ChartNakayamaGen.chartMon_mem c _) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
