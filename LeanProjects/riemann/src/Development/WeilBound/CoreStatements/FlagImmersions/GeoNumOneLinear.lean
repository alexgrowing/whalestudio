import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersProjectionFormulaDegree

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter.PointVertical

theorem image_dim_le_one {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {F : Type} [Field F]
    {V : Ideal (MRingOver F ι')} (hV : IsProjVarF V 1) {e : ℕ} (he : IsProjVarF (imageVar F v V) e) : e ≤ 1 := by
  classical
  have h1 : FieldNumbers.relDim V = ((1 : ℕ) : WithBot (WithTop ℤ)) :=
    (FieldNumbers.relDim_eq_iff_hasRelDim V 1).mpr hV.2
  have h2 : FieldNumbers.relDim (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) V) =
      ((e : ℕ) : WithBot (WithTop ℤ)) := by
    refine (FieldNumbers.relDim_eq_iff_hasRelDim _ e).mpr ?_
    show ringKrullDim _ = _
    rw [← Targets.ProjContract.ringKrullDim_imageVar hv]
    exact he.2
  have h3 := FieldNumbers.ContractRelDimLe.proof F K K' (Targets.ProjContract.emb hv) ι' V
    ((Bridge.isMultiProjPrime_iff V).mpr hV.1)
  rw [h1, h2] at h3
  exact_mod_cast h3

theorem geoNum_one_linear {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) :
    ∃ w : K → ℤ, (∀ k, 0 ≤ w k) ∧ ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * w k := by
  by_cases h : IsRelevant W
  · refine ⟨fun k => ∑ᶠ V ∈ divSupp W (X ⟨k, (h k).choose⟩),
      (multAt (W ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing ι)}) V : ℤ) * geoNum 0 V Fin.elim0, fun k => ?_, fun a => ?_⟩
    · refine finsum_nonneg fun V => finsum_nonneg fun _ => mul_nonneg (Int.natCast_nonneg _) ?_
      unfold geoNum
      split_ifs
      · exact Int.natCast_nonneg _
      · exact le_rfl
    · rw [geoNum, dif_pos h]
      rfl
  · refine ⟨0, fun _ => le_rfl, fun a => ?_⟩
    rw [geoNum, dif_neg h]
    simp

end SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter.PointVertical in

theorem nefAt_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {P : Ideal (MRing ι)}
    {P' : Ideal (MRing ι')} (hP : P ≤ imageZ v P') {p : ℕ} (hp : p.Prime) {a : K → ℤ} (h : PB.NefAt P p a) :
    PB.NefAt P' p (pullDeg κ a) := by
  intro W hWm hPW hch hWd
  have : Fact p.Prime := ⟨hp⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := hch ▸ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) 1 :=
    ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  have hle := image_dim_le_one hv hWp hVi
  obtain ⟨I', hI', -⟩ := Targets.ExistsUnique.full (ZMod p) ι'
  obtain ⟨I, hI, -⟩ := Targets.ExistsUnique.full (ZMod p) ι
  rw [geoNumStatement ι' p I' hI' W 1 _ hWm hpW hWp]
  rcases hle.lt_or_eq with hlt | heq
  · exact (Targets.ProjContract.full (ZMod p) K ι K' ι' I' hI' κ v _ 1 _ (fun _ => a) hv hWp hVi hlt).ge
  · rw [heq] at hVi
    choose i' hi' using hWp.1.2.2
    rw [Targets.ProjDeg.of_found AutoClose.FieldNumbers_ProjectionFormulaDegree Targets.FnDegRelDeg.proof (ZMod p) ι ι'
      I I' hI hI' κ v _ 1 (fun _ => a) i' hv hWp hVi hi']
    refine mul_nonneg (Int.natCast_nonneg _) ?_
    rw [imageVar_red p v hpW] at hVi ⊢
    rw [← geoNumStatement ι p I hI (imageZ v W) 1 _ hImm hpI hVi]
    refine h _ hImm (hP.trans (Ideal.comap_mono hPW)) ?_ ?_
    · rw [← hch]
      have e : (imageZ v W).comap (C : ℤ →+* MRing ι) = W.comap (C : ℤ →+* MRing ι') := by
        ext n
        show rename v (C n) ∈ W ↔ C n ∈ W
        rw [rename_C]
      exact congrArg (fun J : Ideal ℤ => (Submodule.IsPrincipal.generator J).natAbs) e
    · rw [← ringKrullDim_red p hpI]
      exact hVi.2

theorem nefAt_of_nonneg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℕ)
    {a : K → ℤ} (ha : ∀ k, 0 ≤ a k) : PB.NefAt P p a := by
  intro W _ _ _ _
  obtain ⟨w, hw, e⟩ := geoNum_one_linear W
  rw [e]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (hw k)

theorem nefAt_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {p : ℕ}
    {a b : K → ℤ} (ha : PB.NefAt P p a) (hb : PB.NefAt P p b) : PB.NefAt P p (a + b) := by
  intro W h1 h2 h3 h4
  have ha' := ha W h1 h2 h3 h4
  have hb' := hb W h1 h2 h3 h4
  obtain ⟨w, -, e⟩ := geoNum_one_linear W
  rw [e] at ha' hb' ⊢
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  exact add_nonneg ha' hb'

theorem nefAt_step {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (p : ℕ)
    (h : ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0) (τ : Ψ) (i : Fin N) :
    PB.NefAt M.P p (-∑ k ∈ Finset.Iic i, M.xdeg (τ, k)) := by
  intro W h1 h2 h3 h4
  let mu : Top.Wt Ψ N := fun σ k => if σ = τ ∧ k ≤ i then 1 else 0
  have hmu : Top.Dominant mu := by
    intro σ a b hab
    simp only [mu]
    split_ifs with c1 c2
    · exact le_rfl
    · exact absurd ⟨c1.1, hab.trans c1.2⟩ c2
    · exact zero_le_one
    · exact le_rfl
  have key := h mu hmu W ⟨h1, h2, h3, h4⟩
  obtain ⟨w, -, e⟩ := geoNum_one_linear W
  unfold Top.RootModel.curveDeg at key
  rw [Fintype.sum_option, Fintype.sum_prod_type] at key
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, M.x_deg] at key
  rw [Finset.sum_eq_single τ (fun σ _ hσ => by simp [mu, hσ]) (by simp)] at key
  have e2 : ∑ k : Fin N, -mu τ k * (geoNum 1 W (fun _ => M.xdeg (τ, k)) : ℝ) =
      ((-∑ k ∈ Finset.Iic i, geoNum 1 W (fun _ => M.xdeg (τ, k)) : ℤ) : ℝ) := by
    push_cast
    rw [← Finset.sum_neg_distrib, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic i))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [mu, Finset.mem_Iic.1 hk]
    · intro k _ hk
      have : ¬ k ≤ i := fun c => hk (Finset.mem_Iic.2 c)
      simp [mu, this]
  rw [e2] at key
  have key' : 0 ≤ -∑ k ∈ Finset.Iic i, geoNum 1 W (fun _ => M.xdeg (τ, k)) := by exact_mod_cast key
  simp only [e] at key' ⊢
  convert key' using 1
  simp only [Pi.neg_apply, Finset.sum_apply, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

end RootFieldNumerics.Ref
