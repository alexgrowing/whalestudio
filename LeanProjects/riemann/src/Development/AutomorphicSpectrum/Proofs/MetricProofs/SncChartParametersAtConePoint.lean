import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MapMemChartIdealOfAevalEqZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanEqTopOfForallDotEqZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundaryOnPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsRegularLocalRingLocRingOfSpan
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMulPowEqAevalOfMemAdjoinInv
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasicOpenOfIsSncModel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SndEqZeroOfSpan
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem sum_pderiv_renC {σ : Type} [Fintype σ] (t₀ : σ → ℂ) (v : Fin (Fintype.card σ) → ℂ)
    (h : MvPolynomial σ ℂ) :
    ∑ j, v j * eval (renPt t₀) (pderiv j (renC σ h)) =
      ∑ q, v (Fintype.equivFin σ q) * eval t₀ (pderiv q h) := by
  rw [← Equiv.sum_comp (Fintype.equivFin σ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have ht : (renPt t₀ ∘ ⇑(Fintype.equivFin σ)) = t₀ := by
    funext x
    simp [renPt]
  rw [renC, MvPolynomial.renameEquiv_apply, MvPolynomial.pderiv_rename (Fintype.equivFin σ).injective,
    MvPolynomial.eval_rename, ht]

theorem exists_params : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), z ∈ conePts (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) → (∀ k, z ⟨k, p k⟩ ≠ 0) → ∃ (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), ((∀ h ∈ (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p), eval (renPt (affCoord p z)) h = 0) ∧ IsRegularLocalRing (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) ∧ ringKrullDim (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) = e ∧ Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) ∧ (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) ⊔ (ReciprocityTheory.ChartRestriction.G.Geo.pC J)) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮))) := by
  intro K _ ι _ Ω _ _ y e J hA hS p z hz hzp
  classical
  have hPh : IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) :=
    ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_pC hA.2.1.2.1
  have hw := (mem_conePts_iff_chartIdeal hPh p z hzp).1 hz
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, aeval_X, h0]
      simp
    have h1 := hz.2 _ (Ideal.subset_span ⟨_, hX, rfl⟩)
    rw [map_X, eval_X] at h1
    exact hzp k h1
  set P := ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) with hPdef
  set τ : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, p q.1⟩ with hτ
  set t₀ := affCoord p z with ht₀
  have hker : ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ chartIdeal P p :=
    GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.map_mem_chartIdeal_of_aeval_eq_zero K ι Ω y p hy
  have hker0 : ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval τ G = 0 → eval t₀ (map (algebraMap ℚ ℂ) G) = 0 :=
    fun G hG => hw _ (hker G hG)
  obtain ⟨F, S, zz, n, hF, hFt, hSeq, hspan, hbd⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_basicOpen_of_isSncModel K ι Ω y e J hS p hy t₀ hker0
  have hrep : ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Σ k, ι k) ℚ),
      ((zz i : S) : Ω) * aeval τ F ^ N = aeval τ G :=
    fun i => GlobalTheory.CompanionTheory.Ar.Cmp.exists_mul_pow_eq_aeval_of_mem_adjoin_inv Ω (Σ k, ι k) τ F S hF hSeq (zz i)
  choose N Z hZ using hrep
  set c : Fin e → ℂ := fun i => eval t₀ (map (algebraMap ℚ ℂ) (Z i)) / eval t₀ (map (algebraMap ℚ ℂ) F) ^ N i with hc
  set r₀ : Fin e → MvPolynomial (Σ k, ι k) ℂ :=
    fun i => map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i with hr₀
  have hcZ : ∀ i, eval t₀ (map (algebraMap ℚ ℂ) (Z i)) = c i * eval t₀ (map (algebraMap ℚ ℂ) F) ^ N i :=
    fun i => (div_mul_cancel₀ _ (pow_ne_zero _ hFt)).symm
  have hr₀z : ∀ i, eval t₀ (r₀ i) = 0 := by
    intro i
    simp only [hr₀, map_sub, map_mul, map_pow, eval_C]
    rw [hcZ i]
    simp
  have hIt : ∀ h ∈ SncRes.ideal P p, eval (renPt t₀) h = 0 := renPt_zero _ _ hw
  have hrz : ∀ l, eval (renPt t₀) (renC (Σ k, ι k) (r₀ l)) = 0 := fun l => by
    rw [eval_renC]; exact hr₀z l
  have hd : ringKrullDim (locRing (SncRes.ideal P p) (renPt t₀)) = e :=
    (ringKrullDim_eq_of_ringEquiv (locAtEquiv _ _)).symm.trans
      (ringKrullDim_locAt_chart _ hPh e (ReciprocityTheory.ChartRestriction.G.Geo.pcEquidim K ι _ e hA) p _ hw)
  have hsp : Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt t₀))
      (renC (Σ k, ι k) (r₀ l))) =
      Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt t₀))) (ptIdeal (renPt t₀)) := by
    refine GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.span_algebraMap_eq_map_ptIdeal e (SncRes.ideal P p) (renPt t₀) _ hIt hrz fun v hv1 hv2 => ?_
    have hv₀ : (fun q => v (Fintype.equivFin (Σ k, ι k) q)) = 0 := by
      refine GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.tangent_eq_zero Ω (Σ k, ι k) τ F S e zz Z N t₀ _ c hF hSeq hspan hZ hker0 hFt ?_ hcZ ?_
      · intro G hG
        rw [← sum_pderiv_renC]
        refine hv1 _ ?_
        exact Ideal.mem_map_of_mem _ (hker G hG)
      · intro i
        rw [← sum_pderiv_renC]
        exact hv2 i
    funext j
    have := congr_fun hv₀ ((Fintype.equivFin (Σ k, ι k)).symm j)
    simpa using this
  refine ⟨fun l => renC (Σ k, ι k) (r₀ l), Finset.univ.filter fun i : Fin e => (i : ℕ) < n ∧ c i = 0,
    hIt, GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg.isRegularLocalRing_locRing_of_span _ e _ _ _ hIt hd hsp, hd, hsp, ?_⟩
  intro 𝔮 h𝔮 hI𝔮 h𝔮t
  have hle₀ : chartIdeal P p ≤ 𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) :=
    Ideal.map_le_iff_le_comap.1 hI𝔮
  have hpt : ∀ g : MvPolynomial (Σ k, ι k) ℂ, renC (Σ k, ι k) g ∈ 𝔮 → eval t₀ g = 0 := by
    intro g hg
    have := h𝔮t hg
    rw [ptIdeal, RingHom.mem_ker, eval_renC] at this
    exact this
  have hprime : (𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)).IsPrime :=
    Ideal.comap_isPrime _ _
  have hkp := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.boundary_on_primes Ω (Σ k, ι k) τ F S (J : Set _) e n zz Z N hF hSeq hZ hbd
    (𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)) hprime
    (fun G hG => hle₀ (hker G hG))
    (fun hFq => hFt (hpt (map (algebraMap ℚ ℂ) F) hFq))
  have hleft : SncRes.ideal (P ⊔ ReciprocityTheory.ChartRestriction.G.Geo.pC J) p ≤ 𝔮 ↔
      ∀ g ∈ (J : Set _), map (Int.castRingHom ℂ) g ∈
        𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) := by
    rw [SncRes.ideal, Ideal.map_le_iff_le_comap]
    constructor
    · intro h g hg
      exact h (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨g, hg, rfl⟩)))
    · intro h
      refine sup_le (sup_le (fun f hf => hle₀ (Ideal.mem_sup_left hf)) ?_)
        (fun f hf => hle₀ (Ideal.mem_sup_right hf))
      refine Ideal.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact h g hg
  rw [hleft, hkp]
  constructor
  · rintro ⟨i, hin, hi⟩
    have hci : c i = 0 := by
      have h0 : eval t₀ (map (algebraMap ℚ ℂ) (Z i)) = 0 := hpt _ hi
      show eval t₀ _ / _ = 0
      rw [h0, zero_div]
    refine ⟨i, by simp [hin, hci], ?_⟩
    have : r₀ i = map (algebraMap ℚ ℂ) (Z i) := by simp [hr₀, hci]
    simp only [this]
    exact hi
  · rintro ⟨i, hiJ, hi⟩
    obtain ⟨hin, hci⟩ := (Finset.mem_filter.1 hiJ).2
    refine ⟨i, hin, ?_⟩
    have : r₀ i = map (algebraMap ℚ ℂ) (Z i) := by simp [hr₀, hci]
    simp only [this] at hi
    exact hi

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
