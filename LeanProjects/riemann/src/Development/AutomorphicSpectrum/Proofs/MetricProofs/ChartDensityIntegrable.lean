import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSegreChartFibreSum
set_option maxSynthPendingDepth 1

noncomputable section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum

open scoped Matrix
open GroundTheory.Heights₂.Heights (chartLift chartProjMatrix_mulVec chartWeight_of_coord segre_chartLift
  chartLift_segre_apply IsSheetAt sheetSum)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet IsFiniteProjection)
open GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum (isClosed_zeroSet exists_minimalPrime_of_mem_zeroSet
  exists_poly_of_not_mem logNorm_ofWeight_one isSectionOn_ofWeight_one)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_bsmul_of_isMultiHomogC {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (bsmul c z) s = (∏ k, c k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (bsmul c z p) ^ m p = (∏ k, c k ^ a k) * ∏ p, z p ^ m p := by
    simp only [bsmul, mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [hprod]
  ring

theorem bsmul_mem_conePts {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : bsmul c z ∈ conePts Q := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 k
    exact ⟨j, mul_ne_zero (hc k) hj⟩
  · obtain ⟨S, hS, hQS⟩ := hQ
    have hle : Q ≤ RingHom.ker (MvPolynomial.eval (bsmul c z)) := by
      rw [hQS, Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      rw [SetLike.mem_coe, RingHom.mem_ker, eval_bsmul_of_isMultiHomogC ha,
        hz.2 s (by rw [hQS]; exact Ideal.subset_span hs), mul_zero]
    exact hle hf

theorem isSheet_bot_of_isSetSheet {e : ℕ} {Q : Ideal (MRingOver ℂ ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSetSheet (conePts Q) Ψ y w γ) : IsSheet (⊥ : Ideal (MRing ι)) Ψ y w γ := by
  refine ⟨h.1, h.2.mono fun y' hy' => ⟨hy'.1, ⟨hy'.2.1.1, fun f hf => ?_⟩, hy'.2.2⟩⟩
  rw [Ideal.mem_bot.1 hf]
  simp

theorem mem_setFibre_of_chart {e m : ℕ} {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i)
    {x : Fin m → ℂ} (hx : x ∈ chartSet S σ i) :
    (fun i' => x (σ.symm i')) ∈ setFibre S Ψ (chartProjMatrix σ Ψ *ᵥ x) := by
  obtain ⟨z, hz, hzi, hxe⟩ := hx
  have hw : (fun i' => x (σ.symm i')) = segre z := by
    funext i'
    simp [hxe]
  refine ⟨z, hz, hw.symm, ?_⟩
  rw [hw]
  funext r
  refine Fin.cases ?_ (fun r => ?_) r
  · rw [hΨ0, hzi, Fin.cons_zero]
  · rw [Fin.cons_succ, chartProjMatrix_mulVec, hw]

theorem chart_of_mem_setFibre {e m : ℕ} {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i)
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ setFibre S Ψ y) :
    (fun a => w (σ a)) ∈ chartSet S σ i ∧ chartProjMatrix σ Ψ *ᵥ (fun a => w (σ a)) = y := by
  obtain ⟨z, hz, rfl, hΨw⟩ := hw
  have hzi : segre z i = 1 := by
    have h := hΨ0 (segre z)
    rw [hΨw, Fin.cons_zero] at h
    exact h.symm
  refine ⟨⟨z, hz, hzi, rfl⟩, funext fun r => ?_⟩
  rw [chartProjMatrix_mulVec]
  simp only [Equiv.apply_symm_apply]
  rw [hΨw, Fin.cons_succ]

variable [DecidableEq K]

theorem chartLift_of_chartSet {m : ℕ} {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {x : Fin m → ℂ}
    (hx : x ∈ chartSet (conePts Q) σ i) :
    chartLift σ i x ∈ conePts Q ∧ segre (chartLift σ i x) = fun i' => x (σ.symm i') := by
  obtain ⟨z, hz, hzi, rfl⟩ := hx
  have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := by
    have h1 : ∏ k, z ⟨k, i k⟩ ≠ 0 := by
      change segre z i ≠ 0
      rw [hzi]
      exact one_ne_zero
    exact fun k => (Finset.prod_ne_zero_iff.mp h1) k (Finset.mem_univ k)
  refine ⟨?_, ?_⟩
  · have heq : chartLift σ i (fun a => segre z (σ a)) = bsmul (fun k => (z ⟨k, i k⟩)⁻¹) z := by
      funext p
      obtain ⟨k, j⟩ := p
      rw [chartLift_segre_apply σ i z hzi k j]
      simp only [bsmul]
      ring
    rw [heq]
    exact bsmul_mem_conePts hQ (fun k => inv_ne_zero (hne k)) hz
  · rw [segre_chartLift σ i z hzi]
    funext i'
    simp

theorem term_eq {e m : ℕ} {Q : Ideal (MRingOver ℂ ι)} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {L : Fin e → HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hMH : IsMultiHomogIdeal Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z)
    (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hsub : ∀ J ∈ chartComponents (conePts Q) σ i, zeroSet J ⊆ chartSet (conePts Q) σ i)
    (hcov : ∀ x ∈ chartSet (conePts Q) σ i, ∃ J ∈ chartComponents (conePts Q) σ i, x ∈ zeroSet J)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ chartComponents (conePts Q) σ i)
    {y : Fin e → ℂ} {x : Fin m → ℂ}
    (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J (chartProjMatrix σ Ψ) y)
    (hsep : ∀ J' ∈ chartComponents (conePts Q) σ i, J' ≠ J → x ∉ zeroSet J')
    (hsh : ∃ s, IsSheetAt J (chartProjMatrix σ Ψ) x s) :
    chartWeight σ i g x * ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ hsh.choose) y =
      setSheetDensity (conePts Q) Ψ (pot L) g y (fun i' => x (σ.symm i')) := by
  classical
  obtain ⟨U, hUo, hxU, hsd, hsx, hsU, V, hV, hloc⟩ := hsh.choose_spec
  generalize hsh.choose = s at hsd hsx hsU hloc ⊢
  have hxy : chartProjMatrix σ Ψ *ᵥ x = y := hx.2
  rw [hxy] at hxU hsx
  have hxC : x ∈ chartSet (conePts Q) σ i := hsub J hJ hx.1
  have hx1 : x (σ.symm i) = 1 := by
    obtain ⟨z, -, hzi, rfl⟩ := hxC
    simpa using hzi
  set w : ((k : K) → ι k) → ℂ := fun i' => x (σ.symm i') with hw
  have hγ' : IsSetSheet (conePts Q) Ψ y w (fun y' => chartLift σ i (s y')) := by
    refine ⟨?_, ?_⟩
    · show segre (chartLift σ i (s y)) = w
      rw [hsx]
      exact (chartLift_of_chartSet hMH hxC).2
    · filter_upwards [hUo.mem_nhds hxU] with y' hy'
      have hsy' := hsU y' hy'
      have hC' := hsub J hJ hsy'.2
      refine ⟨?_, (chartLift_of_chartSet hMH hC').1, ?_⟩
      · have hd : DifferentiableAt ℂ s y' := hsd.differentiableAt (hUo.mem_nhds hy')
        refine differentiableAt_pi.2 fun p => ?_
        exact differentiableAt_pi.1 hd (σ.symm (Function.update i p.1 p.2))
      · rw [(chartLift_of_chartSet hMH hC').2]
        have hf := mem_setFibre_of_chart (Ψ := Ψ) hΨ0 hC'
        rw [hsy'.1] at hf
        obtain ⟨_, _, _, h⟩ := hf
        exact h
  have hex : ∃ γ, IsSetSheet (conePts Q) Ψ y w γ := ⟨_, hγ'⟩
  unfold setSheetDensity
  rw [dif_pos hex]
  set γ := hex.choose with hγ_def
  have hγ : IsSetSheet (conePts Q) Ψ y w γ := hex.choose_spec
  have hγan := sheet_analyticAt osgood (isSheet_bot_of_isSetSheet hγ)
  have hγ'an := sheet_analyticAt osgood (isSheet_bot_of_isSetSheet hγ')
  have hcseg : Continuous fun z : (Σ k, ι k) → ℂ => fun a : Fin m => segre z (σ a) := by
    refine continuous_pi fun a => ?_
    simp only [segre]
    exact continuous_finsetProd _ fun k _ => continuous_apply _
  have hxy0 : (fun a => segre (γ y) (σ a)) = x := by
    funext a
    rw [hγ.1]
    simp [hw]
  have ht : Tendsto (fun y' => fun a => segre (γ y') (σ a)) (𝓝 y) (𝓝 x) := by
    have h2 := (hcseg.continuousAt.comp hγan.continuousAt).tendsto
    simp only [Function.comp_def] at h2
    rwa [hxy0] at h2
  have hE4 : ∀ᶠ y' in 𝓝 y, ∀ J' ∈ chartComponents (conePts Q) σ i, J' ≠ J →
      (fun a => segre (γ y') (σ a)) ∉ zeroSet J' := by
    refine (eventually_all_finset _).2 fun J' hJ' => ?_
    by_cases hJJ : J' = J
    · exact Eventually.of_forall fun _ h => absurd hJJ h
    · exact Filter.Eventually.mono (p := fun y' => (fun a => segre (γ y') (σ a)) ∈ (zeroSet J')ᶜ)
        (ht ((isClosed_zeroSet J').isOpen_compl.mem_nhds (hsep J' hJ' hJJ))) fun _ h _ => h
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (chartLift σ i (s y')) := by
    filter_upwards [hγ.2, hUo.mem_nhds hxU, ht hV, hE4] with y' hy' hyU hxV h4
    obtain ⟨-, hmc, hΨy⟩ := hy'
    have hzi : segre (γ y') i = 1 := by
      have h := hΨ0 (segre (γ y'))
      rw [hΨy, Fin.cons_zero] at h
      exact h.symm
    have hC : (fun a => segre (γ y') (σ a)) ∈ chartSet (conePts Q) σ i := ⟨γ y', hmc, hzi, rfl⟩
    have hAx : chartProjMatrix σ Ψ *ᵥ (fun a => segre (γ y') (σ a)) = y' :=
      (chart_of_mem_setFibre (Ψ := Ψ) hΨ0 ⟨γ y', hmc, rfl, hΨy⟩).2
    obtain ⟨J', hJ', hxJ'⟩ := hcov _ hC
    have hJJ : J' = J := by
      by_contra h
      exact h4 J' hJ' h hxJ'
    have hxJ : (fun a => segre (γ y') (σ a)) ∈ zeroSet J := hJJ ▸ hxJ'
    have hxs : (fun a => segre (γ y') (σ a)) = s y' := by
      have h := hloc _ ⟨hxJ, hxV⟩ (by rw [hAx]; exact hyU)
      rwa [hAx] at h
    rw [← hxs]
    exact (segre_chartLift σ i (γ y') hzi).symm
  have hy0 : ∀ k, ∃ j, γ y ⟨k, j⟩ ≠ 0 := hγ.2.self_of_nhds.2.1.1
  have hde := density_eq hL (isSectionOn_ofWeight_one (P := (⊥ : Ideal (MRing ι))) Ideal.isPrime_bot g hg)
    hγan hγ'an hy0 hseg
  rw [logNorm_ofWeight_one, logNorm_ofWeight_one] at hde
  rw [hde, chartWeight_of_coord g hx1, hsx]
  rfl

theorem fibreSum : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → (∀ j, IsSmoothHerm (L j)) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    (∀ w, Ψ w 0 = w i) → (∀ y, (setFibre (conePts Q) Ψ y).Finite) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    (∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ)) →
    ∀ᵐ y, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot L) g y w =
      ∑ J ∈ chartComponents (conePts Q) σ i,
        chartDens J (chartProjMatrix σ Ψ) (chartWeight σ i g) (chartPot σ i L) y := by
  intro K _ _ ι _ Q e m σ i L g Ψ hQ hL hg hΨ0 hfinF hzero hdim hfinp
  classical
  set A := chartProjMatrix σ Ψ with hAdef
  set C := chartComponents (conePts Q) σ i with hCdef
  have hMH : IsMultiHomogIdeal Q := hQ.2.1.2.1
  have hmin : ∀ J ∈ C, J ∈ (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i).minimalPrimes :=
    fun J hJ => GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.1 hJ
  have hprime : ∀ J ∈ C, J.IsPrime := fun J hJ => (hmin J hJ).1.1
  have hsub : ∀ J ∈ C, zeroSet J ⊆ chartSet (conePts Q) σ i := by
    intro J hJ x hx
    rw [← hzero]
    exact fun q hq => hx q ((hmin J hJ).1.2 hq)
  have hcov : ∀ x ∈ chartSet (conePts Q) σ i, ∃ J ∈ C, x ∈ zeroSet J := by
    intro x hx
    rw [← hzero] at hx
    obtain ⟨J, hJ, hxJ⟩ := exists_minimalPrime_of_mem_zeroSet hx
    exact ⟨J, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.2 hJ, hxJ⟩

  have hG1 : ∀ᵐ y, ∀ J ∈ C, ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, ∃ s, IsSheetAt J A x s := by
    refine (eventually_all_finset C).2 fun J hJ => ?_
    obtain ⟨Q', U, D, N, s, -, hUD, -, -, hvol, hfib⟩ :=
      GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full
        m e J A (hprime J hJ) (hdim J hJ) (hfinp J hJ)
    have hae : (⋃ k, D k) ∈ ae volume := mem_ae_iff.2 hvol
    filter_upwards [hae] with y hy x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
    obtain ⟨hrange, -, hsheet⟩ := hfib k y ((hUD k).2.2.1 hk)
    rw [hrange] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨_, hsheet j⟩

  have hG2 : ∀ᵐ y, ∀ J ∈ C, ∀ J' ∈ C, J' ≠ J →
      ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, x ∉ zeroSet J' := by
    refine (eventually_all_finset C).2 fun J hJ => (eventually_all_finset C).2 fun J' hJ' => ?_
    by_cases hJJ : J' = J
    · exact Eventually.of_forall fun _ h => absurd hJJ h
    have hnle : ¬ J' ≤ J := fun hle =>
      hJJ (le_antisymm hle ((hmin J hJ).2 ⟨hprime J' hJ', (hmin J' hJ').1.2⟩ hle))
    obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hnle
    obtain ⟨q, hq, hqz⟩ := exists_poly_of_not_mem (hprime J hJ) (hfinp J hJ) hfJ
    have hae : {y : Fin e → ℂ | MvPolynomial.eval y q = 0}ᶜ ∈ ae volume :=
      compl_mem_ae_iff.2 (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.volume_zero_set q hq)
    filter_upwards [hae] with y hy _ x hx hxJ'
    exact hy (by rw [← hx.2]; exact hqz x hx.1 (hxJ' f hfJ'))
  filter_upwards [hG1, hG2] with y hy1 hy2
  set ψ : (Fin m → ℂ) → ((k : K) → ι k) → ℂ := fun x i' => x (σ.symm i') with hψ
  set S := ⋃ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))),
    GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y with hS
  have hψS : ∀ x ∈ S, ψ x ∈ setFibre (conePts Q) Ψ y := by
    intro x hx
    obtain ⟨J, hJ, hxJ⟩ := Set.mem_iUnion₂.1 hx
    have h := mem_setFibre_of_chart (Ψ := Ψ) hΨ0 (hsub J hJ hxJ.1)
    rwa [hxJ.2] at h
  have himg : ψ '' S = setFibre (conePts Q) Ψ y := by
    refine Set.Subset.antisymm ?_ fun w hw => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hψS x hx
    · obtain ⟨hC, hAw⟩ := chart_of_mem_setFibre hΨ0 hw
      obtain ⟨J, hJ, hxJ⟩ := hcov _ hC
      exact ⟨_, Set.mem_iUnion₂.2 ⟨J, hJ, hxJ, hAw⟩, funext fun i' => by simp [hψ]⟩
  have hinj : Set.InjOn ψ S := fun x _ x' _ h => funext fun a => by
    simpa [hψ] using congrFun h (σ a)
  have hfinJ : ∀ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))),
      (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := by
    intro J hJ
    refine ((hfinF y).image fun w a => w (σ a)).subset fun x hx => ?_
    refine ⟨ψ x, hψS x (Set.mem_iUnion₂.2 ⟨J, hJ, hx⟩), funext fun a => by simp [hψ]⟩
  have hdisj : (C : Set (Ideal (MvPolynomial (Fin m) ℂ))).PairwiseDisjoint
      fun J => GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y :=
    fun J hJ J' hJ' hne => Set.disjoint_left.2 fun x hx hx' => hy2 J hJ J' hJ' (Ne.symm hne) x hx hx'.1
  calc ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot L) g y w
      = ∑ᶠ w ∈ ψ '' S, setSheetDensity (conePts Q) Ψ (pot L) g y w := by rw [himg]
    _ = ∑ᶠ x ∈ S, setSheetDensity (conePts Q) Ψ (pot L) g y (ψ x) := finsum_mem_image hinj
    _ = ∑ᶠ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))),
          ∑ᶠ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y,
            setSheetDensity (conePts Q) Ψ (pot L) g y (ψ x) :=
        finsum_mem_biUnion hdisj C.finite_toSet hfinJ
    _ = ∑ J ∈ C, ∑ᶠ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y,
          setSheetDensity (conePts Q) Ψ (pot L) g y (ψ x) :=
        finsum_mem_coe_finset _ _
    _ = ∑ J ∈ C, chartDens J A (chartWeight σ i g) (chartPot σ i L) y := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        simp only [chartDens, sheetSum]
        refine finsum_mem_congr rfl fun x hx => ?_
        rw [dif_pos (hy1 J hJ x hx)]
        exact (term_eq hMH hL hg hΨ0 hsub hcov hJ hx (fun J' hJ' h => hy2 J hJ J' hJ' h x hx)
          (hy1 J hJ x hx)).symm

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum
