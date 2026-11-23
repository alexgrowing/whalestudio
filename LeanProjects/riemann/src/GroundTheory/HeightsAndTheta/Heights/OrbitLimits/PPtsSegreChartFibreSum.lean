import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSegreChartFibreSum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartProjFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsMultiHomogIdeal IsMultiHomog
  IsSheet IsSectionOn sheetDensity pot segre mcPts bsmul logNorm)
open ComplexSets

namespace PtsSegreChartFibreSum

section Alg

variable {n d : ℕ}

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem exists_minimalPrime_of_mem_zeroSet {I : Ideal (MvPolynomial (Fin n) ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ zeroSet I) : ∃ J ∈ I.minimalPrimes, x ∈ zeroSet J := by
  have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => RingHom.mem_ker.2 (hx q hq)
  have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨J, hJ, hJle⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨J, hJ, fun q hq => RingHom.mem_ker.1 (hJle hq)⟩

theorem exists_poly_of_not_mem {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A) {f : MvPolynomial (Fin n) ℂ} (hf : f ∉ J) :
    ∃ q : MvPolynomial (Fin d) ℂ, q ≠ 0 ∧
      ∀ x ∈ zeroSet J, MvPolynomial.eval x f = 0 → MvPolynomial.eval (A *ᵥ x) q = 0 := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ)
    (Ideal.Quotient.mk J f)
  obtain ⟨p', hpp, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  have hc0 : p'.coeff 0 ≠ 0 := fun h => hndvd (by simpa using Polynomial.X_dvd_iff.mpr h)
  have := hJ
  have hmk : Ideal.Quotient.mk J f ≠ 0 := fun h => hf (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hp' : p'.eval₂ (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J))
      (Ideal.Quotient.mk J f) = 0 := by
    rw [hpp, Polynomial.eval₂_mul, Polynomial.eval₂_pow] at hp
    rcases mul_eq_zero.1 hp with h | h
    · exfalso
      have h2 := eq_zero_of_pow_eq_zero h
      simp only [Polynomial.eval₂_X, map_zero, sub_zero] at h2
      exact hmk h2
    · exact h
  refine ⟨p'.coeff 0, hc0, fun x hx hfx => ?_⟩
  let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ :=
    Ideal.Quotient.lift J (MvPolynomial.eval x) (fun q hq => hx q hq)
  have hev : ev.comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) =
      MvPolynomial.eval (A *ᵥ x) := by
    refine RingHom.ext fun Q => ?_
    change ev (Ideal.Quotient.mk J (pullback A Q)) = _
    rw [Ideal.Quotient.lift_mk, FibreBound.eval_pullback]
  have h := congrArg ev hp'
  rw [Polynomial.hom_eval₂, hev, map_zero] at h
  have hs : ev (Ideal.Quotient.mk J f) = 0 := hfx
  rw [hs, Polynomial.eval₂_at_zero] at h
  exact h

end Alg

section Chart

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

theorem bsmul_mem_mcPts {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : bsmul c z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 k
    exact ⟨j, mul_ne_zero (hc k) hj⟩
  · obtain ⟨S, hS, hPS⟩ := hP
    have hle : P ≤ RingHom.ker ((MvPolynomial.eval (bsmul c z)).comp
        (MvPolynomial.map (Int.castRingHom ℂ))) := by
      rw [hPS, Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply,
        ReciprocityTheory.ChartRestriction.G.Geo.eval_bsmul_of_isMultiHomog ha,
        hz.2 s (by rw [hPS]; exact Ideal.subset_span hs), mul_zero]
    exact hle hf

omit [DecidableEq K] in

theorem mem_fibre_of_chart {e m : ℕ} {P : Ideal (MRing ι)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i)
    {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i) :
    (fun i' => x (σ.symm i')) ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ (chartProjMatrix σ Ψ *ᵥ x) := by
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

omit [DecidableEq K] in

theorem chart_of_mem_fibre {e m : ℕ} {P : Ideal (MRing ι)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i)
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y) :
    (fun a => w (σ a)) ∈ segreChartSet P σ i ∧ chartProjMatrix σ Ψ *ᵥ (fun a => w (σ a)) = y := by
  obtain ⟨z, hz, rfl, hΨw⟩ := hw
  have hzi : segre z i = 1 := by
    have h := hΨ0 (segre z)
    rw [hΨw, Fin.cons_zero] at h
    exact h.symm
  refine ⟨⟨z, hz, hzi, rfl⟩, funext fun r => ?_⟩
  rw [chartProjMatrix_mulVec]
  simp only [Equiv.apply_symm_apply]
  rw [hΨw, Fin.cons_succ]

theorem chartLift_of_chart {m : ℕ} {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P)
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i) :
    chartLift σ i x ∈ mcPts P ∧ segre (chartLift σ i x) = fun i' => x (σ.symm i') := by
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
    exact bsmul_mem_mcPts hP (fun k => inv_ne_zero (hne k)) hz
  · rw [segre_chartLift σ i z hzi]
    funext i'
    simp

end Chart

section Term

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem logNorm_ofWeight_one (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) (z : (Σ k, ι k) → ℂ) :
    logNorm (HermLine.ofWeight g hg) 1 z = g z := by
  simp [logNorm, HermLine.ofWeight, Real.exp_neg]

omit [DecidableEq K] in

theorem isSectionOn_ofWeight_one {P : Ideal (MRing ι)} (hP : P.IsPrime) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) :
    IsSectionOn P (HermLine.ofWeight g hg) 1 := by
  classical
  refine ⟨0, fun k => by simp [HermLine.ofWeight], ?_, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
  intro mm hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  have h0 : (0 : (Σ k, ι k) →₀ ℕ) = mm := by
    by_contra h
    exact hm (if_neg h)
  subst h0
  simp

theorem term_eq {e m : ℕ} {P : Ideal (MRing ι)} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {L : Fin e → HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hMH : IsMultiHomogIdeal P) (hPp : P.IsPrime) (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g)
    (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hsub : ∀ J ∈ segreChartComponents P σ i, zeroSet J ⊆ segreChartSet P σ i)
    (hcov : ∀ x ∈ segreChartSet P σ i, ∃ J ∈ segreChartComponents P σ i, x ∈ zeroSet J)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {y : Fin e → ℂ} {x : Fin m → ℂ} (hx : x ∈ ComplexSets.fibre J (chartProjMatrix σ Ψ) y)
    (hsep : ∀ J' ∈ segreChartComponents P σ i, J' ≠ J → x ∉ zeroSet J')
    (hsh : ∃ s, IsSheetAt J (chartProjMatrix σ Ψ) x s) :
    chartWeight σ i g x * ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ hsh.choose) y =
      sheetDensity P Ψ (pot L) g y (fun i' => x (σ.symm i')) := by
  classical
  obtain ⟨U, hUo, hxU, hsd, hsx, hsU, V, hV, hloc⟩ := hsh.choose_spec
  generalize hsh.choose = s at hsd hsx hsU hloc ⊢
  have hxy : chartProjMatrix σ Ψ *ᵥ x = y := hx.2
  rw [hxy] at hxU hsx
  have hxC : x ∈ segreChartSet P σ i := hsub J hJ hx.1
  have hx1 : x (σ.symm i) = 1 := chart_coord_eq_one hJ hx.1
  set w : ((k : K) → ι k) → ℂ := fun i' => x (σ.symm i') with hw
  have hγ' : IsSheet P Ψ y w (fun y' => chartLift σ i (s y')) := by
    refine ⟨?_, ?_⟩
    · show segre (chartLift σ i (s y)) = w
      rw [hsx]
      exact (chartLift_of_chart hMH hxC).2
    · filter_upwards [hUo.mem_nhds hxU] with y' hy'
      have hsy' := hsU y' hy'
      have hC' := hsub J hJ hsy'.2
      refine ⟨?_, (chartLift_of_chart hMH hC').1, ?_⟩
      · have hd : DifferentiableAt ℂ s y' := hsd.differentiableAt (hUo.mem_nhds hy')
        refine differentiableAt_pi.2 fun p => ?_
        exact differentiableAt_pi.1 hd (σ.symm (Function.update i p.1 p.2))
      · rw [(chartLift_of_chart hMH hC').2]
        have hf := mem_fibre_of_chart (Ψ := Ψ) hΨ0 hC'
        rw [hsy'.1] at hf
        obtain ⟨_, _, _, h⟩ := hf
        exact h
  have hex : ∃ γ, IsSheet P Ψ y w γ := ⟨_, hγ'⟩
  unfold sheetDensity
  rw [dif_pos hex]
  set γ := hex.choose with hγ_def
  have hγ : IsSheet P Ψ y w γ := hex.choose_spec
  have hγan := ReciprocityTheory.ChartRestriction.G.Geo.sheet_analyticAt ReciprocityTheory.ChartRestriction.G.Geo.osgood hγ
  have hγ'an := ReciprocityTheory.ChartRestriction.G.Geo.sheet_analyticAt ReciprocityTheory.ChartRestriction.G.Geo.osgood hγ'
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
  have hE4 : ∀ᶠ y' in 𝓝 y, ∀ J' ∈ segreChartComponents P σ i, J' ≠ J →
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
    have hC : (fun a => segre (γ y') (σ a)) ∈ segreChartSet P σ i := ⟨γ y', hmc, hzi, rfl⟩
    have hAx : chartProjMatrix σ Ψ *ᵥ (fun a => segre (γ y') (σ a)) = y' :=
      (chart_of_mem_fibre (Ψ := Ψ) hΨ0 ⟨γ y', hmc, rfl, hΨy⟩).2
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
  have hde := ReciprocityTheory.ChartRestriction.G.Geo.density_eq hL (isSectionOn_ofWeight_one hPp g hg.2) hγan hγ'an hy0 hseg
  rw [logNorm_ofWeight_one, logNorm_ofWeight_one] at hde
  rw [hde, chartWeight_of_coord g hx1, hsx]
  rfl

end Term

end PtsSegreChartFibreSum

open PtsSegreChartFibreSum in

theorem PtsSegreChartFibreSum.proof (h₁ : SegreChartZeroSet.Statement) (h₂ : SegreChartProjFinite.Statement) :
    PtsSegreChartFibreSum.Statement := by
  intro K _ _ ι _ P e m σ i L g Ψ hP hL hg hΨ hΨ0
  classical
  set A := chartProjMatrix σ Ψ with hAdef
  set C := segreChartComponents P σ i with hCdef
  have hMH : IsMultiHomogIdeal P := hP.2.1.2.1
  have hPp : P.IsPrime := hP.2.1.1
  have hzero := h₁ K ι P m σ i hMH
  have hmin : ∀ J ∈ C, J ∈ (segreChartIdeal P σ i).minimalPrimes :=
    fun J hJ => mem_segreChartComponents.1 hJ
  have hprime : ∀ J ∈ C, J.IsPrime := fun J hJ => (hmin J hJ).1.1
  have hfinp : ∀ J ∈ C, IsFiniteProjection J A := h₂ K ι P e m σ i Ψ hP hΨ hΨ0
  have hdim : ∀ J ∈ C, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) :=
    SegreChartDim.proof K ι P e m σ i hP
  have hsub : ∀ J ∈ C, zeroSet J ⊆ segreChartSet P σ i := by
    intro J hJ x hx
    rw [← hzero]
    exact fun q hq => hx q ((hmin J hJ).1.2 hq)
  have hcov : ∀ x ∈ segreChartSet P σ i, ∃ J ∈ C, x ∈ zeroSet J := by
    intro x hx
    rw [← hzero] at hx
    obtain ⟨J, hJ, hxJ⟩ := exists_minimalPrime_of_mem_zeroSet hx
    exact ⟨J, mem_segreChartComponents.2 hJ, hxJ⟩

  have hG1 : ∀ᵐ y, ∀ J ∈ C, ∀ x ∈ ComplexSets.fibre J A y, ∃ s, IsSheetAt J A x s := by
    refine (eventually_all_finset C).2 fun J hJ => ?_
    obtain ⟨Q, U, D, N, s, -, hUD, -, -, hvol, hfib⟩ :=
      DiscriminantSheetCover.proof ComplexSets.DiscriminantCover.full m e J A (hprime J hJ) (hdim J hJ)
        (hfinp J hJ)
    have hae : (⋃ k, D k) ∈ ae volume := mem_ae_iff.2 hvol
    filter_upwards [hae] with y hy x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
    obtain ⟨hrange, -, hsheet⟩ := hfib k y ((hUD k).2.2.1 hk)
    rw [hrange] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨_, hsheet j⟩

  have hG2 : ∀ᵐ y, ∀ J ∈ C, ∀ J' ∈ C, J' ≠ J → ∀ x ∈ ComplexSets.fibre J A y, x ∉ zeroSet J' := by
    refine (eventually_all_finset C).2 fun J hJ => (eventually_all_finset C).2 fun J' hJ' => ?_
    by_cases hJJ : J' = J
    · exact Eventually.of_forall fun _ h => absurd hJJ h
    have hnle : ¬ J' ≤ J := fun hle =>
      hJJ (le_antisymm hle ((hmin J hJ).2 ⟨hprime J' hJ', (hmin J' hJ').1.2⟩ hle))
    obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hnle
    obtain ⟨q, hq, hqz⟩ := exists_poly_of_not_mem (hprime J hJ) (hfinp J hJ) hfJ
    have hae : {y : Fin e → ℂ | MvPolynomial.eval y q = 0}ᶜ ∈ ae volume :=
      compl_mem_ae_iff.2 (DiscriminantSheetCover.volume_zero_set q hq)
    filter_upwards [hae] with y hy _ x hx hxJ'
    exact hy (by rw [← hx.2]; exact hqz x hx.1 (hxJ' f hfJ'))
  filter_upwards [hG1, hG2] with y hy1 hy2
  set ψ : (Fin m → ℂ) → ((k : K) → ι k) → ℂ := fun x i' => x (σ.symm i') with hψ
  set S := ⋃ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))), ComplexSets.fibre J A y with hS
  have hfinF := ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite K ι P e Ψ hP hΨ y
  have hψS : ∀ x ∈ S, ψ x ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y := by
    intro x hx
    obtain ⟨J, hJ, hxJ⟩ := Set.mem_iUnion₂.1 hx
    have h := mem_fibre_of_chart (Ψ := Ψ) hΨ0 (hsub J hJ hxJ.1)
    rwa [hxJ.2] at h
  have himg : ψ '' S = ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y := by
    refine Set.Subset.antisymm ?_ fun w hw => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hψS x hx
    · obtain ⟨hC, hAw⟩ := chart_of_mem_fibre hΨ0 hw
      obtain ⟨J, hJ, hxJ⟩ := hcov _ hC
      exact ⟨_, Set.mem_iUnion₂.2 ⟨J, hJ, hxJ, hAw⟩, funext fun i' => by simp [hψ]⟩
  have hinj : Set.InjOn ψ S := fun x _ x' _ h => funext fun a => by
    simpa [hψ] using congrFun h (σ a)
  have hfinJ : ∀ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))), (ComplexSets.fibre J A y).Finite := by
    intro J hJ
    refine (hfinF.image fun w a => w (σ a)).subset fun x hx => ?_
    refine ⟨ψ x, hψS x (Set.mem_iUnion₂.2 ⟨J, hJ, hx⟩), funext fun a => by simp [hψ]⟩
  have hdisj : (C : Set (Ideal (MvPolynomial (Fin m) ℂ))).PairwiseDisjoint fun J => ComplexSets.fibre J A y :=
    fun J hJ J' hJ' hne => Set.disjoint_left.2 fun x hx hx' => hy2 J hJ J' hJ' (Ne.symm hne) x hx hx'.1
  calc ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (pot L) g y w
      = ∑ᶠ w ∈ ψ '' S, sheetDensity P Ψ (pot L) g y w := by rw [himg]
    _ = ∑ᶠ x ∈ S, sheetDensity P Ψ (pot L) g y (ψ x) := finsum_mem_image hinj
    _ = ∑ᶠ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))),
          ∑ᶠ x ∈ ComplexSets.fibre J A y, sheetDensity P Ψ (pot L) g y (ψ x) :=
        finsum_mem_biUnion hdisj C.finite_toSet hfinJ
    _ = ∑ J ∈ C, ∑ᶠ x ∈ ComplexSets.fibre J A y, sheetDensity P Ψ (pot L) g y (ψ x) :=
        finsum_mem_coe_finset _ _
    _ = ∑ J ∈ C, chartDens J A (chartWeight σ i g) (chartPot σ i L) y := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        simp only [chartDens, sheetSum]
        refine finsum_mem_congr rfl fun x hx => ?_
        rw [dif_pos (hy1 J hJ x hx)]
        exact (term_eq hMH hPp hL hg hΨ0 hsub hcov hJ hx (fun J' hJ' h => hy2 J hJ J' hJ' h x hx)
          (hy1 J hJ x hx)).symm

end GroundTheory.Heights₂.Heights
