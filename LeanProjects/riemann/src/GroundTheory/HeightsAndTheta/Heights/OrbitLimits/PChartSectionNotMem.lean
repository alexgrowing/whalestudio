import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSection
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Algebra
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn mcPts segre)

namespace ChartSectionNotMem

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def coneMap (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
    MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
  aeval fun q => X q.1 * C (Ideal.Quotient.mk 𝔮 (X q))

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_C_mk (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => (C (Ideal.Quotient.mk 𝔮 (X q)) : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))) f =
      C (Ideal.Quotient.mk 𝔮 f) := by
  have : (aeval fun q => (C (Ideal.Quotient.mk 𝔮 (X q)) : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))) =
      (IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
        (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).comp (Ideal.Quotient.mkₐ ℂ 𝔮) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [MvPolynomial.algebraMap_eq]
  rw [this]
  simp [MvPolynomial.algebraMap_eq]

theorem coneMap_of_isMultiHomog (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {f : MvPolynomial (Σ k, ι k) ℂ}
    {a : K → ℕ} (hf : ReciprocityTheory.AnForm.R.IsMultiHomog f a) :
    coneMap 𝔮 f = (∏ k, X k ^ a k) * C (Ideal.Quotient.mk 𝔮 f) := by
  have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog hf
    (fun k => (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)))
    (fun q => C (Ideal.Quotient.mk 𝔮 (X q)))
  rw [aeval_C_mk] at h
  exact h

set_option maxHeartbeats 1000000 in

theorem ringKrullDim_ker_coneMap (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime] (p : (k : K) → ι k)
    (h1 : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = (d : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker (coneMap (K := K) 𝔮)) =
      ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let θ : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := coneMap 𝔮
  let y : (Σ k, ι k) → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    fun q => C (Ideal.Quotient.mk 𝔮 (X q))
  show ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) = _
  have : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime _
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) := Ideal.Quotient.isDomain _
  let κ : (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Ideal.kerLiftAlg θ
  have hκ : Function.Injective κ := Ideal.kerLiftAlg_injective θ
  letI : Algebra (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    κ.toRingHom.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    IsScalarTower.of_algebraMap_eq fun c => (κ.commutes c).symm
  have hκmk : ∀ f, algebraMap (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
      (Ideal.Quotient.mk _ f) = θ f := fun f => Ideal.kerLiftAlg_mk θ f
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔮) (Ideal.Quotient.mkₐ_surjective ℂ 𝔮)
  obtain ⟨sA, hAdim, hAtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  obtain ⟨sR, hRdim, hRtr⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ))
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    (faithfulSMul_iff_algebraMap_injective ℂ _).mpr (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) :=
    (faithfulSMul_iff_algebraMap_injective ℂ _).mpr
      (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hκ
  have hT1 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) +
      trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
  have hmk1 : ∀ k, Ideal.Quotient.mk 𝔮 (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq]
    exact h1 k
  let AC := Subalgebra.algebraicClosure (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)
    (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have hRAC : ∀ f, θ f ∈ AC := fun f => by
    rw [Subalgebra.mem_algebraicClosure, ← hκmk]
    exact isAlgebraic_algebraMap _
  have hXk : ∀ k, θ (X ⟨k, p k⟩) = (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) := by
    intro k
    simp only [θ, coneMap, aeval_X, hmk1, map_one, mul_one]
  have hXq : ∀ q, θ (X q) = (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q := fun q => by
    simp only [θ, coneMap, aeval_X, y]
  have hyAC : ∀ q, y q ∈ AC := fun q => by
    have h2 := hRAC (X ⟨q.1, p q.1⟩)
    have h3 := hRAC (X q)
    rw [hXk] at h2
    rw [hXq] at h3
    exact (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero q.1))
      ((Subalgebra.mem_algebraicClosure _ _).mp h2) ((Subalgebra.mem_algebraicClosure _ _).mp h3))
  have hCAC : ∀ f : MvPolynomial (Σ k, ι k) ℂ, C (Ideal.Quotient.mk 𝔮 f) ∈ AC := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
      have h2 := hRAC (C c)
      have h3 : θ (C c) = C (Ideal.Quotient.mk 𝔮 (C c)) := by
        simp only [θ, coneMap, aeval_C, MvPolynomial.algebraMap_apply]
        rfl
      rwa [h3] at h2
    | add f g hf hg =>
      rw [map_add, map_add]
      exact AC.add_mem hf hg
    | mul_X f q hf =>
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC q)
  have hall : ∀ t : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮), t ∈ AC := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    | add f g hf hg => exact AC.add_mem hf hg
    | mul_X f k hf =>
      have h2 := hRAC (X ⟨k, p k⟩)
      rw [hXk] at h2
      exact AC.mul_mem hf h2
  have : Algebra.IsAlgebraic (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) +
      trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)
  have h0 : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = 0 :=
    trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      (Fintype.card K : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + Fintype.card K = sR := by exact_mod_cast hT1
  have hsA : sA = d := by
    rw [hAdim] at hd
    exact_mod_cast hd
  rw [hRdim, ← hnat, hsA]

end ChartSectionNotMem

open ChartSectionNotMem in

theorem ChartSectionNotMem.proof : ChartSectionNotMem.Statement := by
  classical
  intro K _ _ ι _ P e m σ i A s hP hs J hJ hmem
  obtain ⟨a, -, hsa, hsP⟩ := hs
  have hJmin := mem_segreChartComponents.1 hJ
  have : J.IsPrime := hJmin.1.1
  have hvan : ∀ f : MvPolynomial (Fin m) ℂ,
      (∀ z ∈ mcPts P, segre z i = 1 → eval (fun a => segre z (σ a)) f = 0) → f ∈ J := by
    intro f hf
    apply hJmin.1.2
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hzi, rfl⟩
    exact hf z hz hzi

  let β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval fun q => X (σ.symm (Function.update i q.1 q.2))
  have hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g := by
    intro x g
    induction g using MvPolynomial.induction_on with
    | C c => simp [β]
    | add f g hf hg => simp [hf, hg]
    | mul_X f q hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [β, chartLift]
  let 𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ) := J.comap β
  have : 𝔮.IsPrime := Ideal.comap_isPrime _ J
  have hz0 : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 → ∀ k, z ⟨k, i k⟩ ≠ 0 := fun z hz k h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hz] at this
    exact one_ne_zero this
  have h1 : ∀ k, (X ⟨k, i k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮 := by
    intro k
    show β _ ∈ J
    refine hvan _ fun z _ hzi => ?_
    rw [hβ]
    simp [chartLift, hzi]
  have hPq : ∀ g ∈ P, MvPolynomial.map (Int.castRingHom ℂ) g ∈ 𝔮 := by
    intro g hg
    show β _ ∈ J
    refine hvan _ fun z hz hzi => ?_
    rw [hβ]
    have hl : chartLift σ i (fun a => segre z (σ a)) = fun q => (z ⟨q.1, i q.1⟩)⁻¹ * z q := by
      funext q
      rw [chartLift_segre_apply σ i z hzi q.1 q.2, mul_comm]
    rw [hl]
    exact (ReciprocityTheory.ChartRestriction.G.Geo.mcPts_smul hP.2.1.2.1 (fun k => (z ⟨k, i k⟩)⁻¹)
      (fun k => inv_ne_zero (hz0 z hzi k)) hz).2 g hg
  have hs𝔮 : MvPolynomial.map (Int.castRingHom ℂ) s ∈ 𝔮 := hmem

  have hd𝔮 : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = (e : WithBot ℕ∞) := by
    let ψ : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ ⧸ J :=
      (Ideal.Quotient.mk J).comp β.toRingHom
    have hker : RingHom.ker ψ = 𝔮 := by
      ext f
      simp [ψ, 𝔮, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hXa : ∀ a : Fin m, ∃ g, ψ g = Ideal.Quotient.mk J (X a) := by
      intro a
      refine ⟨∏ k, X ⟨k, σ a k⟩, ?_⟩
      show Ideal.Quotient.mk J (β _) = _
      rw [Ideal.Quotient.eq]
      refine hvan _ fun z _ hzi => ?_
      have hc := congrFun (segre_chartLift σ i z hzi) (σ a)
      rw [map_sub, hβ, eval_X, map_prod]
      simp only [eval_X]
      rw [show ∏ x, chartLift σ i (fun a => segre z (σ a)) ⟨x, σ a x⟩ =
        segre (chartLift σ i (fun a => segre z (σ a))) (σ a) from rfl, hc, sub_self]
    have hsurj : Function.Surjective ψ := by
      intro x
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      induction f using MvPolynomial.induction_on with
      | C c => exact ⟨C c, by simp [ψ, β]⟩
      | add f g hf hg =>
        obtain ⟨f', hf'⟩ := hf
        obtain ⟨g', hg'⟩ := hg
        exact ⟨f' + g', by rw [map_add, hf', hg', map_add]⟩
      | mul_X f a hf =>
        obtain ⟨f', hf'⟩ := hf
        obtain ⟨g', hg'⟩ := hXa a
        exact ⟨f' * g', by rw [map_mul, hf', hg', map_mul]⟩
    rw [← hker, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)]
    exact SegreChartDim.proof K ι P e m σ i hP J hJ

  set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
  have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  have : PQ.IsPrime := hvar.1.isPrime
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
    rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      congr 1
    · simp
  have hdim : ∀ Q ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hext] at hQ
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]
    exact hvar.2
  have : P.IsPrime := hP.2.1.1
  have hch : ∀ n : ℤ, (C n : MRing ι) ∈ P → n = 0 := by
    intro n hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr hn
    rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at hn'
    exact hn'
  have hcomapQ : PQ.comap (MvPolynomial.map (Int.castRingHom ℚ)) = P :=
    (ReciprocityTheory.AnForm.R.extQ_spec P hch).2.1
  have hsQ : ∀ Q ∈ PC.minimalPrimes, MvPolynomial.map (Int.castRingHom ℂ) s ∉ Q := by
    intro Q hQ hsQ
    rw [← hext] at hQ
    have hc := ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC PQ Q hQ
    apply hsP
    rw [← hcomapQ, Ideal.mem_comap, ← hc, Ideal.mem_comap, MvPolynomial.map_map,
      show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    exact hsQ

  have hθP : PC ≤ RingHom.ker (coneMap (K := K) 𝔮) := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    have hPC' : PC = Ideal.span (MvPolynomial.map (Int.castRingHom ℂ) '' S) := by
      rw [hPC, hPS, Ideal.map_span]
    rw [hPC', Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    have hfq : MvPolynomial.map (Int.castRingHom ℂ) f ∈ 𝔮 := hPq f (by rw [hPS]; exact Ideal.subset_span hf)
    rw [SetLike.mem_coe, RingHom.mem_ker, coneMap_of_isMultiHomog 𝔮
      (fun d hd k => hb d (MvPolynomial.support_map_subset _ _ hd) k),
      Ideal.Quotient.eq_zero_iff_mem.mpr hfq, map_zero, mul_zero]
  have hsθ : MvPolynomial.map (Int.castRingHom ℂ) s ∈ RingHom.ker (coneMap (K := K) 𝔮) := by
    rw [RingHom.mem_ker, coneMap_of_isMultiHomog 𝔮
      (fun d hd k => hsa d (MvPolynomial.support_map_subset _ _ hd) k),
      Ideal.Quotient.eq_zero_iff_mem.mpr hs𝔮, map_zero, mul_zero]
  have : (RingHom.ker (coneMap (K := K) 𝔮)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hQθ⟩ := Ideal.exists_minimalPrimes_le hθP
  have : Q.IsPrime := hQ.1.1
  obtain ⟨W, hW, hWθ⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hQθ ((Ideal.span_singleton_le_iff_mem _).2 hsθ))
  have hpit := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Σ k, ι k) Q W _ hQ.1.1 (hsQ Q hQ) hW
  rw [hdim Q hQ] at hpit
  have hle : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker (coneMap (K := K) 𝔮)) ≤
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hWθ) fun x => by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk W f, rfl⟩
  rw [ringKrullDim_ker_coneMap 𝔮 i h1 e hd𝔮] at hle
  have h2 : ((e + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    calc ((e + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) + 1 := by
          gcongr
      _ = _ := hpit
  have h3 : e + Fintype.card K + 1 ≤ e + Fintype.card K := by exact_mod_cast h2
  omega

end GroundTheory.Heights₂.Heights.Targets
