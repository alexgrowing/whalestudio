import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphMetric
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphFactor
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftGraphMetric

theorem pderiv_rename_of_injective {σ τ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f)
    (x : σ) (p : MvPolynomial σ R) : pderiv (f x) (rename f p) = rename f (pderiv x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, rename_X, Derivation.leibniz, hp, smul_eq_mul, map_add]
    congr 1
    rw [pderiv_X, pderiv_X]
    by_cases hnx : n = x
    · subst hnx; simp
    · rw [Pi.single_eq_of_ne (hf.ne hnx), Pi.single_eq_of_ne hnx]; simp

theorem pderiv_rename_of_not_mem_range {σ τ R : Type*} [CommSemiring R] {f : σ → τ} {t : τ}
    (ht : t ∉ Set.range f) (p : MvPolynomial σ R) : pderiv t (rename f p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    have hne : f n ≠ t := fun h => ht ⟨n, h⟩
    simp only [map_mul, rename_X, Derivation.leibniz, hp, smul_eq_mul]
    rw [pderiv_X, Pi.single_eq_of_ne hne]
    simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}

def oldEmb (r : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι r k) := fun p => ⟨some p.1, p.2⟩

theorem oldEmb_injective : Function.Injective (oldEmb (ι := ι) r) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj h).2
  subst h2
  rfl

def oldCLM (r : ℕ) : ((Σ k, addIdx ι r k) → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (oldEmb r p)

theorem oldCLM_apply (z : (Σ k, addIdx ι r k) → ℂ) : oldCLM r z = basePart₂ z := rfl

theorem isOpen_allNZ {κ : Type} [Fintype κ] {ρ : κ → Type} :
    IsOpen {z : (Σ k, ρ k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ρ k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

variable {Ω : Type} [Field Ω]

theorem rename_mem_mCoordIdeal (y : (Σ k, ι k) → Ω) (v : Fin r → Ω) {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) : rename (oldEmb r) f ∈ mCoordIdeal (addBlock y v) := by
  rw [mCoordIdeal, RingHom.mem_ker] at hf ⊢
  have key : ∀ g : MRing ι, mConeMap (addBlock y v) (rename (oldEmb r) g) = rename some (mConeMap y g) := by
    intro g
    simp only [mConeMap, aeval_rename]
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, aeval_X, hp, Function.comp_apply, rename_C, rename_X]
      rfl
  rw [key, hf, map_zero]

theorem oldPart_mem_mcPts {y : (Σ k, ι k) → Ω} {v : Fin r → Ω} {z : (Σ k, addIdx ι r k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (some k), fun f hf => ?_⟩
  have h := hz.2 _ (rename_mem_mCoordIdeal y v hf)
  rw [map_rename, eval_rename] at h
  exact h

theorem isConeTangent_oldPart {y : (Σ k, ι k) → Ω} {v : Fin r → Ω} {P0 : Ideal (MRing ι)}
    (hP0 : P0 ≤ mCoordIdeal y) {z ξ : (Σ k, addIdx ι r k) → ℂ}
    (hξ : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z ξ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (basePart₂ z) (basePart₂ ξ) := by
  intro f hf
  have h := hξ _ (rename_mem_mCoordIdeal y v (hP0 hf))
  rw [map_rename] at h
  have hnone : ∀ i : Fin r, pderiv (⟨none, i⟩ : Σ k, addIdx ι r k)
      (rename (oldEmb r) (map (Int.castRingHom ℂ) f)) = 0 := by
    intro i
    refine pderiv_rename_of_not_mem_range ?_ _
    rintro ⟨p, hp⟩
    exact Option.some_ne_none _ (congrArg Sigma.fst hp)
  have hsum : ∑ q : (Σ k, addIdx ι r k),
      eval z (pderiv q (rename (oldEmb r) (map (Int.castRingHom ℂ) f))) * ξ q =
      ∑ p : (Σ k, ι k), eval (basePart₂ z) (pderiv p (map (Int.castRingHom ℂ) f)) * basePart₂ ξ p := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma, Fintype.sum_option]
    rw [Finset.sum_eq_zero (fun i _ => by rw [hnone i]; simp), zero_add]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have e := pderiv_rename_of_injective (oldEmb_injective (r := r)) (⟨k, i⟩ : Σ k, ι k)
      (map (Int.castRingHom ℂ) f)
    simp only [oldEmb] at e
    rw [e, eval_rename]
    rfl
  rw [← hsum]
  exact h

theorem levi_const_mul {κ : Type} [Fintype κ] {g : (κ → ℂ) → ℝ} {z : κ → ℂ} (c : ℝ)
    (hg : ContDiffAt ℝ 2 g z) (w : κ → ℂ) :
    ReciprocityTheory.AnForm.levi (fun y => c * g y) z w = c * ReciprocityTheory.AnForm.levi g z w := by
  have h := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const hg w
  simp only [zero_add] at h
  rw [h]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : κ → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  rw [h0, zero_add]

theorem proof (hF : LiftGraphFactor.Statement) : LiftGraphMetric.Statement := by
  intro K _ _ ι _ Ω _ y N P0 a r v hP0 hN hNc hv hgen
  classical
  obtain ⟨Φ, hΦs, hΦp, hΦh, hΦc, hΦv, hΦl⟩ := hF K ι Ω y N a r v hv hgen
  let U : Set ((Σ k, addIdx ι r k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  let U0 : Set ((Σ k, ι k) → ℂ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}
  let S : ((Σ k, addIdx ι r k) → ℂ) → ℝ := fun z => ∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2
  let F : ((Σ k, addIdx ι r k) → ℂ) → ℝ := fun z =>
    N.h (basePart₂ z) ^ a * Real.sqrt (S z) / Real.sqrt (Φ (basePart₂ z))
  have hUo : IsOpen U := isOpen_allNZ
  have hU0o : IsOpen U0 := isOpen_allNZ
  have hold : ∀ z ∈ U, basePart₂ z ∈ U0 := fun z hz k => hz (some k)
  have hSpos : ∀ z ∈ U, 0 < S z := by
    intro z hz
    obtain ⟨i, hi⟩ := hz none
    have hi' : 0 < ‖z ⟨none, i⟩‖ ^ 2 := by positivity
    exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun i : Fin r => ‖z ⟨none, i⟩‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  have hNpos : ∀ z ∈ U, 0 < N.h (basePart₂ z) := fun z hz => N.pos _ (hold z hz)
  have hΦpos : ∀ z ∈ U, 0 < Φ (basePart₂ z) := fun z hz => hΦp _ (hold z hz)
  have hFpos : ∀ z ∈ U, 0 < F z := fun z hz =>
    div_pos (mul_pos (pow_pos (hNpos z hz) _) (Real.sqrt_pos.2 (hSpos z hz))) (Real.sqrt_pos.2 (hΦpos z hz))
  have hmemU : ∀ c : Option K → ℂ, (∀ k, c k ≠ 0) → ∀ z : (Σ k, addIdx ι r k) → ℂ,
      ((fun p => c p.1 * z p) ∈ U ↔ z ∈ U) := by
    intro c hc z
    simp only [U, Set.mem_setOf_eq, ne_eq, mul_eq_zero, not_or]
    exact forall_congr' fun k => exists_congr fun i => and_iff_right (hc k)
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r) :=
    { a := unitDeg none
      h := fun z => if z ∈ U then F z else 0
      pos := fun z hz => by
        simp only [if_pos (show z ∈ U from hz)]
        exact hFpos z hz
      smul := by
        intro c z hc
        by_cases hz : z ∈ U
        · rw [if_pos ((hmemU c hc z).2 hz), if_pos hz]
          let c' : K → ℂ := fun k => c (some k)
          have hc' : ∀ k, c' k ≠ 0 := fun k => hc _
          have h1 : N.h (basePart₂ (fun p => c p.1 * z p)) = (∏ k, ‖c' k‖ ^ N.a k) * N.h (basePart₂ z) :=
            N.smul c' (basePart₂ z) hc'
          have h2 : Φ (basePart₂ (fun p => c p.1 * z p)) =
              (∏ k, ‖c' k‖ ^ ((a • N.a) k)) ^ 2 * Φ (basePart₂ z) :=
            hΦh c' (basePart₂ z) hc' (hold z hz)
          have h3 : S (fun p => c p.1 * z p) = ‖c none‖ ^ 2 * S z := by
            simp only [S, norm_mul, mul_pow, Finset.mul_sum]
          have hprod : ∏ k : Option K, ‖c k‖ ^ (unitDeg (none : Option K) k) = ‖c none‖ := by
            rw [Fintype.prod_option]
            simp [unitDeg]
          have hpow : (∏ k, ‖c' k‖ ^ N.a k) ^ a = ∏ k, ‖c' k‖ ^ ((a • N.a) k) := by
            rw [← Finset.prod_pow]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]
          have hPpos : 0 < ∏ k, ‖c' k‖ ^ ((a • N.a) k) :=
            Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc' k)) _
          have hs1 : Real.sqrt (S (fun p => c p.1 * z p)) = ‖c none‖ * Real.sqrt (S z) := by
            rw [h3, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
          have hs2 : Real.sqrt (Φ (basePart₂ (fun p => c p.1 * z p))) =
              (∏ k, ‖c' k‖ ^ ((a • N.a) k)) * Real.sqrt (Φ (basePart₂ z)) := by
            rw [h2, Real.sqrt_mul (by positivity), Real.sqrt_sq hPpos.le]
          have hΦ0 : 0 < Real.sqrt (Φ (basePart₂ z)) := Real.sqrt_pos.2 (hΦpos z hz)
          simp only [F]
          rw [hprod, hs1, hs2, h1, mul_pow, hpow]
          field_simp
        · rw [if_neg (mt (hmemU c hc z).1 hz), if_neg hz, mul_zero] }
  have hAh : ∀ z, A.h z = if z ∈ U then F z else 0 := fun z => rfl
  have h2le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hoR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, addIdx ι r k) → ℂ => basePart₂ z) :=
    ((oldCLM (ι := ι) r).restrictScalars ℝ).contDiff
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℂ).comp (contDiff_apply ℝ ℂ _)
  have hNs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) N.h U0 := hN.1
  have hNo : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => N.h (basePart₂ z)) U :=
    hNs.comp hoR.contDiffOn fun z hz => hold z hz
  have hΦo : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Φ (basePart₂ z)) U :=
    hΦs.comp hoR.contDiffOn fun z hz => hold z hz
  have hFs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U :=
    ((hNo.pow a).mul (hS.contDiffOn.sqrt fun z hz => (hSpos z hz).ne')).div
      (hΦo.sqrt fun z hz => (hΦpos z hz).ne') fun z hz => (Real.sqrt_pos.2 (hΦpos z hz)).ne'
  have hAs : IsSmoothHerm A := hFs.congr fun z hz => by rw [hAh, if_pos hz]
  refine ⟨A, rfl, ?_, ⟨hAs, ?_⟩, ?_⟩
  ·
    intro z
    have hmem : (fun p => (starRingEnd ℂ) (z p)) ∈ U ↔ z ∈ U := by
      simp only [U, Set.mem_setOf_eq, ne_eq, map_eq_zero]
    rw [hAh, hAh]
    by_cases hz : z ∈ U
    · rw [if_pos (hmem.2 hz), if_pos hz]
      have e1 : N.h (basePart₂ fun p => (starRingEnd ℂ) (z p)) = N.h (basePart₂ z) := hNc (basePart₂ z)
      have e2 : Φ (basePart₂ fun p => (starRingEnd ℂ) (z p)) = Φ (basePart₂ z) := hΦc (basePart₂ z)
      simp only [F, S]
      rw [e1, e2]
      simp only [Complex.norm_conj]
    · rw [if_neg (mt hmem.1 hz), if_neg hz]
  ·
    intro z hz ξ hξ
    have hzU : z ∈ U := hz.1
    have hw := oldPart_mem_mcPts hz
    have hwU : basePart₂ z ∈ U0 := hw.1
    have hev : (fun x => Real.log (A.h x)) =ᶠ[𝓝 z] fun x =>
        (a : ℝ) * Real.log (N.h (basePart₂ x)) +
          (1 / 2 : ℝ) * (Real.log (S x) + (-1 : ℝ) * Real.log (Φ (basePart₂ x))) := by
      filter_upwards [hUo.mem_nhds hzU] with x hx
      rw [hAh, if_pos hx]
      have hN0 := hNpos x hx
      have hS0 := hSpos x hx
      have hΦ0 := hΦpos x hx
      simp only [F]
      rw [Real.log_div (by positivity) (Real.sqrt_pos.2 hΦ0).ne', Real.log_mul (by positivity)
        (Real.sqrt_pos.2 hS0).ne', Real.log_pow, Real.log_sqrt hS0.le, Real.log_sqrt hΦ0.le]
      ring
    have hNlog : ContDiffAt ℝ 2 (fun w => Real.log (N.h w)) (basePart₂ z) :=
      ((hNs.contDiffAt (hU0o.mem_nhds hwU)).of_le h2le).log (N.pos _ hwU).ne'
    have hL1 : ContDiffAt ℝ 2 (fun x => Real.log (N.h (basePart₂ x))) z :=
      hNlog.comp z (hoR.contDiffAt.of_le h2le)
    have hL2 : ContDiffAt ℝ 2 (fun x => Real.log (S x)) z :=
      (hS.contDiffAt.of_le h2le).log (hSpos z hzU).ne'
    have hL3 : ContDiffAt ℝ 2 (fun x => Real.log (Φ (basePart₂ x))) z :=
      (((hΦs.contDiffAt (hU0o.mem_nhds hwU)).of_le h2le).log (hΦp _ hwU).ne').comp z
        (hoR.contDiffAt.of_le h2le)
    have hcomp : ReciprocityTheory.AnForm.levi (fun x => Real.log (N.h (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun w => Real.log (N.h w)) (basePart₂ z) (basePart₂ ξ) := by
      have h := ReciprocityTheory.AnForm.levi_comp (φ := fun w => Real.log (N.h w))
        (τ := ⇑(oldCLM (ι := ι) r)) (z := z) ξ ((oldCLM (ι := ι) r).analyticAt z) hNlog
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hsemi : 0 ≤ ReciprocityTheory.AnForm.levi (fun w => Real.log (N.h w)) (basePart₂ z) (basePart₂ ξ) :=
      hN.2 (basePart₂ z) hw (basePart₂ ξ) (isConeTangent_oldPart hP0 hξ)
    have hfac : ReciprocityTheory.AnForm.levi (fun x => Real.log (Φ (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun x => Real.log (S x)) z ξ := hΦl z hz ξ hξ
    show 0 ≤ ReciprocityTheory.AnForm.levi (fun x => Real.log (A.h x)) z ξ
    rw [ReciprocityTheory.AnForm.levi_congr hev,
      ReciprocityTheory.AnForm.levi_add_smul (f := fun x => (a : ℝ) * Real.log (N.h (basePart₂ x)))
        (1 / 2 : ℝ) (contDiffAt_const.mul hL1) (hL2.add (contDiffAt_const.mul hL3)) ξ,
      levi_const_mul (a : ℝ) hL1 ξ,
      ReciprocityTheory.AnForm.levi_add_smul (-1 : ℝ) hL2 hL3 ξ, hcomp, hfac]
    have := mul_nonneg (Nat.cast_nonneg a) hsemi
    linarith
  ·
    intro z hz j
    have hzU : z ∈ U := hz.1
    have h := hΦv z hz j
    have hΦ0 : 0 < Real.sqrt (Φ (basePart₂ z)) := Real.sqrt_pos.2 (hΦpos z hzU)
    rw [hAh, if_pos hzU]
    simp only [F]
    rw [mul_div_assoc', ← mul_assoc, h, mul_div_assoc, div_self hΦ0.ne', mul_one]

end LiftGraphMetric

end

end GroundTheory.Heights₂.Heights.Targets
