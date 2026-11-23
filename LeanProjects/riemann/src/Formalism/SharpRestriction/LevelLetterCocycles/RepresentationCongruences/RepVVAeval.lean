import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InFPOfMul

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundRep

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
  {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL}

theorem RepVV_smulA {a₀ : LetA O n} (ha₀ : a₀ ∈ W.AΔ) {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a₀ • x) (fun k => algebraMap (LetA O n) W.EE a₀ * f k) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  refine ⟨κ, κ', Hh, fun k => a₀ * a k, hH, fun k => ⟨W.AΔ.mul_mem ha₀ (ha k).1, ?_⟩,
    a₀ • y, Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W ha₀ hy, ?_⟩
  · rw [map_mul, ← (ha k).2]
    ring
  · have hsum : ∑ k, (a₀ * a k) • ((W.φD T) ^ e) (Hh k) = a₀ • ∑ k, a k • ((W.φD T) ^ e) (Hh k) := by
      rw [Finset.smul_sum]
      simp only [smul_smul]
    rw [hsum]
    have e1 : lA W ^ κ' • (lA W ^ κ • Λ • a₀ • x - a₀ • ∑ k, a k • ((W.φD T) ^ e) (Hh k)) =
        a₀ • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
      rw [smul_comm Λ a₀ x, smul_comm (lA W ^ κ) a₀, ← smul_sub, smul_comm (lA W ^ κ') a₀]
    rw [e1, hxy, smul_comm]

theorem RepVV_smulO (o : O) {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (o • x) (fun k => algebraMap O W.EE o * f k) := by
  have h1 := RepVV_smulA W (W.AΔ.algebraMap_mem o) h
  have hx : o • x = algebraMap O (LetA O n) o • x := (algebraMap_smul (LetA O n) o x).symm
  have hf : (fun k => algebraMap O W.EE o * f k) =
      fun k => algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) o) * f k := by
    funext k
    rw [← IsScalarTower.algebraMap_apply]
  rw [hx, hf]
  exact h1

theorem RepVV_zero {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol 0 (fun _ => 0) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  refine ⟨κ, κ', Hh, fun _ => 0, hH, fun k => ⟨W.AΔ.zero_mem, by simp⟩,
    (0 : LetA O n) • y, Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W W.AΔ.zero_mem hy, by simp⟩

theorem RepVV_sum (h0 : RepVV W T c' e M Λ b sol 0 (fun _ => 0)) {ι : Type} (s : Finset ι)
    (x : ι → W.DD T) (f : ι → Fin d → W.EE) (h : ∀ i ∈ s, RepVV W T c' e M Λ b sol (x i) (f i)) :
    RepVV W T c' e M Λ b sol (∑ i ∈ s, x i) (fun k => ∑ i ∈ s, f i k) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using h0) ?_
  intro j s hj ih h
  have := Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.RepVV_add W (h j (Finset.mem_insert_self j s))
    (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  simpa [Finset.sum_insert hj] using this

theorem RepVV_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (W.γ T x) (fun k => W.γE W.gam (f k)) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  obtain ⟨R, hR, R', hR', hRR', hΛR⟩ := hΛ
  obtain ⟨u, hu, hu'⟩ := hpi0
  obtain ⟨u₂, hu₂, hM'⟩ := hM
  have hγH : ∀ k, ∃ z, Formalism.MainNotions.LiftingTheory.InNΔi W T c' z ∧ W.γ T (Hh k) = Hh k + W.π₀ ^ M • z := by
    intro k
    obtain ⟨yy, hyy, hHk⟩ := hH k
    obtain ⟨z, hz, hzeq⟩ := (hb.2 k).1 M κ yy hyy
    refine ⟨z, hz, ?_⟩
    rw [hHk]
    rw [smul_zero, sub_zero, sub_eq_iff_eq_add] at hzeq
    rw [hzeq, add_comm]
  choose z hz hγz using hγH
  have hZ : ∑ k, W.γA W.gam (a k) • ((W.φA ^ e) (W.π₀ ^ M) • ((W.φD T) ^ e) (z k)) =
      (W.π₀ * Λ ^ 2) • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, hM', smul_smul, smul_smul]
    congr 1
    ring
  have h1 := congrArg (W.γ T) hxy
  simp only [γ_smul W, map_sub, map_sum, γA_lA W, γ_φpow W, hγz, map_add, φpow_smulA W, smul_add,
    Finset.sum_add_distrib, hΛR] at h1
  rw [hZ, map_mul, map_pow, hu', hΛR] at h1
  have hlA : lA W ∈ W.AΔ := by
    unfold lA
    exact W.AΔ.natCast_mem _
  refine ⟨κ, κ', Hh, fun k => R' * W.γA W.gam (a k), hH,
    fun k => ⟨W.AΔ.mul_mem hR' (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_mem W _ (ha k).1), ?_⟩,
    (R' * u * R ^ 2) • W.γ T y + lA W ^ κ' • R' • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k),
    AddSubgroup.add_mem _
      (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.mul_mem (W.AΔ.mul_mem hR' hu) (W.AΔ.pow_mem hR 2))
        (γ_Pp W hT hP2 hy))
      (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.pow_mem hlA κ')
        (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W hR' (AddSubgroup.sum_mem _ fun k _ =>
          Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.mul_mem (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_mem W _ (ha k).1) hu₂)
            (AddSubgroup.subset_closure ⟨1, W.AΔ.one_mem, z k, hz k, (one_smul _ _).symm⟩)))), ?_⟩
  · have h2 := congrArg (W.γE W.gam) (ha k).2
    rw [map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γE_ι W, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γE_ι W, hΛR, map_mul] at h2
    have h3 : algebraMap (LetA O n) W.EE R' * algebraMap (LetA O n) W.EE R = 1 := by
      rw [← map_mul, mul_comm, hRR', map_one]
    rw [map_mul, ← h2]
    linear_combination (-(algebraMap (LetA O n) W.EE Λ * W.γE W.gam (f k))) * h3
  · have hsH : ∑ k, (R' * W.γA W.gam (a k)) • ((W.φD T) ^ e) (Hh k) =
        R' • ∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (Hh k) := by
      rw [Finset.smul_sum]
      simp only [smul_smul]
    have hΛ1 : lA W ^ κ • Λ • W.γ T x = lA W ^ κ • ((R' * R) * Λ) • W.γ T x := by
      rw [mul_comm R' R, hRR', one_mul]
    rw [hsH, hΛ1]
    calc _ = R' • (lA W ^ κ' • (lA W ^ κ • (R * Λ) • W.γ T x -
            (∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (Hh k) +
              (W.π₀ * Λ ^ 2) • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k)))) +
          (W.π₀ * Λ ^ 2) • (lA W ^ κ' • R' • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k)) := by
          simp only [smul_sub, smul_add, smul_smul]
          ring_nf
          abel
      _ = _ := by
          rw [h1]
          simp only [smul_add, smul_smul]
          ring_nf

theorem RepVV_iter (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) (i : ℕ) :
    RepVV W T c' e M Λ b sol ((W.γ T)^[i] x) (fun k => (W.γE W.gam)^[i] (f k)) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have := RepVV_γ W hT hP2 hpi0 hb hΛ hM ih
    simpa [Function.iterate_succ_apply'] using this

theorem RepVV_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) (P : Polynomial O) :
    RepVV W T c' e M Λ b sol (Polynomial.aeval (W.γ T) P x)
      (fun k => Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (f k)) := by
  rw [aeval_eq W P x]
  have hf : (fun k => Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (f k)) =
      fun k => ∑ i ∈ Finset.range (P.natDegree + 1),
        algebraMap O W.EE (P.coeff i) * (W.γE W.gam)^[i] (f k) := by
    funext k
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Module.End.pow_apply, Algebra.smul_def]
    rfl
  rw [hf]
  exact RepVV_sum W (RepVV_zero W h) _ _ (fun i k => algebraMap O W.EE (P.coeff i) * (W.γE W.gam)^[i] (f k))
    fun i _ => RepVV_smulO W (P.coeff i) (RepVV_iter W hT hP2 hpi0 hb hΛ hM h i)

end Formalism.MainNotions.N.Ln17.PCutBoundRep
