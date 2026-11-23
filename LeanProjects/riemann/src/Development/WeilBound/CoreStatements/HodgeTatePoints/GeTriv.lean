import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.FrameExpandLoc
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Ge

theorem chartMon_ne_zero {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {s : ∀ k, J k} (hs : mseg y s ≠ 0) (a : K → ℤ) : chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

theorem trivflag_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [CharZero Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R m j k : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R (j + k) V) (σ : E →+* Ω) (d : Ω) (dd : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, chartRing o (mseg y) s.1) (i : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)) →ₗ[chartRing o (mseg y) s.1] (Fin (j + k) → chartRing o (mseg y) s.1)) (bW : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin j) (chartRing o (mseg y) s.1) (Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)))) (bM : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin k) (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) (wW : Fin j → Module.Dual Ω V) (wM : Fin k → V) (b : Fin (j + k) → K → ℤ), (∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, IsFractionRing (chartRing o (mseg y) s.1) Ω) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) (a : 𝓞 E), σ' (a : E) ∈ chartRing o (mseg y) s.1) → (∀ s, (dd s : Ω) = d ∧ GeneratesDiff σ (dd s)) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ ∧ (Dc s).e = (Dc t).e) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ') → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ (Dc t).omHT σ', (mseg y s.1 / mseg y t.1) ^ n • eigProj (Dc t).ρΩ σ' ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ m) • z) → (∀ s, (Dc s).IsDualMap σ (dd s) m (i s) ∧ (Dc s).ExactMod σ m (i s) ∧ ∀ x, (Dc s).q σ x ∈ (Dc s).omHT σ) → m ≤ R → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin j → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.castAdd k a)) ∧ ∀ z : (Dc s).omHT (σ.comp c.toRingHom), ((bW s a z : chartRing o (mseg y) s.1) : Ω) = ∑ a', cf a' * wW a' z) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin k → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.natAdd j a)) ∧ ((bM s a : (Dc s).omHT σ) : V) = ∑ a', cf a' • wM a') → Num.TrivFlagMod o ((p : o) ^ m) y (j + k) b := by
  intro o _ Ω _ _ K _ J _ y _ E _ _ c hc p R m j k _ V _ _ Dc σ d dd i bW bM wW wM b hfr hint hdd hρe hM hh hi hm
    hW hMb
  classical
  have hfe := fun s => frame_exists _ Ω Subtype.val_injective E c hc p R (j + k) V (Dc s) σ m j k (i s) (bW s) (bM s)
    finSumFinEquiv (hi s).2.2 (hi s).2.1
  choose g hg using fun s => (hfe s).1
  choose cf cf1 cf2 cf3 using hW
  have hϖ : algebraMap o Ω ((p : o) ^ m) = (p : Ω) ^ m := by simp
  refine ⟨fun s => if h : mseg y s ≠ 0 then
    ((g ⟨s, h⟩).map (fun a => (a : Ω))).submatrix id finSumFinEquiv.symm else 0, fun s hs => ?_,
    fun s t hs ht => ?_⟩
  · simp only [dif_pos hs]
    refine ⟨fun a a' => (g ⟨s, hs⟩ _ _).2, ?_⟩
    obtain ⟨h, r, e⟩ := (hfe ⟨s, hs⟩).2 _ (hg ⟨s, hs⟩)
    refine ⟨h, h.2, r, r.2, ?_⟩
    have := congrArg (chartRing o (mseg y) s).val e
    rw [map_mul, AlgHom.map_det] at this
    rw [hϖ, Matrix.submatrix_map]
    simpa using this
  · simp only [dif_pos hs, dif_pos ht, hϖ]
    haveI := hfr ⟨t, ht⟩
    have hu := div_mem_chartRing (o := o) (mseg y) t s
    have hu0 : mseg y s / mseg y t ≠ 0 := div_ne_zero hs ht
    have hAL : ∀ a ∈ chartRing o (mseg y) s, a ∈ loc _ _ hu := fun a ha =>
      exists_pow_mul_mem_chartRing (mseg y) s t hs ha
    obtain ⟨T, T1, T2, T3⟩ := tri wW (fun a => ∑ a', cf ⟨s, hs⟩ a a' • wW a') (fun a => ∑ a', cf ⟨t, ht⟩ a a' • wW a')
      (fun a => chartMon y s (b (Fin.castAdd k a))) (fun a => chartMon y t (b (Fin.castAdd k a)))
      (fun a => chartMon_ne_zero ht _) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩)
    obtain ⟨S, S1, S2, S3⟩ := tri wM (fun a => (bM ⟨s, hs⟩ a : V)) (fun a => (bM ⟨t, ht⟩ a : V))
      (fun a => chartMon y s (b (Fin.natAdd j a))) (fun a => chartMon y t (b (Fin.natAdd j a)))
      (fun a => chartMon_ne_zero ht _) (hMb ⟨s, hs⟩) (hMb ⟨t, ht⟩)
    obtain ⟨X, Z, hU, hZ, e⟩ := overlap (hu := hu) hc hu0 hAL (Dc ⟨s, hs⟩) (Dc ⟨t, ht⟩) hm (hint ⟨t, ht⟩ σ)
      (dd ⟨s, hs⟩) (dd ⟨t, ht⟩) ((hdd _).1.trans (hdd _).1.symm) (hdd _).2 (hρe _ _).1 (hρe _ _).2
      (hM ⟨s, hs⟩ ⟨t, ht⟩ σ) (by rw [inv_div]; exact hM ⟨t, ht⟩ ⟨s, hs⟩ _) (hh ⟨s, hs⟩ ⟨t, ht⟩)
      (hi _).1 (hi _).1 (hi _).2.1 (hg _) (hg _) _ _
      (fun a z => by rw [cf3]; simp) (fun a z => by rw [cf3]; simp) T T3 S S3
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := (((Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hU a a')).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hZ a a'))).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hAL _ (g ⟨s, hs⟩ a a').2))).exists
    refine ⟨n, (mseg y s / mseg y t) ^ n •
      (Matrix.fromBlocks T X 0 S).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      (mseg y s / mseg y t) ^ n • Z.submatrix id finSumFinEquiv.symm, fun a a' => h1 _ _, fun a a' => h2 _ _,
      fun a a' h => ?_, fun a => ?_, fun a a' => h3 _ _, ?_⟩
    · rw [Matrix.smul_apply, Matrix.submatrix_apply]
      refine smul_eq_zero_of_right _ ?_
      induction a using Fin.addCases with
      | left a =>
        induction a' using Fin.addCases with
        | left a' => simpa using T1 a a' h
        | right a' =>
          have : j + (a' : ℕ) < a := h
          omega
      | right a =>
        induction a' using Fin.addCases with
        | left a' => simp
        | right a' => simpa using S1 a a' (by simpa using h)
    · rw [Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
      congr 1
      induction a using Fin.addCases with
      | left a => simpa using T2 a
      | right a => simpa using S2 a
    · rw [Matrix.mul_smul, smul_comm, ← smul_add, Matrix.submatrix_mul_equiv, e]
      rfl

end PositivityTheory.HtPt.Ge
