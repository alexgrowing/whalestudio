import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.Rs.JSqIntGlue

section Tor

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem posIdele_congr {a b : ℝ} (h : a = b) (ha : 0 < a) (hb : 0 < b) :
    GroundTheory.Automorphic.Reduction.posIdele (K := K) a ha = GroundTheory.Automorphic.Reduction.posIdele (K := K) b hb := by
  subst h; rfl

theorem tor_add (x y : Fin n → ℝ) : An.tor K (x + y) = An.tor K x * An.tor K y := by
  unfold An.tor
  rw [← map_mul]
  congr 1
  funext i
  rw [Pi.mul_apply, GroundTheory.Automorphic.Reduction.posIdele_mul]
  exact posIdele_congr (by rw [Pi.add_apply, Real.exp_add]) _ _

theorem continuous_tor : Continuous fun x : Fin n → ℝ => An.tor K x := by
  have hp : Continuous fun r : {r : ℝ // 0 < r} => GroundTheory.Automorphic.Reduction.posIdele (K := K) r.1 r.2 :=
    GroundTheory.Automorphic.Reduction.continuous_posIdele_subtype
  have hq : ∀ i : Fin n, Continuous fun x : Fin n → ℝ =>
      GroundTheory.Automorphic.Reduction.posIdele (K := K) (Real.exp (x i)) (Real.exp_pos _) := fun i =>
    hp.comp (f := fun x : Fin n → ℝ => (⟨Real.exp (x i), Real.exp_pos _⟩ : {r : ℝ // 0 < r}))
      ((Real.continuous_exp.comp (continuous_apply i)).subtype_mk _)
  have hd : Continuous fun x : Fin n → ℝ => GroundTheory.Automorphic.Reduction.diagUnits n
      (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := K) (Real.exp (x i)) (Real.exp_pos _)) :=
    (GroundTheory.Automorphic.Reduction.continuous_diagUnits n).comp (continuous_pi hq)
  exact hd

theorem aR_add (r : ℕ) (s t : ℝ) : An.aR K n r (s + t) = An.aR K n r s * An.aR K n r t := by
  unfold An.aR
  rw [← tor_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  split_ifs <;> simp

theorem continuous_aR (r : ℕ) : Continuous fun t : ℝ => An.aR K n r t := by
  unfold An.aR
  refine continuous_tor.comp (continuous_pi fun i => ?_)
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem continuous_ctn_comp {φ : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ) (r : ℕ)
    {h : ℝ → GroundTheory.Automorphic.AdelicGLn.AdelicGL K n} (hh : Continuous h) :
    Continuous fun t => An.ctn r φ (h t) := by
  unfold An.ctn
  refine continuous_const.mul ?_
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  have e : ∀ t, GroundTheory.Automorphic.AutomorphicForm.constantTerm r φ (h t) =
      ∫ X in C, φ (GroundTheory.Automorphic.AutomorphicForm.unipGL X * h t) ∂((GroundTheory.Automorphic.AutomorphicForm.unipMeasure K n r).restrict
        (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain K n r)) := by
    intro t
    rw [Measure.restrict_restrict' GroundTheory.Automorphic.AutomorphicForm.measurableSet_unipFundamentalDomain,
      Set.inter_eq_right.2 hDC]
    rfl
  simp only [e]
  have hc : Continuous (Function.uncurry fun (t : ℝ) (X : GroundTheory.Automorphic.AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) =>
      φ (GroundTheory.Automorphic.AutomorphicForm.unipGL X * h t)) :=
    hφ.comp ((GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL.comp continuous_snd).mul (hh.comp continuous_fst))
  exact continuous_parametric_integral_of_continuous hc hC

end Tor

theorem setLIntegral_le_of_cover {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] {μ : Measure α}
    [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ] [Countable Γ] {D S : Set α}
    (hD : IsFundamentalDomain Γ D μ) (hS : ∀ x, ∃ g : Γ, g • x ∈ S) (f : α → ℝ≥0∞)
    (hf : ∀ (g : Γ) x, f (g • x) = f x) : ∫⁻ x in D, f x ∂μ ≤ ∫⁻ x in S, f x ∂μ := by
  have hsub : D ⊆ ⋃ g : Γ, (g • S ∩ D) := by
    intro x hx
    obtain ⟨g, hg⟩ := hS x
    exact Set.mem_iUnion.2 ⟨g⁻¹, ⟨g • x, hg, by simp⟩, hx⟩
  calc ∫⁻ x in D, f x ∂μ ≤ ∫⁻ x in ⋃ g : Γ, (g • S ∩ D), f x ∂μ := lintegral_mono_set hsub
    _ ≤ ∑' g : Γ, ∫⁻ x in g • S ∩ D, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : Γ, ∫⁻ x in g • S ∩ D, f (g⁻¹ • x) ∂μ := by simp only [hf]
    _ = ∫⁻ x in S, f x ∂μ := (hD.setLIntegral_eq_tsum' f S).symm

theorem exists_lt_of_finset (s : Finset ℂ) (ρ : ℝ) (h : ∀ z ∈ s, ‖z‖ < Real.exp ρ) :
    ∃ κ < ρ, ∀ z ∈ s, ‖z‖ < Real.exp κ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨ρ - 1, by linarith, by simp⟩
  | insert a s ha ih =>
    obtain ⟨κ, hκ, hs⟩ := ih fun z hz => h z (Finset.mem_insert_of_mem hz)
    have ha' := h a (Finset.mem_insert_self a s)
    set m : ℝ := max ‖a‖ (Real.exp (ρ - 1)) with hm
    have hm0 : 0 < m := lt_max_of_lt_right (Real.exp_pos _)
    have hmρ : m < Real.exp ρ := max_lt ha' (Real.exp_lt_exp.2 (by linarith))
    have hlog : Real.log m < ρ := (Real.log_lt_iff_lt_exp hm0).2 hmρ
    refine ⟨max κ ((Real.log m + ρ) / 2), max_lt hκ (by linarith), fun z hz => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · calc ‖z‖ ≤ m := le_max_left _ _
        _ < Real.exp ((Real.log m + ρ) / 2) := (Real.log_lt_iff_lt_exp hm0).1 (by linarith)
        _ ≤ _ := Real.exp_le_exp.2 (le_max_right _ _)
    · exact (hs z hz).trans_le (Real.exp_le_exp.2 (le_max_left _ _))

section Cover

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem exists_mem_slab (hS : ∀ t, splitCentre E N t = An.tor E fun _ => t) (hL : latticeGL E N = An.lat E N)
    {ω : Set (GA E N)} {t : ℝ} (ht : 0 < t)
    (hsieg : ∀ g : GroundTheory.Automorphic.AdelicGLn.AdelicGL E N, ∃ γ : GL (Fin N) E,
      GroundTheory.Automorphic.AdelicGLn.diagonal E N γ * g ∈ GroundTheory.Automorphic.Reduction.siegelSet N ω t)
    (g : GA E N) : ∃ γ ∈ latticeGL E N, γ * g ∈ An.slab ω (max 0 (-Real.log t)) := by
  obtain ⟨γ, hγ⟩ := hsieg g
  obtain ⟨b, hb, _, ⟨r, hr, hratio, rfl⟩, k, hk, hg⟩ := hγ
  set x : Fin N → ℝ := fun i => Real.log (r i) with hx
  have ha : GroundTheory.Automorphic.Reduction.diagUnits N (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (r i) (hr i)) =
      An.tor E x := by
    unfold An.tor
    congr 1
    funext i
    exact posIdele_congr (Real.exp_log (hr i)).symm _ _
  set m : ℤ := if h : 0 < N then ⌊x ⟨N - 1, by omega⟩⌋ else 0 with hm
  set c : ℝ := ((-m : ℤ) : ℝ) with hc
  refine ⟨splitCentre E N c * GroundTheory.Automorphic.AdelicGLn.diagonal E N γ, ?_, ?_⟩
  · refine mul_mem ?_ ?_
    · rw [hc, splitCentre_intCast]
      exact zpow_mem_latticeGL _
    · rw [hL]
      exact Subgroup.mem_sup_left ⟨γ, rfl⟩
  · have e : splitCentre E N c * GroundTheory.Automorphic.AdelicGLn.diagonal E N γ * g =
        b * An.tor E (fun i => c + x i) * k := by
      rw [mul_assoc, hg, ha, ← mul_assoc, ← mul_assoc, splitCentre_comm, mul_assoc b, hS, ← tor_add]
      rfl
    refine ⟨b, hb, fun i => c + x i, fun r' => ?_, fun i hi => ?_, k, hk, e⟩
    · unfold An.sr
      split_ifs with h
      · have h1 := hratio ⟨r' - 1, by omega⟩ ⟨r', h.2⟩ (by simp only; omega)
        have h2 := Real.log_le_log (mul_pos ht (hr _)) h1
        rw [Real.log_mul ht.ne' (hr _).ne'] at h2
        have h3 : -max 0 (-Real.log t) ≤ Real.log t := by
          have := le_max_right 0 (-Real.log t); linarith
        simp only [hx]
        linarith
      · have := le_max_left 0 (-Real.log t); linarith
    · have hN : 0 < N := by omega
      have hi' : i = ⟨N - 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [hi']
      have hmN : m = ⌊x ⟨N - 1, by omega⟩⌋ := by rw [hm, dif_pos hN]
      have hc' : c = -(⌊x ⟨N - 1, by omega⟩⌋ : ℝ) := by rw [hc, hmN]; push_cast; ring
      rw [hc']
      constructor
      · linarith [Int.floor_le (x ⟨N - 1, by omega⟩)]
      · linarith [Int.lt_floor_add_one (x ⟨N - 1, by omega⟩)]

end Cover

end PositivityTheory.Rg.Rs.JSqIntGlue

namespace PositivityTheory.Rg.Rs

open JSqIntGlue in
theorem sqIntGlue_holds : SqIntGlue := by
  intro hDict hNice hInit hFin hKill hBoot hSlab E _ _ _ N φ hφ hcen hexp
  obtain ⟨hA, hS, hL, hCT⟩ := hDict E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := hNice E N φ hφ hcen'
  obtain ⟨M, hM⟩ := hInit E N φ hφ hcen'
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hk : ∀ r, ∃ κ : ℝ, 0 < r → r < N → κ < An.rho E N r ∧ ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨0, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
    obtain ⟨hr0, hrN⟩ := hr
    have hct := (hCT φ hφ r hr0 hrN).1
    have hfin := hFin E N φ hφ r hr0 hrN _ hct
    have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => by
      rw [hA, hA, hA]; exact aR_add r s t
    have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
      intro g
      have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
        funext fun t => by rw [hA]
      rw [e]
      exact continuous_ctn_comp hnice.cont r ((continuous_aR r).mul continuous_const)
    obtain ⟨p, hp, hpk, hroots⟩ := hKill (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
    have hroot' : ∀ z ∈ p.roots.toFinset, ‖z‖ < Real.exp (An.rho E N r) := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hp.ne_zero] at hz
      obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
      have hc : c ∈ Exp r φ.1 := ⟨_, hct, F, hF, hF0, hFe⟩
      have h1 := hexp r hr0 hrN c hc
      unfold pE at h1
      rw [Complex.norm_exp]
      refine Real.exp_lt_exp.2 ?_
      have h2 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
      have h3 := (div_lt_iff₀ hd).1 h2
      unfold An.rho
      calc c.re < (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
        _ = _ := by ring
    obtain ⟨κ, hκ, hκz⟩ := exists_lt_of_finset _ _ hroot'
    refine ⟨κ, fun _ _ => ⟨hκ, p, hp, fun g => ?_, fun z hz => hκz z ?_⟩⟩
    · have := hpk g
      simpa only [hA] using this
    · rw [Multiset.mem_toFinset, mem_roots hp.ne_zero]
      exact hz
  choose κ hκ using hk
  have hB := hBoot E N φ.1 M κ hnice hM fun r h1 h2 => (hκ r h1 h2).2
  have hleft : ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
    let S : Subgroup (GA E N) :=
      { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
        one_mem' := fun g => by rw [one_mul]
        mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
        inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
    have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact hφ.left γ) (Subgroup.zpowers_le.2 (hcen 1))
    exact this
  have hfd := isFundamentalDomain_stdDom (latticeGL E N) (Measure.haar : Measure (GA E N))
  refine ⟨hcen, Measure.haar, _, inferInstance, hfd, ?_⟩
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  have hslab := hSlab E N Measure.haar φ.1 κ hnice.cont hB (fun r h1 h2 => (hκ r h1 h2).1) ω hω hωB
    (max 0 (-Real.log t))
  refine lt_of_le_of_lt ?_ hslab
  have : MeasurableConstSMul (latticeGL E N) (GA E N) := ⟨fun γ => measurable_const_mul (γ : GA E N)⟩
  have : SMulInvariantMeasure (latticeGL E N) (GA E N) (Measure.haar : Measure (GA E N)) :=
    ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  refine setLIntegral_le_of_cover hfd (fun g => ?_) _ (fun γ g => ?_)
  · obtain ⟨γ, hγ, h⟩ := exists_mem_slab hS hL ht hsieg g
    exact ⟨⟨γ, hγ⟩, h⟩
  · show ‖φ.1 (γ.1 * g)‖ₑ ^ 2 = ‖φ.1 g‖ₑ ^ 2
    rw [hleft γ.1 γ.2 g]

end PositivityTheory.Rg.Rs

end
