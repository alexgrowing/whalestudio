import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerCoeffNeZeroOfAdmissible
import Development.AutomorphicArithmetic.WhittakerHecke.EventuallyUnramifiedSatakeEigenOfMemCuspRep
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsPrincipalCongruenceLevelInvariant
import Development.AutomorphicArithmetic.WhittakerHecke.BaseChangeGL2CongruenceOfLevel
import Development.AutomorphicArithmetic.WhittakerHecke.UnipotentThetaMemCongruenceOfIntegral
import Development.AutomorphicArithmetic.WhittakerHecke.UnipotentConjCongruenceOfPowFive
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentTranslateOfInfiniteComponentZe
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerSumMulEqSumMulWhittaker
import Development.AutomorphicArithmetic.WhittakerHecke.SumRangeRatAdeleCharIotaMulOneSubEqIte
import Development.AutomorphicArithmetic.WhittakerHecke.HasLevelOfUnitIdeleCongruentOne
import Development.AutomorphicArithmetic.WhittakerHecke.FixedAndHeckeEigenOfFinsetLinearCombination
import Development.AutomorphicArithmetic.WhittakerHecke.UnipotentNatDivMemMaximalCompactOfNotBadPrime
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsNatMulIntegralAtAllFinitePlaces
import Development.AutomorphicArithmetic.WhittakerHecke.CongruenceElementCommuteInfEmbedding
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem ψ_add' (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

private theorem ψ_zero' : ψ (0 : A ℚ) = 1 := by simp [ψ]

private theorem ψ_neg_mul' (x : A ℚ) : ψ (-x) * ψ x = 1 := by
  rw [← ψ_add', neg_add_cancel, ψ_zero']

private theorem congE_mono {E : Type} [Field E] [NumberField E] {M L : ℕ} (h : M ∣ L) {κ : GL (Fin 2) (A E)}
    (hκ : CongE L κ) : CongE M κ := by
  obtain ⟨e, rfl⟩ := h
  have hmul : ∀ (e : ℕ) (c : A E), c ∈ Oh E → (e : A E) * c ∈ Oh E := by
    intro e c hc
    induction e with
    | zero =>
      rw [Nat.cast_zero, zero_mul]
      refine ⟨rfl, fun v => ?_⟩
      change Valued.v (0 : H.Kv v) ≤ 1
      simp
    | succ e ih =>
      rw [Nat.cast_succ, add_mul, one_mul]
      refine ⟨?_, fun v => ?_⟩
      · change ((e : A E) * c).1 + c.1 = 0
        rw [ih.1, hc.1, add_zero]
      · change Valued.v (((e : A E) * c).2 v + c.2 v) ≤ 1
        exact (Valuation.map_add _ _ _).trans (max_le (ih.2 v) (hc.2 v))
  have key : ∀ x : A E, (∃ c ∈ Oh E, x = ((M * e : ℕ) : A E) * c) → ∃ c ∈ Oh E, x = (M : A E) * c := by
    rintro x ⟨c, hc, rfl⟩
    exact ⟨(e : A E) * c, hmul e c hc, by push_cast; ring⟩
  exact fun i j => ⟨key _ (hκ i j).1, key _ (hκ i j).2⟩

private theorem exNat (S : Finset (H.P ℚ)) : ∃ Q : ℕ, 0 < Q ∧ ∀ v ∈ S, Bad Q v := by
  refine ⟨∏ v ∈ S, Ideal.absNorm v.asIdeal, ?_, fun v hv => ?_⟩
  · refine Finset.prod_pos fun v _ => Nat.pos_of_ne_zero fun h => ?_
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · unfold Bad
    rw [← Finset.mul_prod_erase S _ hv, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

private theorem dv_mul_iff (L : ℕ) (v : H.P ℚ) (y t : (A ℚ)ˣ) (ht : Valued.v (H.cp v (t : A ℚ)) = 1)
    (h1 : Dv L v ((t : A ℚ) - 1)) : Dv L v (((y * t : (A ℚ)ˣ) : A ℚ) - 1) ↔ Dv L v ((y : A ℚ) - 1) := by
  have e : H.cp v ((y : A ℚ) - 1) * H.cp v (t : A ℚ) = H.cp v (((y * t : (A ℚ)ˣ) : A ℚ) - 1) - H.cp v ((t : A ℚ) - 1) := by
    simp only [Units.val_mul, map_sub, map_mul, map_one]; ring
  have e2 : Valued.v (H.cp v ((y : A ℚ) - 1)) = Valued.v (H.cp v (((y * t : (A ℚ)ˣ) : A ℚ) - 1) - H.cp v ((t : A ℚ) - 1)) := by
    rw [← e, Valuation.map_mul, ht, mul_one]
  have e3 : H.cp v (((y * t : (A ℚ)ˣ) : A ℚ) - 1) = (H.cp v (((y * t : (A ℚ)ˣ) : A ℚ) - 1) - H.cp v ((t : A ℚ) - 1)) + H.cp v ((t : A ℚ) - 1) := by ring
  unfold Dv at h1 ⊢
  constructor
  · intro h
    rw [e2]
    exact (Valuation.map_sub _ _ _).trans (max_le h h1)
  · intro h
    rw [e3]
    exact (Valuation.map_add _ _ _).trans (max_le (e2 ▸ h) h1)

private theorem aE_mul' (y t : (A ℚ)ˣ) : aE (y * t) = aE y * aE t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aE, Matrix.mul_apply, Fin.sum_univ_two]

private theorem aE_one' : aE (1 : (A ℚ)ˣ) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aE]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.exGd_of :
    ExGd := by
  intro E _ _ _ D P ω _ _ _ _ hA N₀ hN₀
  obtain ⟨f, hf, h, hne⟩ := UpperTheory.exists_whittakerCoeff_ne_zero_of_admissible E D P ω hA
  obtain ⟨M₀, hM₀, hlev⟩ := UpperTheory.exists_principalCongruence_level_invariant E P f hf h
  obtain ⟨d, hd, hdθ⟩ := UpperTheory.exists_nat_mul_integral_at_all_finite_places E D.θ
  have hae := UpperTheory.eventually_unramified_satake_eigen_of_mem_cuspRep E D P f hf h
  obtain ⟨Q, hQ, hQT⟩ := exNat (Filter.eventually_cofinite.1 hae).toFinset
  set φ₀ : GL (Fin 2) (A E) → ℂ := fun g => f.1 (g * h) with hφ₀
  have trans : ∀ ν : GL (Fin 2) (A E), (fun g => φ₀ (g * ν)) ∈ Tr P := fun ν =>
    Submodule.subset_span ⟨f, hf, ν * h, funext fun g => by simp only [hφ₀, mul_assoc]⟩
  have adm₀ : admitted D ω φ₀ := hA _ (Submodule.subset_span ⟨f, hf, h, rfl⟩)
  have admν : ∀ ν : GL (Fin 2) (A E), admitted D ω (fun g => φ₀ (g * ν)) := fun ν => hA _ (trans ν)
  have hlev₀ : ∀ κ, CongE M₀ κ → ∀ g, φ₀ (g * κ) = φ₀ g := fun κ hκ g => hlev κ hκ g

  obtain ⟨L, hLdef⟩ : ∃ L, L = N₀ * M₀ * d * Q := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; positivity
  have hN₀L : N₀ ∣ L := by rw [hLdef]; exact ⟨M₀ * d * Q, by ring⟩
  have hM₀L : M₀ ∣ L := by rw [hLdef]; exact ⟨N₀ * d * Q, by ring⟩
  have hdL : d ∣ L := by rw [hLdef]; exact ⟨N₀ * M₀ * Q, by ring⟩
  have hQL : Q ∣ L := by rw [hLdef]; exact ⟨N₀ * M₀ * d, by ring⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = M₀ * d := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  obtain ⟨n, hndef⟩ : ∃ n, n = L * M := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hndef]; positivity
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hBadL : ∀ v, Bad (L ^ 5) v → Bad L v := fun v hv => by
    unfold Bad at hv ⊢
    rw [Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem _ hv
  have hBadN : ∀ v, Bad L v → Bad (L ^ 5) v := fun v hv => by
    unfold Bad at hv ⊢
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_of_mem _ hv _ (by norm_num)
  have hgood : ∀ v, ¬ Bad (L ^ 5) v → (H.Gd D.δ v ∧ ∀ w : H.P E, w.under (𝓞 ℚ) = v →
      Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w φ₀ ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B φ₀) := fun v hv => by
    by_contra hc
    refine hv (hBadN v ?_)
    have hb : Bad Q v := hQT v (by simpa using hc)
    obtain ⟨e, rfl⟩ := hQL
    unfold Bad at hb ⊢
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hb

  obtain ⟨x, hx⟩ : ∃ x : ℕ → A ℚ, x = fun a : ℕ => (a : A ℚ) * iota L := ⟨_, rfl⟩
  have hx1 : ∀ a, (x a).1 = 0 := fun a => by
    rw [hx]
    change ((a : A ℚ)).1 * (iota L).1 = 0
    change _ * (0 : InfiniteAdeleRing ℚ) = 0
    rw [mul_zero]
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun a => ψ (x a) / n := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → GL (Fin 2) (A E) → ℂ, Φ = fun a g => φ₀ (g * nu D (x a)) := ⟨_, rfl⟩
  have hΦc : ∀ a, Continuous (Φ a) := fun a => by rw [hΦ]; exact (admν _).cont
  have hΦb : ∀ a, ∃ B : ℝ, ∀ g, ‖Φ a g‖ ≤ B := fun a => by rw [hΦ]; exact (admν _).bdd
  obtain ⟨φ, hφ⟩ : ∃ φ : GL (Fin 2) (A E) → ℂ, φ = fun g => ∑ a ∈ Finset.range n, c a * Φ a g := ⟨_, rfl⟩
  obtain ⟨Wz, hWz⟩ : ∃ Wz : (A ℚ)ˣ → GL (Fin 2) (Cinf E) → ℂ, Wz = fun y X => Wo D φ₀ (em E (aE y) * infGL E 2 X) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : (A ℚ)ˣ → ℂ, S = fun y : (A ℚ)ˣ => ∑ a ∈ Finset.range n, ψ ((a : A ℚ) * iota L * (1 - (y : A ℚ))) := ⟨_, rfl⟩
  have hW : ∀ y X, Wo D φ (em E (aE y) * infGL E 2 X) = S y / n * Wz y X := fun y X => by
    rw [hφ, UpperTheory.whittaker_sum_mul_eq_sum_mul_whittaker E D ℕ _ c Φ hΦc hΦb, hS, hWz]
    simp only [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e := UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero E D φ₀ adm₀.cont adm₀.left (x a) (hx1 a) y X
    have e' : Wo D (Φ a) (em E (aE y) * infGL E 2 X) = ψ (-((y : A ℚ) * x a)) * Wo D φ₀ (em E (aE y) * infGL E 2 X) := by
      rw [hΦ]; exact e
    rw [e', hc]
    have e2 : ψ ((a : A ℚ) * iota L * (1 - (y : A ℚ))) = ψ (x a) * ψ (-((y : A ℚ) * x a)) := by
      rw [← ψ_add', hx]
      congr 1
      ring
    rw [e2]
    ring
  have hsup : ∀ y X, Wz y X ≠ 0 → ∀ b ∈ Oh ℚ, ψ ((y : A ℚ) * ((M : A ℚ) * b)) = 1 := fun y X hz b hb => by
    have hb0 : ((M₀ : A ℚ) * (d : A ℚ) * b).1 = 0 := by
      change ((M₀ : A ℚ) * (d : A ℚ)).1 * b.1 = 0
      rw [hb.1, mul_zero]
    have hcg := UpperTheory.unipotentTheta_mem_congruence_of_integral E D M₀ d (hdθ d dvd_rfl) b hb
    have e := UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero E D φ₀ adm₀.cont adm₀.left _ hb0 y X
    have e1 : (fun g => φ₀ (g * nu D ((M₀ : A ℚ) * (d : A ℚ) * b))) = φ₀ := funext fun g => hlev₀ _ hcg g
    rw [e1] at e
    have hz' : Wo D φ₀ (em E (aE y) * infGL E 2 X) ≠ 0 := by rw [hWz] at hz; exact hz
    have e2 : ψ (-((y : A ℚ) * ((M₀ : A ℚ) * (d : A ℚ) * b))) = 1 := by
      have := mul_right_cancel₀ hz' (e.symm.trans (one_mul _).symm)
      exact this
    have e3 := ψ_neg_mul' ((y : A ℚ) * ((M₀ : A ℚ) * (d : A ℚ) * b))
    rw [e2, one_mul] at e3
    rw [hMdef]
    push_cast
    exact e3
  have hSv : ∀ y X, Wz y X ≠ 0 → S y = if ∀ v : H.P ℚ, Dv L v ((y : A ℚ) - 1) then (n : ℂ) else 0 := fun y X hz => by
    have := UpperTheory.sum_range_ratAdeleChar_iota_mul_one_sub_eq_ite L M hL hM (y : A ℚ) (hsup y X hz)
    rw [hS, hndef]
    exact this
  refine ⟨L, L ^ 5, φ, hN₀L, ?_, ?_⟩
  · refine ⟨by positivity, Dvd.intro_left (L ^ 4) (by ring), hBadL, ?_, fun v hv => (hgood v hv).1, ?_, ?_, ?_, ?_⟩
    ·
      have : φ = ∑ a ∈ Finset.range n, c a • (fun g => φ₀ (g * nu D (x a))) := by
        rw [hφ, hΦ]
        funext g
        simp [Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (trans _)
    ·
      intro w hw
      obtain ⟨-, hv⟩ := hgood _ hw
      obtain ⟨hθ, hfix, B, hB, hE⟩ := hv w rfl
      have hLw : ¬ Bad L (w.under (𝓞 ℚ)) := fun hb => hw (hBadN _ hb)
      have hk : ∀ a, H.KAt w (nu D (x a)) := fun a => by
        rw [hx]; exact UpperTheory.unipotent_natDiv_mem_maximalCompact_of_not_badPrime E D L a w hLw hθ
      have hfx := UpperTheory.fixed_and_heckeEigen_of_finset_linearCombination E w ℕ (Finset.range n) c Φ B ⟨0, Finset.mem_range.2 hn⟩
        (fun a => by rw [hΦ]; exact (H.fixTr E w φ₀ _ (hk a)).1 hfix)
        (fun a => by rw [hΦ]; exact (H.fixTr E w φ₀ _ (hk a)).2 B hE)
      rw [hφ]
      exact ⟨hfx.1, B, hB, hfx.2⟩
    ·
      intro k hk g
      rw [hφ, hΦ]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      have hcg := UpperTheory.unipotent_conj_congruence_of_pow_five E D L a hL (hdθ L hdL) (em E k) (UpperTheory.baseChangeGL2_congruence_of_level E (L ^ 5) (by positivity) k hk)
      have e := hlev₀ _ (congE_mono hM₀L hcg) (g * nu D ((a : A ℚ) * iota L))
      rw [hx]
      simp only
      rw [← e]
      congr 1
      group
    ·
      intro y X hy v _
      rw [hW] at hy
      have hz : Wz y X ≠ 0 := right_ne_zero_of_mul hy
      have hs : S y ≠ 0 := fun h0 => hy (by rw [h0]; simp)
      rw [hSv y X hz] at hs
      by_contra hv
      exact hs (if_neg fun hall => hv (hall v))
    ·
      intro t ht h1 y X
      have htL := UpperTheory.hasLevel_of_unitIdele_congruent_one L hL t ht h1
      have hcg : CongE L (em E (aE t)) := UpperTheory.baseChangeGL2_congruence_of_level E L hL _ htL
      have hWzt : Wz (y * t) X = Wz y X := by
        rw [hWz]
        have e : em E (aE (y * t)) * infGL E 2 X = em E (aE y) * infGL E 2 X * em E (aE t) := by
          rw [mul_assoc, ← UpperTheory.congruence_element_commute_inf_embedding E L _ hcg X, ← mul_assoc, ← map_mul]
          congr 2
          exact aE_mul' y t
        simp only
        rw [e]
        unfold Wo
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        rw [← mul_assoc, hlev₀ _ (congE_mono hM₀L hcg)]
      rw [hW, hW, hWzt]
      by_cases hz : Wz y X = 0
      · rw [hz, mul_zero, mul_zero]
      · congr 2
        rw [hSv y X hz, hSv (y * t) X (hWzt ▸ hz)]
        have hiff : (∀ v : H.P ℚ, Dv L v (((y * t : (A ℚ)ˣ) : A ℚ) - 1)) ↔ ∀ v : H.P ℚ, Dv L v ((y : A ℚ) - 1) :=
          forall_congr' fun v => dv_mul_iff L v y t (ht.2 v) (h1 v)
        simp only [hiff]
  ·
    have e1 : em E (aE (1 : (A ℚ)ˣ)) * infGL E 2 (1 : GL (Fin 2) (Cinf E)) = 1 := by
      rw [map_one, aE_one', map_one, one_mul]
    have hz : Wz 1 1 ≠ 0 := by
      rw [hWz]
      simp only
      rw [e1]
      unfold Wo at hne ⊢
      simpa only [hφ₀, mul_one] using hne
    have h2 := hW 1 1
    rw [e1] at h2
    rw [h2, hSv 1 1 hz, if_pos fun v => ?_]
    · exact mul_ne_zero (div_self hnC ▸ one_ne_zero) hz
    · unfold Dv
      simp
