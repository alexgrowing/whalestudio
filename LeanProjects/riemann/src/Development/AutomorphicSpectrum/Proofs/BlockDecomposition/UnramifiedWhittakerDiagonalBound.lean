import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdelicNormVecMulLeMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizationPureIntegrand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWhittakerBoundHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerContinuity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.UnrTorus

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mem_integers_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  have hset : ({x : F | x ∈ 𝒪[F]} : Set F) = (valBall F 0 : Set F) := by
    rw [coe_valBall_zero]; rfl
  have h0 := mem_valBall_iff_le_ord (K := F) (n := 0) hx
  rw [← h0]
  exact Set.ext_iff.1 hset x

theorem modulus_eq_zpow {x : F} (hx : x ≠ 0) :
    (modulus x : ℝ) = (residueCard F : ℝ) ^ (-ord x) := by
  rw [modulus_of_ne_zero hx]
  push_cast
  rfl

theorem succ_le_modulus_inv {x : F} (hx : x ≠ 0) {n : ℕ} (hn : ord x = n) :
    (n : ℝ) + 1 ≤ (modulus x : ℝ)⁻¹ := by
  have hq : (2 : ℝ) ≤ (residueCard F : ℝ) := by
    exact_mod_cast (one_lt_residueCard (K := F))
  rw [modulus_eq_zpow hx, hn, zpow_neg, inv_inv, zpow_natCast]
  calc (n : ℝ) + 1 ≤ 2 ^ n := by
        exact_mod_cast Nat.lt_two_pow_self (n := n)
    _ ≤ (residueCard F : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) hq n

variable [MeasurableSpace F] [BorelSpace F]

theorem split_bound (χ : AddChar F Circle) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (a : Fˣ) :
    ‖GL2LocalData.WcS χ c₁ c₂ (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) (dg2 a 1)‖ ≤
                 (modulus (a : F) : ℝ)⁻¹ ∧
      (GL2LocalData.WcS χ c₁ c₂ (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) (dg2 a 1) ≠ 0 →
        (modulus (a : F) : ℝ) ≤ 1) := by
  set Ψ : F × F → ℂ := Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1 with hΨ
  set f : Fˣ → ℂ := fun u => Ψ (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) *
    (((c₂ u)⁻¹ : ℂˣ) : ℂ) with hf
  have hpos : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hmp : ‖mp a (1 / 2)‖ = (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) := by
    simp only [mp]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    norm_num
  have hW : GL2LocalData.WcS χ c₁ c₂ Ψ (dg2 a 1) = ((c₁ a : ℂˣ) : ℂ) * mp a (1 / 2) * ∫ u, f u ∂multHaar F :=
    GlobalTheory.CompanionTheory.SplitBound.wcS_diag χ c₁ c₂ Ψ a
  have hsupp : ∀ u : Fˣ, f u ≠ 0 → ord (u : F) ≤ 0 ∧ 0 ≤ ord (u : F) + ord (a : F) := by
    intro u hu
    have h0 : Ψ (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) ≠ 0 := fun h0 => hu (by simp only [hf]; rw [h0]; simp)
    have hm : (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} := by
      by_contra hn
      exact h0 (Set.indicator_of_notMem hn _)
    obtain ⟨m1, m2⟩ := hm
    have e1 := (mem_integers_iff_ord (u * a).ne_zero).1 m1
    have e2 := (mem_integers_iff_ord (u⁻¹).ne_zero).1 m2
    rw [ord_units_mul] at e1
    rw [ord_units_inv] at e2
    exact ⟨by omega, e1⟩
  have hnf : ∀ u, ‖f u‖ ≤ 1 := fun u => by
    have e2 : ‖(((c₂ u)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, h₂.2 u, inv_one]
    simp only [hf, norm_mul, h₁.2 u, e2, mul_one]
    by_cases hm : (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]}
    · simp only [hΨ]
      rw [Set.indicator_of_mem hm]
      simp
    · simp only [hΨ]
      rw [Set.indicator_of_notMem hm]
      simp
  by_cases hm : 0 ≤ ord (a : F)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm
    have hle : (modulus (a : F) : ℝ) ≤ 1 := by
      have : (a : F) ∈ 𝒪[F] := (mem_integers_iff_ord a.ne_zero).2 hm
      exact_mod_cast modulus_le_one_iff.2 this
    refine ⟨?_, fun _ => hle⟩
    set S : Set Fˣ := ⋃ i ∈ Finset.range (n + 1), ordShell F (-(i : ℤ)) with hS
    have hμ : multHaar F S ≤ ((n + 1 : ℕ) : ENNReal) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      simp [multHaar_ordShell]
    have hμ' : multHaar F S < ⊤ := hμ.trans_lt (ENNReal.natCast_lt_top _)
    have hreal : (multHaar F).real S ≤ (n : ℝ) + 1 := by
      have h := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hμ
      rw [ENNReal.toReal_natCast] at h
      rw [measureReal_def]
      push_cast at h
      exact h
    have hz : ∀ u ∉ S, f u = 0 := by
      intro u hu
      by_contra hne
      obtain ⟨b1, b2⟩ := hsupp u hne
      refine hu ?_
      simp only [hS, Set.mem_iUnion]
      refine ⟨(-ord (u : F)).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · simp only [mem_ordShell]
        omega
    have hI : ‖∫ u, f u ∂multHaar F‖ ≤ (n : ℝ) + 1 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
      refine (norm_setIntegral_le_of_norm_le_const hμ' (fun u _ => hnf u)).trans ?_
      simpa using hreal
    rw [hW, norm_mul, norm_mul, h₁.2 a, one_mul, hmp]
    have hr : (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one hpos.le hle (by norm_num)
    calc (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) * ‖∫ u, f u ∂multHaar F‖
        ≤ 1 * ((n : ℝ) + 1) := mul_le_mul hr hI (norm_nonneg _) zero_le_one
      _ = (n : ℝ) + 1 := one_mul _
      _ ≤ _ := succ_le_modulus_inv a.ne_zero hn
  · have hzero : ∀ u, f u = 0 := by
      intro u
      by_contra hne
      obtain ⟨b1, b2⟩ := hsupp u hne
      omega
    have hW0 : GL2LocalData.WcS χ c₁ c₂ Ψ (dg2 a 1) = 0 := by
      rw [hW]
      simp [funext hzero]
    rw [hW0]
    exact ⟨by simpa using (inv_pos.2 hpos).le, fun h => absurd rfl h⟩

end Local

section Field

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [Algebra F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] in
theorem nsg_one_field : GL2LocalData.nsg E (1 : F) = 1 := by
  unfold GL2LocalData.nsg
  rw [if_pos]
  exact ⟨1, by simp⟩

theorem field_bound (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) {c : Eˣ →* ℂˣ}
    (hc : IsUnit1 c) (hmod : ∀ x : E, (modulus x : ℝ) = modulus (Algebra.norm F x)) (a : Fˣ) :
    ‖GL2LocalData.Wc χ σ μE lam c (Set.indicator {x : E | x ∈ 𝒪[E]} 1) (dg2 a 1)‖ ≤ (modulus (a : F) : ℝ)⁻¹ ∧
      (GL2LocalData.Wc χ σ μE lam c (Set.indicator {x : E | x ∈ 𝒪[E]} 1) (dg2 a 1) ≠ 0 →
        (modulus (a : F) : ℝ) ≤ 1) := by
  classical
  set Φ : E → ℂ := Set.indicator {x : E | x ∈ 𝒪[E]} 1 with hΦ
  have hpos : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hdet : ((dg2 a 1 : GL (Fin 2) F).val).det = a := by
    simp [dg2, Matrix.det_fin_two]
  have h00 : (dg2 a 1 : GL (Fin 2) F).val 0 0 = a := by simp [dg2]
  have h01 : (dg2 a 1 : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
  have h10 : (dg2 a 1 : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
  have h11 : (dg2 a 1 : GL (Fin 2) F).val 1 1 = 1 := by simp [dg2]
  have key : ∀ w : ℂ, w = GL2LocalData.Wc χ σ μE lam c Φ (dg2 a 1) → w = 0 ∨
      ((modulus (a : F) : ℝ) ≤ 1 ∧ ‖w‖ ≤ 1) := by
    rintro w rfl
    unfold GL2LocalData.Wc
    rw [hdet, h00, h01, h10, h11]
    by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)
    · rw [dif_pos h]
      set t : Eˣ := h.choose with ht
      have htN : Algebra.norm F (t : E) = (a : F) := h.choose_spec
      have ha : (a : F) / a = 1 := div_self a.ne_zero
      simp only [GL2LocalData.rW, ha, zero_div, if_true, nsg_one_field]
      by_cases hm : (t : E) ∈ 𝒪[E]
      · right
        have hle : (modulus (a : F) : ℝ) ≤ 1 := by
          rw [← htN, ← hmod]
          exact_mod_cast modulus_le_one_iff.2 hm
        refine ⟨hle, ?_⟩
        have hv : Φ (algebraMap F E 1 * 1 * (t : E)) = 1 := by
          simp only [map_one, mul_one, one_mul, hΦ]
          exact Set.indicator_of_mem (s := {x : E | x ∈ 𝒪[E]}) hm _
        rw [hv]
        simp only [norm_mul, hc.2 t, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        simpa using Real.rpow_le_one hpos.le hle (by norm_num : (0:ℝ) ≤ 1 / 2)
      · left
        have hv : Φ (algebraMap F E 1 * 1 * (t : E)) = 0 := by
          simp only [map_one, mul_one, one_mul, hΦ]
          exact Set.indicator_of_notMem (s := {x : E | x ∈ 𝒪[E]}) hm _
        rw [hv]
        simp
    · rw [dif_neg h]
      exact Or.inl rfl
  rcases key _ rfl with h0 | ⟨hle, hn⟩
  · rw [h0]
    exact ⟨by simpa using (inv_pos.2 hpos).le, fun h => absurd rfl h⟩
  · exact ⟨hn.trans ((one_le_inv₀ hpos).2 hle), fun _ => hle⟩

end Field

theorem main : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → m.std → Unr c v →
  ∀ y : (Qv v)ˣ, ‖m.W (dg2 y 1)‖ ≤ ‖(y : Qv v)‖⁻¹ ∧ (m.W (dg2 y 1) ≠ 0 → ‖(y : Qv v)‖ ≤ 1) := by
  intro K _ _ h2 c v m hok hstd hU y
  have hn : (modulus (y : Qv v) : ℝ) = ‖(y : Qv v)‖ :=
    GroundTheory.Automorphic.GodementSection.modulus_adicCompletion v (y : Qv v)
  rw [← hn]
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    haveI := i₁
    haveI := i₂
    obtain rfl : Φ = _ := hstd
    exact split_bound (GP.psiF v)⁻¹ (GlobalTheory.CompanionTheory.WCont.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.WCont.isUnit1_cAt c v w₂) y
  | @ns w i σ η Φ =>
    haveI := i
    obtain rfl : Φ = _ := hstd
    obtain ⟨hu, hσ, hη, -⟩ := hok
    have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
    obtain ⟨hχc, hχ1, -⟩ :=
      (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
    have hf : Module.finrank (Qv v) (Kv K w) = 2 :=
      GlobalTheory.CompanionTheory.StdThetaExists.finrank_eq_two_of_unique h2 v w hu
    have hcont : Continuous (algebraMap (Qv v) (Kv K w)) := continuous_adicCompletionMap v w
    have hWm := GlobalTheory.CompanionTheory.NormModulus.wMod (Qv v) _ hχc hχ1 (Kv K w) hf hcont σ hσ η hη
    exact field_bound (GP.psiF v)⁻¹ σ _ _ (GlobalTheory.CompanionTheory.WCont.isUnit1_localChar c w) hWm y

end GlobalTheory.CompanionTheory.UnrTorus
