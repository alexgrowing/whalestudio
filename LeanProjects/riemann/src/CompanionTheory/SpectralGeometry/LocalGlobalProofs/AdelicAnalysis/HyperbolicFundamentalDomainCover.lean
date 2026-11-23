import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBound
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetReps
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicUnitaryStabilizerCocompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicParabolicSiegelSetBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryTransitiveOnIsotropicVectorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.IsoMain

theorem actW_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (a : R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J h (a • X) = a • actW R σ J h X := funext fun i => Matrix.mulVec_smul _ a (X i)

set_option maxHeartbeats 1000000 in

theorem integral_isotropic_lines_le_flow_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∃ (Y : Set ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))) (Kc : ℝ≥0∞), IsCompact Y ∧ Kc < ⊤ ∧ (∀ p ∈ Y, hR (AF F) σ (hypJ J) (p.2 0) (p.1 0) = 1) ∧ ∀ Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → (∀ (l : E) y, l ≠ 0 → Φ ((inclR (F := F) (AF F) l : AF F ⊗[F] E) • y) = Φ y) → ∀ g : ℤ → ℝ≥0∞, (∀ (j : ℤ), ∀ p ∈ Y, Φ (((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1) ≤ g j) → ∀ L : Set (Fin 1 → Fin (M + 2) → E), L ⊆ {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} → (∀ X ∈ L, ∀ X' ∈ L, ∀ l : E, X' = l • X → X' = X) → cntI σ _ μ 𝓕 L Φ ≤ Kc * ∑' j : ℤ, g j * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ)))) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hfin τ hτ μ 𝓕 hμ h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 (M + 2)
  have hH := (GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND F E σ hcm M J hJ).1
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm _ _ hH (AF F)
  obtain ⟨ac, a1, a2, -⟩ := hact 1
  obtain ⟨-, -, -, ag⟩ := hact 2
  have : μ.IsHaarMeasure := hμ
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  obtain ⟨P, ν, S, ω, Kc, hP, _, hν, hνU, hω, hKc, hSm, hSν, hSP, hScov⟩ := GlobalTheory.T.hyperbolic_parabolic_siegel_set_bound F E σ hcm M J hJ hfin τ hτ
  obtain ⟨C, hC, hiwa⟩ := GlobalTheory.T.hyperbolic_unitary_stabilizer_cocompact F E σ hcm M J hJ
  obtain ⟨C', K, hC', hK, hcover⟩ := GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel _ μ P ν hν hνU C hC
  set e₀ : Fin 1 → Fin (M + 2) → AF F ⊗[F] E := eOne _ (M + 1) with he₀
  set e₁ : Fin 1 → Fin (M + 2) → AF F ⊗[F] E := fun _ => Fin.cons 0 (Fin.cons 1 fun _ => 0) with he₁
  have aC : ∀ X, Continuous fun h : HA (AF F) σ (hypJ J) => actW (AF F) σ _ h⁻¹ X := fun X =>
    ac.comp (continuous_inv.prodMk continuous_const)
  let Γ : Subgroup (HA (AF F) σ (hypJ J)) := HFinIn (AF F) σ (hypJ J)
  have : Countable Γ := (GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hcm _ _ hH).1
  have : Countable (Γ ⊓ P : Subgroup _) := (Subgroup.inclusion_injective (inf_le_left : Γ ⊓ P ≤ Γ)).countable
  have hrat : ∀ γ ∈ Γ, ∀ X, ∃ X' : Fin 1 → Fin (M + 2) → E, actW (AF F) σ _ γ (ratTup (AF F) X) = ratTup (AF F) X' := by
    rintro γ ⟨g, -, e⟩ X
    refine ⟨fun a => g.val *ᵥ X a, funext fun a => funext fun i => ?_⟩
    have e' : (HA.mat (AF F) σ _ γ).val = g.val.map (inclR (AF F)) :=
      (congrArg Units.val e).symm
    simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have he : e₀ = ratTup (AF F) (eOne E (M + 1)) := by
    funext a i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [he₀, eOne, ratTup]
  have hline : ∀ γ ∈ Γ ⊓ P, ∃ l : E, l ≠ 0 ∧ actW (AF F) σ _ γ e₀ = (inclR (AF F) l : AF F ⊗[F] E) • e₀ := by
    intro γ hγ
    obtain ⟨a, ha⟩ := (hP γ).1 hγ.2
    obtain ⟨X, hX⟩ := hrat γ hγ.1 (eOne E (M + 1))
    have h1 : (a : AF F ⊗[F] E) = inclR (AF F) (X 0 0) := by
      have := congrFun (congrFun (ha.symm.trans (he ▸ hX)) 0) 0
      simpa [he₀, eOne, ratTup] using this
    refine ⟨X 0 0, fun h0 => ?_, h1 ▸ ha⟩
    have : Nontrivial (AF F ⊗[F] E) := hinj.nontrivial
    exact a.ne_zero (by rw [h1, h0, map_zero])
  refine ⟨(fun p : (AF F ⊗[F] E)ˣ × HA (AF F) σ (hypJ J) =>
      (((p.1⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • actW (AF F) σ _ p.2⁻¹ e₀,
        sigR (AF F) σ (p.1 : AF F ⊗[F] E) • actW (AF F) σ _ p.2⁻¹ e₁)) '' (ω ×ˢ C'), K * Kc,
    (hω.prod hC').image (((Units.continuous_coe_inv.comp continuous_fst).smul ((aC _).comp continuous_snd)).prodMk
      ((hsc.comp (Units.continuous_val.comp continuous_fst)).smul ((aC _).comp continuous_snd))),
    ENNReal.mul_lt_top hK hKc, ?_, fun Φ hΦ hΦl g hg L hL hLu => ?_⟩
  · rintro _ ⟨⟨a, c⟩, -, rfl⟩
    have h1 : hR (AF F) σ (hypJ J) (actW (AF F) σ _ c⁻¹ e₁ 0) (actW (AF F) σ _ c⁻¹ e₀ 0) =
        hR (AF F) σ (hypJ J) (e₁ 0) (e₀ 0) := congrFun (congrFun (ag c⁻¹ ![e₁ 0, e₀ 0]) 0) 1
    have h2 : hR (AF F) σ (hypJ J) (e₁ 0) (e₀ 0) = 1 := by
      simp [hR, hform, he₀, he₁, eOne, JR, hypJ, Fin.sum_univ_succ]
    have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := GlobalTheory.GaussMean.OneVec.sigR_sigR (AF F) hcm
    rw [h2] at h1
    simp only [hR, hform, Pi.smul_apply, smul_eq_mul, map_mul, hs] at h1 ⊢
    rw [← a.mul_inv, ← mul_one (_ * _), ← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · have hw : ∀ X : L, ∃ γ ∈ Γ, actW (AF F) σ _ γ⁻¹ e₀ = ratTup (AF F) X.1 := fun X => by
      obtain ⟨g, hg, e⟩ := GlobalTheory.T.unitary_transitive_on_isotropic_vectors F E σ hcm _ _ hH (eOne E (M + 1) 0) (X.1 0)
        (fun h => one_ne_zero (congrFun h 0)) (fun h => (hL X.2).1 (funext fun a => by rw [Subsingleton.elim a 0]; exact h))
        (by simp [hE, hform, eOne, hypJ, Fin.sum_univ_succ]) (congrFun (congrFun (hL X.2).2 0) 0)
      have hm : bc (inclR (AF F)) g ∈ HR (AF F) σ (hypJ J) := by
        have h1 := congrArg (fun A => A.map (inclR (F := F) (AF F))) hg
        simp only [Matrix.map_mul] at h1
        refine Eq.trans ?_ h1
        have e1 : cT (sigR (AF F) σ) (bc (inclR (F := F) (AF F)) g).val = (cT (σ : E →+* E) g.val).map (inclR (AF F)) := by
          ext1 i j; simp [cT, bc, sigR, inclR]
        rw [e1]
        rfl
      refine ⟨(⟨_, hm⟩ : HR (AF F) σ (hypJ J))⁻¹, Γ.inv_mem ⟨g, hg, rfl⟩, ?_⟩
      rw [he]
      funext a i
      rw [Subsingleton.elim a 0, ratTup, ← e]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rfl
    choose γ hγ hγe using hw
    let Q := Quotient (QuotientGroup.rightRel ((Γ ⊓ P).subgroupOf Γ))
    have hout : ∀ x : Γ, (x : HA (AF F) σ (hypJ J)) * (((Quotient.mk _ x : Q).out : Γ) : HA (AF F) σ (hypJ J))⁻¹ ∈ Γ ⊓ P :=
      fun x => (QuotientGroup.rightRel_apply (s := (Γ ⊓ P).subgroupOf Γ)).1 (Quotient.mk_out x)
    obtain ⟨𝓕', h𝓕', hunf⟩ := GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain _ μ Γ (Γ ⊓ P) inf_le_left 𝓕 h𝓕 Q (fun q => (q.out : Γ)) (fun q => q.out.2)
      fun x hx => ⟨Quotient.mk _ ⟨x, hx⟩, hout ⟨x, hx⟩, fun q hq =>
        (Quotient.out_eq q).symm.trans (Quotient.sound (QuotientGroup.rightRel_apply.2 hq))⟩
    set f : HA (AF F) σ (hypJ J) → ℝ≥0∞ := fun h => Φ (actW (AF F) σ _ h⁻¹ e₀) with hf
    have hfm : Measurable f := hΦ.comp (aC _).measurable
    have hfi : ∀ x ∈ Γ ⊓ P, ∀ h, f (x * h) = f h := fun x hx h => by
      obtain ⟨l, hl, e⟩ := hline _ ((Γ ⊓ P).inv_mem hx)
      simp only [hf, mul_inv_rev, a2, e, actW_smul, hΦl l _ hl]
    let q : L → Q := fun X => Quotient.mk _ ⟨γ X, hγ X⟩
    have hq : Function.Injective q := fun X X' h => by
      obtain ⟨l, -, e⟩ := hline (γ X * (γ X')⁻¹)
        ((QuotientGroup.rightRel_apply (s := (Γ ⊓ P).subgroupOf Γ)).1 (Quotient.exact h.symm))
      have h1 := congrArg (actW (AF F) σ _ (γ X)⁻¹) e
      rw [← a2, inv_mul_cancel_left, actW_smul, hγe, hγe] at h1
      refine Subtype.ext (hLu _ X.2 _ X'.2 l (funext fun a => funext fun i => ?_)).symm
      apply hinj
      simpa [ratTup] using congrFun (congrFun h1 a) i
    have h1 : cntI σ _ μ 𝓕 L Φ ≤ ∫⁻ h in 𝓕', f h ∂μ := by
      rw [← hunf f hfm]
      refine lintegral_mono fun h => le_trans (le_of_eq (tsum_congr fun X => ?_))
        (ENNReal.tsum_comp_le_tsum_of_injective hq fun y => f ((y.out : Γ) * h))
      have h2 : γ X * (((q X).out : Γ) : HA (AF F) σ (hypJ J))⁻¹ ∈ Γ ⊓ P := hout ⟨γ X, hγ X⟩
      rw [← hfi _ h2, ← mul_assoc, inv_mul_cancel_right, hf]
      simp only [mul_inv_rev, a2, hγe]
    have hgm : ∀ j, Measurable ((S j).indicator fun _ => g j) := fun j => measurable_const.indicator (hSm j)
    refine h1.trans ((hcover (Γ ⊓ P) inf_le_right 𝓕' h𝓕' (⋃ j, S j) (MeasurableSet.iUnion hSm)
      (hScov.mono fun p ⟨x, hx, hx', j, hj⟩ => ⟨x, ⟨hx', hx⟩, Set.mem_iUnion.2 ⟨j, hj⟩⟩) f
      (fun p => ∑' j, (S j).indicator (fun _ => g j) p) hfm (Measurable.ennreal_tsum hgm) hfi
      (fun x _ => ?_) fun p hp c hc => ?_).trans ?_)
    · obtain ⟨c, hc, a, ha⟩ := hiwa x
      exact ⟨x * c⁻¹, (hP _).2 ⟨a, ha⟩, c, hc, by rw [inv_mul_cancel_right]⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hp
      obtain ⟨-, a, ha, e⟩ := hSP j p hj
      refine le_trans ?_ (ENNReal.le_tsum j)
      rw [Set.indicator_of_mem hj]
      refine le_trans (le_of_eq ?_) (hg j _ ⟨(a, c), ⟨ha, hc⟩, rfl⟩)
      have h2 := congrArg (fun X => (((τ (Multiplicative.ofAdd (j : ℝ)) * a)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
        actW (AF F) σ _ p⁻¹ X) e
      simp only [← a2, inv_mul_cancel, a1, actW_smul, smul_smul, Units.inv_mul, one_smul] at h2
      simp only [hf, mul_inv_rev, a2, ← h2, actW_smul, smul_smul, ofAdd_neg, map_inv, Units.val_mul, mul_comm]
    · rw [mul_assoc]
      gcongr
      refine (setLIntegral_le_lintegral _ _).trans ?_
      rw [lintegral_tsum (f := fun j p => (S j).indicator (fun _ => g j) p) fun j => (hgm j).aemeasurable, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [lintegral_indicator_const (hSm j), mul_left_comm]
      gcongr
      exact hSν j

end GlobalTheory.CompanionTheory.SW.IsoMain
