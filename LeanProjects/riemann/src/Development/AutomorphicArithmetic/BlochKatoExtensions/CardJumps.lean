import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrime
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Module GlobalTheory.HeightCounting

private theorem cj_norm_eq {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ ≤ 1 ↔ ‖φ x‖ ≤ 1 := by
  have e1 := PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)
  have e2 := PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)
  have := (e1.symm.trans e2).le_one_iff (x := x)
  simpa only [PI.CompDegEF.normAbv_apply] using this

private theorem cj_embedding {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (τ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ ‖τ (x : E)‖ < 1) (A : ValuationSubring Ω) (hA : IsPlaceOver A w) :
    ∃ j : Ω →+* Om l, (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) ∧ ∀ x : E, j (algebraMap E Ω x) = τ x := by
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := l) E Ω w A hw hA
  have hlt : ∀ y : Ω, A.valuation y < 1 ↔ ‖j₁ y‖ < 1 := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have h0 : 0 < ‖j₁ y‖ := norm_pos_iff.2 ((map_ne_zero j₁).2 hy)
      have hv : 0 < A.valuation y := zero_lt_iff.2 ((map_ne_zero _).2 hy)
      rw [← not_le, ← not_le, ← inv_le_one₀ hv, ← inv_le_one₀ h0, ← map_inv₀, ← norm_inv, ← map_inv₀,
        A.valuation_le_one_iff, hj₁]
  have hn := cj_norm_eq τ (j₁.comp (algebraMap E Ω)) w hw (fun x => (hτ x).symm)
    (fun x => (hlt _).symm.trans (hA x))
  letI : Algebra E (Om l) := τ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let j₀ : Ω →ₐ[E] Om l := IsAlgClosed.lift
  let B : ValuationSubring Ω := ((Valued.v : Valuation (PadicAlgCl l) NNReal).comap j₀.toRingHom).valuationSubring
  have hB : ∀ y, y ∈ B ↔ ‖j₀ y‖ ≤ 1 := fun y => by
    change Valued.v (j₀ y) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.ValConjClosure.exists_conj_of_isGalois (F := E) A B (fun a => by
    rw [hB, hj₁, j₀.commutes]
    exact (hn a).symm)
  refine ⟨j₀.toRingHom.comp σ.toAlgHom.toRingHom, fun x => ((hσ x).symm.trans (hB _)), fun x => ?_⟩
  change j₀ (σ (algebraMap E Ω x)) = _
  rw [σ.commutes, j₀.commutes]
  rfl

private theorem cj_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧ Bw.Kw.1 ≤ Bw.LL.1 ∧
      ∀ x : ↥(OL L), ((x : ↥L.1) : Om l) = ((Bw.toLL x : ↥Bw.LL.1) : Om l) := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl,
    fun x hx => AlgHom.fieldRange_le_normalClosure K.1.val ⟨⟨x, hx⟩, rfl⟩, fun _ => rfl⟩

private theorem cj_model {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {a : ℕ} (r : G E Ω →* GL (Fin a) (Om l))
    (hr : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) (L₀ : FinExt l) :
    ∃ (L : FinExt l) (_ : L₀.1 ≤ L.1) (ρ : G E Ω →* GL (Fin a) ↥L.1),
      Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥L.1)) ∧ mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  obtain ⟨L, hL, h⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a r hr L₀
  let m : G E Ω →* Matrix (Fin a) (Fin a) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, h g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  refine ⟨L, hL, m.toHomUnits, ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact continuous_induced_rng.2 (hr.matrix_elem i j)
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    rfl

private theorem cj_count {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) {V : Type} [AddCommGroup V]
    [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) [FiniteDimensional ↥L.1 ↥(DdRE (P.PD K) ρ τ)] (J : Multiset ℤ)
    (hJ : ∀ n : ℤ, (J.count n : ℤ) = multV (P.PD K) ρ τ n) :
    Multiset.card J = finrank ↥L.1 ↥(DdRE (P.PD K) ρ τ) := by
  obtain ⟨lo, hlo⟩ := Pv.LocalLengthBound.rk_fildR_lo (P.PD K) ρ τ
  obtain ⟨hi, hhi⟩ := Pv.LocalLengthBound.rk_fildR_hi (P.PD K) ρ τ
  have hs := Pv.LocalLengthBound.rk_sum_multV (P.PD K) ρ τ (lo) (max (lo + 1) hi) (by omega)
  rw [hlo lo le_rfl, hhi _ (le_max_right _ _), finrank_bot, Nat.cast_zero, sub_zero] at hs
  have hsub : J.toFinset ⊆ Finset.Ico lo (max (lo + 1) hi) := by
    intro n hn
    by_contra hc
    have h0 : multV (P.PD K) ρ τ n = 0 := by
      refine Pv.LocalLengthBound.rk_multV_of_not_jump (P.PD K) ρ τ n ?_
      unfold IsJumpV
      rw [Finset.mem_Ico] at hc
      rcases lt_or_ge n lo with h | h
      · rw [hlo n h.le, hlo (n + 1) (by omega)]; simp
      · rw [hhi n (by omega), hhi (n + 1) (by omega)]; simp
    rw [← hJ, Nat.cast_eq_zero, Multiset.count_eq_zero] at h0
    exact h0 (Multiset.mem_toFinset.1 hn)
  apply Nat.cast_injective (R := ℤ)
  rw [← hs, ← Multiset.sum_count_eq_card (fun n hn => hsub (Multiset.mem_toFinset.2 hn)), Nat.cast_sum]
  exact Finset.sum_congr rfl fun n _ => hJ n

set_option maxHeartbeats 1000000 in
theorem UpperTheory.Prune.card_jumps :
    ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Wd : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
        (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (τ : D.host.E →+* Qbar l) (w : PlE D.host)
        (hr : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
        (hτ : ∀ x : 𝓞 D.host.E, x ∈ w.asIdeal ↔ ‖τ (x : D.host.E)‖ < 1) (hd : Wd.IsdRW l ι r w),
        Multiset.card (Wd.jumpsW l ι r τ) = a := by
  intro D T Wd l _ ι a r τ w hr hτ hd
  have hw : w ∈ placesOver D.host.E l := by
    refine (hτ _).2 ?_
    simpa using PI.CompDegEF.norm_natCast_lt_one l
  obtain ⟨j, hj, hjτ⟩ := cj_embedding (Ω := D.nd.Om) τ w hw hτ (D.nd.plOm.1 w) (D.nd.plOm.2 w)
  obtain ⟨L₀, Bw, hBj, hK, hto⟩ := cj_bridge (E := D.host.E) j hj
  obtain ⟨L, hL, ρ, hρc, hρ⟩ := cj_model r hr Bw.LL
  have hcl := (Wd.loc l ι w hw _ Bw (fun x => by rw [hBj]; exact hj x)
    (L₀.1.val.toRingHom.comp (OL L₀).val.toRingHom) hto).2 L hL a ρ hρc
  rw [hρ] at hcl
  have hdR := hcl.2.1.1 hd
  let τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1 := IntermediateField.inclusion (hK.trans hL)
  have hJ := (hcl.2.2.2 τ τ' (fun x => by
    change τ x = Bw.j _
    rw [hBj, hjτ])).2 hdR
  obtain ⟨hfin, -, hdim⟩ := (GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) Bw.Kw L
    (Fin a → ↥L.1) (Bw.repE L (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype))).1 τ'
  rw [cj_count (D.loc l) Bw.Kw L _ τ' _ hJ, hdim, Module.finrank_fin_fun]
  unfold IsDR
  rw [Module.finrank_fin_fun]
  exact hdR
