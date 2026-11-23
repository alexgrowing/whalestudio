import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaDeRham
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem continuous_rank_one_rep {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] (μ : Γ →* Kˣ)
    (hμ : Continuous μ) : Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using Units.continuous_val.comp hμ

theorem UpperTheory.V.Loc.laWD :
    GlobalArtinReciprocity → HeckeLAdicCharacter → HeckeLAdicCharacterDeRham → AlgebraicCharacterWD → DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → ∀ wt : Emb l w → ℤ, IsLocAlg h κ wt → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∃ (ξ : Weil h →* ℂˣ) (hs : IsSmooth ξ), (∀ σ, (ξ σ : ℂ) = ι ((κ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) * ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion F) ^ wt τ)) ∧ GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 κ) = WD.lpOfChar h ξ hs := by
  intro hG hH hD hW hP F Ω _ _ _ _ _ l _ A w h κ hκ wt hwt O _ _ _ Bw hj ι a ha
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨μ, ξ, hμ, hξ, pμ, eξ, wξ⟩ := UpperTheory.V.Loc.ltAll hG hH hD hW hP h Bw hj ι wt a ha
  have pst : ∀ (ν : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous ν → ∀ wt, IsLocAlg h ν wt →
      GlobalTheory.Pst.IsPstAt (PP l) Bw (GlobalTheory.TripleGal.rk1 ν) := fun ν hν wt H =>
    hP.isPstAt T Bw _ (continuous_rank_one_rep ν hν) (UpperTheory.V.Loc.laDeRham hG hH hD hP h ν hν wt H O Bw hj).1
  have pκ := pst κ hκ wt hwt
  obtain ⟨ph, hph, eph⟩ := hwt
  haveI : Finite (Emb l w) := finite_contEmb w
  have hψ : Continuous (κ * μ⁻¹ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) := hκ.mul hμ.inv
  obtain ⟨ψ, hψe⟩ : ∃ ψ, ψ = κ * μ⁻¹ := ⟨_, rfl⟩
  rw [← hψe] at hψ
  have hκψ : ∀ g, (κ g : Qbar l) = μ g * ψ g := fun g => by
    rw [hψe, ← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_comm, inv_mul_cancel_right]
  have sψ : IsSmooth (ψ.comp (Subgroup.inclusion (Weil_le_Dec h))) := by
    refine .of_open (IsOpen.inter hph hξ) (by simp) fun σ hσ => Units.ext ?_
    have h1 := eph a ha σ
    have h2 := eξ (ineIncl h σ)
    have h3 : ph σ = 1 := hσ.1
    have h4 : ξ (ineIncl h σ) = 1 := hσ.2
    rw [h4, Units.val_one, eq_comm, map_eq_one_iff _ ι.injective] at h2
    simp only [zpow_neg] at h1
    rw [h3, mul_one, finprod_inv_distrib, hκψ, ← eq_inv_of_mul_eq_one_left h2] at h1
    exact mul_left_cancel₀ (Units.ne_zero _) (h1.trans (mul_one _).symm)
  have pψ := pst ψ hψ 0 ⟨_, (UpperTheory.V.Loc.laMul h).2.2 ψ ((ψ.comp (Subgroup.inclusion (Weil_le_Dec h))).comp (ineIncl h))⁻¹
    (Subgroup.isOpen_mono (H₁ := ((ψ.comp (Subgroup.inclusion (Weil_le_Dec h))).comp (ineIncl h)).ker)
      (fun _ hx => inv_eq_one.2 hx) sψ) fun σ => mul_inv_cancel _⟩
  have wψ := UpperTheory.V.Loc.wdPotUnr h Bw hj ι ψ hψ sψ pψ
  let η : Weil h →* ℂˣ := (Units.map ι.toRingHom.toMonoidHom).comp (ψ.comp (Subgroup.inclusion (Weil_le_Dec h)))
  have sη : IsSmooth η := sψ.of_le fun σ hσ => by rw [MonoidHom.comp_apply, hσ, map_one]
  have htw : GlobalTheory.TripleGal.rk1 κ = Formalism.MainNotions.SumRepresentations.At.twGL (GlobalTheory.TripleGal.rk1 μ)
      (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 ψ)) := by
    ext g i j
    fin_cases i; fin_cases j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, GlobalTheory.TripleGal.rk1, hκψ, mul_comm, Matrix.algebraMap_matrix_apply]
  have sξη : IsSmooth (ξ * η) := hξ.of_le₂ sη fun σ h1 h2 => by rw [MonoidHom.mul_apply, h1, h2, mul_one]
  refine ⟨ξ * η, sξη, fun σ => ?_, ParamAboveModel.eq_lpOfChar h _ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw h hj _) _ _ fun σ => ?_⟩
  · rw [MonoidHom.mul_apply, Units.val_mul, eξ, hκψ, mul_right_comm, map_mul ι (_ * _)]
    rfl
  · rw [htw] at pκ ⊢
    rw [GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l _ _ ⟨T⟩ ι F Ω A w h O Bw hj 1 _ _ (continuous_rank_one_rep μ hμ) (continuous_rank_one_rep ψ hψ) pμ pψ pκ,
      ParamAboveModel.eq_lpOfChar h _ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw h hj (GlobalTheory.TripleGal.rk1 ψ)) η sη wψ,
      GlobalTheory.RowTie.EigTwist.eig_lpChar _ _ σ (by simp [WD.lpOfChar]) _ (eig_lpOfChar η sη σ)]
    exact Multiset.mem_map_of_mem _ (wξ σ)
