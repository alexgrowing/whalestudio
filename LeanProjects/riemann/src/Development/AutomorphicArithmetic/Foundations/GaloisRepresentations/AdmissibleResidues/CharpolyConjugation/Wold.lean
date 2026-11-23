import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyConjGlAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Wwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem norm_one {x : WD h} {t : ℝ} (ht : (x.lpTw t).tempered) (h0 : x.mono0) {g : ↥(Weil h)}
    (hg : deg g = 1) {α : ℂ} (hα : α ∈ (x.lpTw t).eig g) : ‖α‖ = 1 := by
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.tempered_mk] at ht
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
    rw [WD.lpTw_mk, WD.eig_mk] at hα
    have top := ht.norm_eq_one (by simpa using h0) hg
    have hroot := (mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hα
    have hev : Module.End.HasEigenvalue ((a.tw t).ρ g) α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot
    by_contra hne
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hind := Module.End.eigenspaces_iSupIndep ((a.tw t).ρ g)
    have hle : absSpace ((a.tw t).ρ g) 1 ≤ ⨆ (μ : ℂ) (_ : μ ≠ α), Module.End.eigenspace ((a.tw t).ρ g) μ := by
      refine iSup_le fun μ => iSup_le fun hμ => ?_
      exact le_iSup₂_of_le μ (fun e => hne (e ▸ hμ)) le_rfl
    rw [top] at hle
    have hd := (hind α).le_bot ⟨hv.1, hle Submodule.mem_top⟩
    exact hv.2 (by simpa using hd)

private theorem win {x : WD h} {t : ℝ} (ht : (x.lpTw t).tempered) (h0 : x.mono0) {g : ↥(Weil h)}
    (hg : deg g = 1) {α β : ℂ} (hα : α ∈ x.eig g) (hβ : β ∈ x.eig g) : ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖ := by
  set c : ℂ := ((normV w : ℕ) : ℂ) ^ ((t : ℝ) : ℂ) with hc
  have mem : ∀ z ∈ x.eig g, ‖z‖ * ‖c‖ = 1 := fun z hz => by
    rw [← norm_mul]
    exact norm_one ht h0 hg (by rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hg]; exact Multiset.mem_map_of_mem _ hz)
  have e1 := mem α hα
  have e2 := mem β hβ
  have hc0 : ‖c‖ ≠ 0 := fun e => by rw [e, mul_zero] at e1; exact zero_ne_one e1
  have heq : ‖α‖ = ‖β‖ := mul_right_cancel₀ hc0 (e1.trans e2.symm)
  have hb : 0 < ‖β‖ := by
    rcases (norm_nonneg β).eq_or_lt with e | e
    · rw [← e, zero_mul] at e2; exact absurd e2 zero_ne_one
    · exact e
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  rw [heq]
  nlinarith

end

theorem UpperTheory.GalN.V.L.wold :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n), Continuous r → (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π → Unlinked r := by
  intro P F Ω _ _ _ _ _ _ l _ ι n hn r π hr hreg ⟨χ, hpol⟩ ha
  obtain ⟨R, wt, HT, H⟩ := P.litN.aut.gal F Ω l ι n hn π χ hreg hpol
  have hiso : RepIso r R := by
    refine isoOfFrob P F Ω l ι n r R hr H.cont ha.1 H.ss ((ha.2.and (eventually_not_mem F l)).mono ?_)
    rintro w ⟨⟨B, h1, h2⟩, hw⟩
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P F n π w
    exact ⟨_, h2, satFrob P F Ω l ι n R H.cont w hw σ B (((satLoc P F n w σ).2 _ π.finPart (hi σ hσ) B).1 h1)
      fun A h rc hrc => H.away w hw A h rc hrc σ hσ⟩
  refine UpperTheory.GalN.V.L.wiso F Ω l n R r hiso.symm' ?_
  intro w hl A hA hfin
  refine UpperTheory.GalN.V.L.wwd F Ω l n R ι w A hA hl H.cont ?_
  intro g hg α hα β hβ
  exact win (H.tempered_wdOf hl hA) ((weilDeligneParam_monodromy_eq_zero_iff hl ι (Units.continuous_val.comp H.cont)).2 hfin) hg hα hβ
