import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.untwist :
    GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable →
                 ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
                 (R : G K Ω →* GL (Fin n) (Qbar l)), Continuous R → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ)
                 (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsAlgPos κ m → Continuous μ → IsLAdicOf art ι κ m μ →
                 ∀ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw),
                   IsPstAt (Loc.PP l) Bw (R.comp (Dec (F := K) A).subtype) → IsPstAt (Loc.PP l) Bw ((tw R μ).comp (Dec (F := K) A).subtype) →
                   ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion K))) rc, IsRec h rc →
                     wdAt (Loc.PP l) ι Bw h hj ((tw R μ).comp (Dec (F := K) A).subtype) =
                       rc (algNorm (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w))) →
                     wdAt (Loc.PP l) ι Bw h hj (R.comp (Dec (F := K) A).subtype) = rc (algNorm σ) := by
  intro hA hW hD K Ω _ _ _ _ _ _ l _ ι n R hR art κ m μ hart hκ hμ hL w A h O _ _ _ Bw hj hP hP' σ rc hrc H
  obtain ⟨T⟩ := Loc.tiedP l
  have hdet : Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype)
      = μ.comp (Dec (F := K) A).subtype := by
    ext g
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
  have htw : (tw R μ).comp (Dec (F := K) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.twGL (R.comp (Dec (F := K) A).subtype)
        (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype)) := by
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  have hcR : Continuous fun g : ↥(Dec (F := K) A) =>
      ((R.comp (Dec (F := K) A).subtype g : GL (Fin n) (Loc.Om l)) : Matrix (Fin n) (Fin n) (Loc.Om l)) :=
    Units.continuous_val.comp (hR.comp continuous_subtype_val)
  have hcμ : Continuous fun g : ↥(Dec (F := K) A) =>
      (((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype g : GL (Fin 1) (Loc.Om l)) :
        Matrix (Fin 1) (Fin 1) (Loc.Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμ.comp (continuous_subtype_val (p := fun x => x ∈ Dec (F := K) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hdR := (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj).1
  have hPμ := GlobalTheory.Published.DeRhamPotSemistable.isPstAt hD T Bw _ hcμ hdR
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  rw [htw] at H hP'
  rw [GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l _ _ ⟨T⟩ ι K Ω A w h O Bw hj n _ _ hcR hcμ hP hPμ hP', rec_algNorm hrc] at H
  rw [rec_algNorm hrc]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [hW K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj _ hc a ha, ← HL.one _ hc.1] at H
  have e : rc (IrrGL.of (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w)).ρ
      (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w)).smooth
      (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w)).irred) =
      (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpChar (rc (.ofChar (κ.loc w) hc.1)) := by
    rw [← HL.twist]
    exact congrArg _ (GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _ hc.1).symm
  rw [e, ← GlobalTheory.NuShift.lpChar_lpTw] at H
  exact GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one K Ω A w h _ _ _ (HL.dim _) H
