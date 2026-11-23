import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModIntStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCocyclesLocallyConstantKilledByUniformiserPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocycStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionTwistedWeilCoefficientsAdmissibl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionConductorTwistedCharacterAdmissi

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UseLoc.Cases

set_option maxHeartbeats 8000000 in
theorem partW : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (WpO D.nd i ρ π) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle D i w hw C lam hlam (locOC C (WpO D.nd i ρ π)) θ a
    (fun g => liftQ C.le D.R.r (z g)) hZ hk
  have hz'' : ∀ g, iotaW ↥C.LL.1 lam a D.R.r (z' g) = liftQ C.le D.R.r (z g) := hz'
  have hadm := GlobalTheory.T.cocycleExtension_twistedWeilCoefficients_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont z hz a z' hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).1 (repV C (locOC C (WpO D.nd i ρ π)))
    (latC C (locOC C (WpO D.nd i ρ π))) (GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul D i w hw C (locOC C (WpO D.nd i ρ π)) θ) rfl z' hcoc).1 hadm
  have hr := GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary D i w hw C lam (locOC C (WpO D.nd i ρ π)) θ a z' hin
  have e : (fun g => liftQ C.le D.R.r (z g)) = fun g => iotaW ↥C.LL.1 lam a D.R.r (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partC : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont c hc z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i c) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ c a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : c ∈ Finset.Icc 1 D.R.t :=
    Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hc).1; omega, (Finset.mem_Icc.1 hc).2⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont c hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.1 c hc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isCoboundary_read_of_twistedCharacter_coboundary D i w hw C lam θ c a z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partU : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i 1) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ 1 a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : 1 ∈ Finset.Icc 1 D.R.t := Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont 1 hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.2 (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup D i w hw C lam θ a _ z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont
  exact ⟨partW D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partC D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partU D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont⟩

end GlobalTheory.UseLoc.Cases

end
