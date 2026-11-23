import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DimClosureAddOneLe
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartResidueDegreeAlgClosedClosed

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Short.ChowClosing in
theorem chowDegreeSection : ObjectsChow.ChowDegreeSection.Statement :=
  ObjectsChow.ChowDegreeSection.proof
    (chowFormSectionPerfect_of
      (chowFormSectionAlgClosed_of
        (SectionOrderAlgClosed.proof IncIdealBelow.full SpecFirstMemIncIdeal.full
          chartChoiceAlgClosed_closed Vertical.SpecFirstNeField.full
          LocalizationPrimeDVR.full EmultiplicityOrd.full ChartFinite.full ChartLocDomain.full
          GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartNormAlgClosed
          chartLengthAlgClosed_closed LengthQuotientDet.full))
      sectionCycleReduced_closed MinimalPrimeComap.proof
      (FundCycleBaseChange.proof MinimalPrimeComap.proof))

theorem algX_strHom {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] :
    algX (strHom κ Z) ⊤ = algebraMap κ Γ(Z, ⊤) := by
  ext r
  rw [algebraMap_eq_strHom]
  simp [algX, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

section Base

variable {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}} {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S}
  {B : LB Z} {m : ℕ} {s : Fin m → B.Sec}

theorem algX_eq_comp (h : algX p ⊤ = (algX q ⊤).comp π) (U : Z.Opens) : algX p U = (algX q U).comp π := by
  rw [← TopForm.resG_comp_algX p (le_top : U ≤ ⊤), h, ← RingHom.comp_assoc, TopForm.resG_comp_algX]

private theorem eq_of_algX_top_eq {R : Type} [CommRing R] {Z : Scheme.{0}} {f g : Z ⟶ Sp R}
    (h : algX f ⊤ = algX g ⊤) : f = g := by
  have hf : ∀ φ : Z ⟶ Sp R,
      algX φ ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ.appTop).hom := by
    intro φ
    ext r
    simp [algX, Scheme.Hom.appLE, Scheme.Hom.appTop]
    rfl
  rw [hf, hf] at h
  have e : f.appTop = g.appTop := by
    simpa using CommRingCat.hom_ext h
  haveI : Mono (Sp R).toSpecΓ := by
    rw [← SpecMap_ΓSpecIso_hom]
    infer_instance
  rw [← cancel_mono (Sp R).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

theorem eq_comp_spMap (h : algX p ⊤ = (algX q ⊤).comp π) : q ≫ spMap π = p := by
  apply eq_of_algX_top_eq
  rw [h]
  ext r
  have key := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  simp only [algX, Scheme.Hom.appLE, spMap, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply,
    RingHom.coe_comp, Function.comp_apply]
  rw [key]
  rfl

theorem emb_base (h : algX p ⊤ = (algX q ⊤).comp π) (hE : Emb p s) : Emb q s := by
  obtain ⟨hLB, hcov, hch⟩ := hE
  refine ⟨hLB, hcov, fun k => ?_⟩
  obtain ⟨ha, t, hs, hr⟩ := hch k
  refine ⟨ha, t, fun x => ?_, hr⟩
  obtain ⟨P, rfl⟩ := hs x
  refine ⟨MvPolynomial.map π P, ?_⟩
  rw [algX_eq_comp h]
  simp [MvPolynomial.eval₂_map]

theorem ptIdeal_base (h : algX p ⊤ = (algX q ⊤).comp π) (z : Z) :
    ptIdeal p s z = (ptIdeal q s z).comap (MvPolynomial.map π) := by
  simp only [ptIdeal, Ideal.comap_iInf, RingHom.comap_ker]
  refine iInf_congr fun i => iInf_congr fun hi => congrArg _ ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_
  · simp [coneHom, algX_eq_comp h]
  · simp [coneHom]

end Base

end ChowFormHeightComparison₂.CF.V

namespace ChowFormHeightComparison₂.CF

private theorem evaluation_genericPoint_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    Z.evaluation U (genericPoint Z) hU a = 0 ↔ a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  constructor
  · intro h
    by_contra ha
    apply h
    have hne : Z.basicOpen a ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    show genericPoint Z ∈ (Z.basicOpen a : Set Z)
    rw [(genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen, Set.univ_inter]
    rwa [Ne, ← Opens.not_nonempty_iff_eq_bot, not_not] at hne
  · rintro rfl
    simp

private theorem C_mem_ptIdeal_genericPoint_iff {R : Type} [CommRing R] {Z : Scheme.{0}} [IsIntegral Z] {B : LB Z} {m : ℕ}
    (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (hB : B.IsLB) (r : R) :
    MvPolynomial.C r ∈ ptIdeal p s (genericPoint Z) ↔ algX p ⊤ r = 0 := by
  have hη : genericPoint Z ∈ ⨆ i, B.U i := by
    rw [hB.cover]
    trivial
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.mp hη
  simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker, coneHom, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Polynomial.C_eq_zero]
  constructor
  · intro h
    have := h i₀ hi₀
    rw [V.evaluation_algX] at this
    exact (evaluation_genericPoint_eq_zero_iff _ _).mp this
  · intro h i hi
    rw [V.evaluation_algX, h]
    simp

private theorem isProjOver_of_surjective_base {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}}
    {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S} (hπ : Function.Surjective π)
    (hq : q ≫ spMap π = p) (hP : IsProjOver p) : IsProjOver q := by
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  let ι : Z ⟶ Limits.pullback p (spMap π) := Limits.pullback.lift (𝟙 Z) q (by simp [hq])
  have h1 : ι ≫ Limits.pullback.fst p (spMap π) = 𝟙 Z := Limits.pullback.lift_fst _ _ _
  have h2 : ι ≫ Limits.pullback.snd p (spMap π) = q := Limits.pullback.lift_snd _ _ _
  haveI : IsIso ι := ⟨⟨Limits.pullback.fst p (spMap π), h1, by
    rw [← cancel_mono (Limits.pullback.fst p (spMap π)), Category.assoc, h1]
    simp⟩⟩
  rw [← h2]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion ι (ProjSpace.isProjOver_pullback_snd π hP)

open V in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem stVert (h1 : StPts) (h2 : StPull) (h3 : StDiv) : StVert := by
  intro K _ _ Z _ p B m s v d hP hE hv hd
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set κ := v.asIdeal.ResidueField
  have hB := hE.isLB
  have hker : ∀ r, algX p ⊤ r = 0 ↔ r ∈ v.asIdeal := by
    intro r
    rw [← C_mem_ptIdeal_genericPoint_iff p s hB r, ← hv, Ideal.mem_comap]
  let e : (𝓞 K ⧸ v.asIdeal) ≃+* κ :=
    RingEquiv.ofBijective _ v.asIdeal.bijective_algebraMap_quotient_residueField
  let φ : κ →+* Γ(Z, ⊤) :=
    (Ideal.Quotient.lift v.asIdeal (algX p ⊤) fun r hr => (hker r).mpr hr).comp e.symm.toRingHom
  letI inst : Algebra κ Γ(Z, ⊤) := φ.toAlgebra
  refine ⟨inst, ?_⟩
  have hπ : algX p ⊤ = (algX (strHom κ Z) ⊤).comp (algebraMap (𝓞 K) κ) := by
    rw [V.algX_strHom]
    ext r
    show algX p ⊤ r = φ (algebraMap (𝓞 K) κ r)
    have hr : e.symm (algebraMap (𝓞 K) κ r) = Ideal.Quotient.mk v.asIdeal r := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hr,
      Ideal.Quotient.lift_mk]
  have hsurj : Function.Surjective (algebraMap (𝓞 K) κ) :=
    v.asIdeal.algebraMap_residueField_surjective
  have hEκ : Emb (strHom κ Z) s := V.emb_base hπ hE
  have hPκ : IsProjOver (strHom κ Z) := isProjOver_of_surjective_base hsurj (V.eq_comp_spMap hπ) hP
  have hred : reduceMod v (ptIdeal p s (genericPoint Z)) = ptIdeal (strHom κ Z) s (genericPoint Z) := by
    rw [V.ptIdeal_base hπ]
    exact Ideal.map_comap_of_surjective _ (MvPolynomial.map_surjective _ hsurj) _
  rw [hred]
  set J := ptIdeal (strHom κ Z) s (genericPoint Z)
  have hdimle : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) ≤ m := by
    refine (ringKrullDim_quotient_le J).trans ?_
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hdimge : ((d : WithBot ℕ∞) + 1) ≤ ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) := by
    have := V.dim_add_one_le h1 hEκ
    rwa [hd] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = n := by
    revert hdimle hdimge
    generalize ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = x
    intro hdimle hdimge
    induction x using WithBot.recBotCoe with
    | bot => simp at hdimge
    | coe y =>
      induction y using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞) := hdimle
        rw [WithBot.coe_le_coe, top_le_iff] at h'
        exact ENat.coe_ne_top m h'
      | coe n => exact ⟨n, rfl⟩
  have hnd : d + 1 ≤ n := by
    rw [hn] at hdimge
    exact_mod_cast hdimge
  have hn' : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = ↑(n - 1 + 1) := by
    rw [hn]
    congr 1
    omega
  obtain ⟨hZ, hdeg⟩ := V.field_case h1 h2 h3 V.chowDegreeSection
    GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ObjectsChow_ChowDegreeClosedPoint (n - 1) Z B s hPκ hEκ hn'
  have hnd' : n - 1 = d := by
    rw [hd] at hZ
    exact_mod_cast hZ.symm
  rw [← hnd']
  exact hdeg

end ChowFormHeightComparison₂.CF
