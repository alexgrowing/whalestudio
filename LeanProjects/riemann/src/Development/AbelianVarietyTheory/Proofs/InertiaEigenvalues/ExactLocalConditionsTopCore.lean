import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionEqTwistedCoefficientsCocycleIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteModuleKilledByPowOfNotIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleClassAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientExtensionIffAdmissibleExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantIsoTransportCocyclesExtensionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivStableLatticeIntegralCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataDualExactStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardHodgeTateJumpsCrystallineEqDimStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumericalGaloisDataLocalSituationStatement

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TopDict

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem mk_mem_unr_iff {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (I : Subgroup G) (z : ↥(Z1 π ⊤)) :
    (Submodule.Quotient.mk z : H1 π ⊤) ∈ unr π I ↔ ∃ b, ∀ g ∈ I, (z : G → M) g = π g b - b := by
  constructor
  · rintro ⟨z', ⟨b, hb⟩, h⟩
    obtain ⟨b', -, hb'⟩ := (Submodule.Quotient.eq _).mp h
    refine ⟨b - b', fun g hg => ?_⟩
    have h1 : π g b' - b' = (z' : G → M) g - (z : G → M) g := congrFun hb' g
    rw [hb g hg] at h1
    have h2 : (z : G → M) g = π g b - b - (π g b' - b') := by rw [h1]; abel
    rw [h2, map_sub]
    abel
  · rintro ⟨b, hb⟩
    exact ⟨z, ⟨b, hb⟩, rfl⟩

theorem admissibleExtension_iff_equivariantCoefIso {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ}
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
    {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (W : Representation O G M) (W' : Representation O G M') (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x))
    (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X)
    (hzz : ∀ g, z' g = LinearEquiv.rTensor X e (z g)) (hz : z ∈ Z1 (twCoef W χ X) ⊤)
    (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0) :
    Admissible PD emb Γ t Ut (Ea W χ hc ⟨z, hz⟩) ↔ Admissible PD emb Γ t Ut (Ea W' χ hc ⟨z', hz'⟩) := by
  obtain ⟨f, hf⟩ := (GlobalTheory.T.equivariantIso_transport_cocycles_extensions W W' e he χ X z z' hzz).2.1 hz hz' hc
  have hf' : ∀ g x, f.symm (Ea W' χ hc ⟨z', hz'⟩ g x) = Ea W χ hc ⟨z, hz⟩ g (f.symm x) :=
    fun g x => f.injective (by rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  exact ⟨fun h => h.of_equiv f hf, fun h => h.of_equiv f.symm hf'⟩

theorem WachMod_mem_B1_iff {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (z : G → M) : z ∈ B1 π ⊤ ↔ ∃ m, ∀ g, z g = π g m - m := by
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext fun g => (hm g).symm⟩

set_option maxHeartbeats 8000000 in

theorem topCore_of_typings : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P →
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)),
    Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  intro l _ P AI hT H hSA hSB hSC K LL hA lam hlam h5 t h w η typ U V _ _ _ _ _ _ _ _ _ _ _ ρ T₀ χ hyp X _ _ _
  let T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := LocLat.mk V ρ hyp.2.2.1 T₀
  have hcard := GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim P AI hT H K LL hA V ρ U hyp.2.2.2.1 hyp.2.2.2.2.1
  obtain ⟨r, D, ε, hHyp, hDt, hcount, hchi⟩ := GlobalTheory.T.exists_numerical_galoisData_localSituation P H K LL hA lam hlam h5 t h w η typ U T χ hyp hcard
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hHyp.1⟩
  let S : TopSit P := ⟨K, LL, _, r, (H.W K 1 LL hA.2.2).emb, D, ⟨lam, T, χ 1, ε⟩, hHyp⟩
  have hkill : ∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0 := by
    obtain ⟨_, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit (↥(OL LL)) lam hlam.not_isUnit X
  have hCl := GlobalTheory.AdmClosure.admissible_closed S
  obtain ⟨hL0, hLc⟩ := GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl (StdAdm.stdAdm S (CrysRules.crysCalc AI hT S) hCl)
  have hpoly : tableLineDegreeTwo.resPoly ρ χ t = tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t := by
    funext g
    change tableLineDegreeTwo.resPoly ρ χ t g = tableLineDegreeTwo.resPoly ρ S.Γ.chi D.t g
    rw [hDt]
    unfold tableLineDegreeTwo.resPoly
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [hchi c hc]
  have key : ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T'.ρ) (z : S.G → ↥L.T ⊗[S.O] X)
      (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤),
      tableLineDegreeTwo.IsAdmCoc (P.PD K) (H.W K 1 LL hA.2.2).emb lam (tableLineDegreeTwo.jTil U w t) (tableLineDegreeTwo.resPoly ρ χ t) L X (χ 1) z ↔
      ∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) := by
    intro T' L z hz
    rw [hpoly]
    exact exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha =>
      GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext S (tableLineDegreeTwo.jTil U w t) hcount T' L X z hz a ha

  have ext_iff : ∀ (c : ℕ) {Mc : Type} [AddCommGroup Mc] [Module S.O Mc] (Wc : Representation S.O S.G Mc)
      (e : S.O ≃ₗ[S.O] Mc), (∀ g x, e (S.Γ.Wchi c g x) = Wc g (e x)) →
      ∀ (z₀ : S.G → S.O ⊗[S.O] X) (z : S.G → Mc ⊗[S.O] X), (∀ g, z g = LinearEquiv.rTensor X e (z₀ g)) →
      ∀ (hz₀ : z₀ ∈ Z1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤) (hz : z ∈ Z1 (twCoef Wc S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea Wc S.Γ.χ₁ ha ⟨z, hz⟩)) ↔
        (∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (S.Γ.Wchi c) S.Γ.χ₁ ha ⟨z₀, hz₀⟩))) := by
    intro c Mc _ _ Wc e he z₀ z hzz hz₀ hz
    refine exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha => ?_
    exact (admissibleExtension_iff_equivariantCoefIso (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut (S.Γ.Wchi c) Wc e he S.Γ.χ₁ X z₀ z hzz hz₀ hz ha).symm
  refine ⟨?_, ?_, ?_⟩
  · intro ρ' T₀' hρ' hTT z hz
    have hz' : z ∈ Z1 (twCoef (latRep T₀) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff T₀ X (χ 1)).2 z).1 hz
    rw [key T T₀ z hz', GlobalTheory.T.cocycle_class_admissible S S.Γ.W₀ X hkill (hL0 X).2.1 ⟨z, hz'⟩]
    have hA' := ((hSA K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2).2.2.2.2 X).2
    exact (Set.ext_iff.1 hA' (Submodule.Quotient.mk ⟨z, hz'⟩)).trans
      (SetLike.mem_coe.trans (GlobalTheory.T.period_data_dual_exact (P.PD K) T₀ ρ' T₀' X (χ 1) hρ' hTT z hz'))
  · intro c hc Lc z hz
    have hc' := Finset.mem_Icc.1 hc
    have hc1 : c ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨by omega, hc'.2⟩
    have hχc : S.Γ.chi c = χ c := hchi c hc1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ c) Lc
    have he' : ∀ g x, e (S.Γ.Wchi c g x) = latRep Lc g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, hB, -⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi c) (latRep Lc) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep Lc) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 c hc1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c))) (fun x => hcont.mul continuous_const) Lc
    rw [key Tc Lc z hz', ext_iff c (latRep Lc) e he' z₀ z hzz hz₀ hz',
      GlobalTheory.T.cocycle_class_admissible S (S.Γ.Wchi c) X hkill ((hLc c (by omega) (by rw [hDt]; exact hc'.2)) X).2.1 ⟨z₀, hz₀⟩]
    have hB' := hSB K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp c hc'.1 (by rw [hDt]; exact hc'.2) X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X ↔ _
    rw [show adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X = {0} from hB',
      Set.mem_singleton_iff, Submodule.Quotient.mk_eq_zero]
    change z₀ ∈ B1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤ ↔ _
    rw [hB, WachMod_mem_B1_iff]
    exact exists_congr fun m => forall_congr' fun g =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).1 g m).symm)
  · intro L₁ z hz
    have h1 : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨le_rfl, hyp.1⟩
    have hχc : S.Γ.chi 1 = χ 1 := hchi 1 h1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ 1) L₁
    have he' : ∀ g x, e (S.Γ.Wchi 1 g x) = latRep L₁ g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, -, hU⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi 1) (latRep L₁) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep L₁) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 1 h1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1))) (fun x => hcont.mul continuous_const) L₁
    rw [key Tc L₁ z hz', ext_iff 1 (latRep L₁) e he' z₀ z hzz hz₀ hz',
      GlobalTheory.T.cocycle_class_admissible S (S.Γ.Wchi 1) X hkill ((hLc 1 le_rfl (by rw [hDt]; exact hyp.1)) X).2.1 ⟨z₀, hz₀⟩]
    have hC' := hSC K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2 X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi 1) X ↔ _
    rw [hC', GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr]
    rw [SetLike.mem_coe, mk_mem_unr_iff, hU]
    exact exists_congr fun m => forall_congr' fun g => forall_congr' fun _ =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).1 g m).symm)

end GlobalTheory.TopDict
