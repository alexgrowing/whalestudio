import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReadsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorMinorProductOriginEqPeriodsJetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSelfDualEColLatOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharFiniteIdeleEqHeckeCharValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedVacuaRatioAlgebraicUnitEveryPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuCharConductorExponentsPosProdModulusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesCoprimeTwoQDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndicatorReadsNormPowerUnitVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealIndicatorUnitBlockTranslateReadsWeilOpeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondUnitBlockCosetRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalLevelMovesStandardPairSupportToUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetIffMaximalLevelCongruentConjIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.BotSmallDict

open GlobalTheory.BotFormula (IsFinPt)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}

theorem reads_om (hI : GlobalTheory.NormSum.Inp D) {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hS : S.rank = P.a) (hT : T.rank = P.d)
    (hset : Setup ψ θ S T ⊤ δ 1) {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (cS : HasFinPart χS P.W.chV P.W.ep) (cT : HasFinPart χT P.W.chV' (-P.W.ep'))
    {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} {y : Formalism.MainNotions.StandardLatticesGL3.GA D P.d} {g : Formalism.L2.Theta.GA D S} {h : Formalism.L2.Theta.GA D T}
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) {G : VC D P.a P.d → ℂ} (hG : G ∈ TT D (tor0 D ⊤ δ) P.a P.d) {f : WO S T → ℂ}
    (hf : Reads ψ θ hS hT ⊤ δ 1 G f) : Reads ψ θ hS hT ⊤ δ 1 (P.W.Om x y G) (om (g, h) f) := by
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction ψ θ S T hS hT ⊤ δ 1 hset P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)
  have h1 := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model ψ θ S T hS hT ⊤ δ 1 hset P.e0 P.W χS χT om hW hI t0 P.pt0 P.even_mul
    P.vac cS cT x y g h hg hh f₀ hf₀
  have h2 := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads ψ θ S T hS hT ⊤ δ 1 hset P.e0 P.W χS χT om hW P.vac.1 x y g h hg hh 1 f₀ hf₀
    (by rwa [one_smul]) G hG f hf
  rwa [one_smul] at h2

theorem IsStdLat.eq_colLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsStdLat L) :
    L = Formalism.L2.DIV.colLat (1 : GL (Fin n) D.host.E) := by
  ext y
  rw [h y, GlobalTheory.TestLat.Inhabitant.mem_colLat_one]
  rfl

theorem IsStdLat.eq_stdLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsStdLat L) :
    L = Formalism.L2.Col.stdLat D.host.E n := by
  ext y
  rw [h y]
  exact ⟨fun h i _ => Submodule.mem_one.2 (h i), fun h i => Submodule.mem_one.1 (h i trivial)⟩

theorem vac_read (hc : D.host.ccK = ⊤) (hset : Setup ψ θ S T ⊤ δ 1)
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLS : IsStdLat LS) (hLT : IsStdLat LT) {vac : WO S T → ℂ} (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT vac)
    {e0 : VC D S.rank T.rank → ℂ} (he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D S.rank) (stdL D T.rank)) (h0 : e0 ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ Reads ψ θ rfl rfl ⊤ δ 1 (κ • e0) vac := by
  rw [hLS.eq_colLat, hLT.eq_colLat] at hv
  have hδ := delta_ne_zero hset.crv
  have o : ∀ V : HSp D, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 * V.gram *
      (1 : GL (Fin V.rank) D.host.E).1 = 1 := fun V h => by
    rw [h, Units.val_one, mul_one, mul_one]
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T 1 1 _ _ (o S hset.gS) (o T hset.gT) vac hv
  have hTh := GlobalTheory.T.unit_vacuum_entire_factor_isThetaFunction_standard ψ θ S T 1 1 (o S hset.gS) (o T hset.gT) δ (hc ▸ hset.crv) hδ vac hv Φ hΦd hreal
  rw [hc] at hTh
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D S.rank) (stdL D T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D S.rank, GlobalTheory.NormSum.VacInt.sd_std D T.rank, rfl⟩
  obtain ⟨κ, hκ⟩ := (GlobalTheory.ThetaLine.theta_line D hG ⊤ δ hset.crv S.rank T.rank _ hK).1 _ hTh e0 he h0
  have hΦ : ∀ Z : VC D S.rank T.rank, Φ Z = (κ • e0) fun τ i j => δ * embT D τ 1 * Z τ i j := fun Z => by
    rw [← hκ]
    congr 1
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, map_one, mul_one]
    rw [inv_mul_cancel_left₀ hδ]
  refine ⟨κ, ?_, (reads_iff hset.crv hset.scale _ _).2 ⟨hv.2.theta, fun w hw => by rw [hreal w hw, hΦ]⟩⟩
  rintro rfl
  obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ vac hv
  apply hfw
  rw [hreal w hw, hΦ, zero_smul, Pi.zero_apply, mul_zero]

theorem vac_const (hI : GlobalTheory.NormSum.Inp D) (hc : D.host.ccK = ⊤) (hset : Setup ψ θ S T ⊤ δ 1)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0)
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLS : IsStdLat LS) (hLT : IsStdLat LT) {vac : WO S T → ℂ} (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT vac) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 →
      ∃ ζ : ℂ, IsAlgUnit ζ ∧ Reads ψ θ hS hT ⊤ δ 1 ((κ * ζ) • e0) vac := by
  by_cases hex : ∃ e1 : VC D S.rank T.rank → ℂ, oddE0 D ⊤ δ t0 _ _ e1 ∧ e1 ≠ 0
  · obtain ⟨e1, h1, h0⟩ := hex
    obtain ⟨κ, hκ, hr⟩ := vac_read hc hset hLS hLT hv h1.1 h0
    refine ⟨κ, hκ, fun hS hT e0 he _ => ?_⟩
    subst hS hT
    obtain ⟨ζ, hζ, e⟩ := GlobalTheory.T.normalisedVacua_ratio_algebraicUnit_everyPrime hI hset.crv ht he h1
    exact ⟨ζ, hζ, by rwa [mul_smul, ← e]⟩
  · refine ⟨1, one_ne_zero, fun hS hT e0 he h0 => ?_⟩
    subst hS hT
    exact absurd ⟨e0, he, h0⟩ hex

theorem om_placeModel {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (he : IsIdemSum e P) {vac : WO S T → ℂ} (hv : IsThetaFunO ψ S T vac) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm)
    {g : Formalism.L2.Theta.GA D S} {h : Formalism.L2.Theta.GA D T}
    (hΛ : ∀ u, u ∈ (latO S T LS LT fun _ => True) ↔ actO S T g h u ∈ (latO S T LS LT fun _ => True))
    {c : ℂ} (hc : c ≠ 0) (h0 : om (g, h) vac = c • vac) {Ψ : WO S T → ℂ}
    (hΨ : IsSBHalf (cA D e) (latO S T LS LT fun _ => True) Ψ) :
    om (g, h) (Tm Ψ) = c • Tm fun y => Ψ (actO S T g⁻¹ h⁻¹ y) := by
  have hcc : cA D (cA D e) = e := Formalism.IndefR.Fin.cA_cA e
  obtain ⟨-, -, hP⟩ := Formalism.IndefR.Fin.placeLatDual D ψ hW.std S T LS LT hS hT
  obtain ⟨T₀, -, huniq, hth, -⟩ := Formalism.IndefR.Fin.placeModelAtF D ψ hW.std S T LS LT hS hT P e he vac hv
    (fun u hu h' => by
      rcases h' with h' | h'
      · exact GlobalTheory.LocReduction.fix_conj (fun x hx hx' y hy hy' => by
          obtain ⟨hd2, -⟩ := hP P e he
          rw [hcc] at hy'
          rw [Formalism.IndefR.Fin.symplO_swap, AddChar.map_neg_eq_inv, (hd2 x hx').2 hx y hy hy', inv_one]) hTm hu
          (by rwa [hcc])
      · exact GlobalTheory.LocReduction.fix_half hTm hu h') (cA D e) (Or.inr rfl)
  have hΛ' : ∀ u, u ∈ (latO S T LS LT fun _ => True) ↔ actO S T g⁻¹ h⁻¹ u ∈ (latO S T LS LT fun _ => True) := fun u => by
    rw [hΛ (actO S T g⁻¹ h⁻¹ u), GlobalTheory.AdelicLatMove.actO_actO_inv]
  have hinv : ∀ t, actO S T g⁻¹ h⁻¹ (actO S T g h t) = t := fun t => by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ t
    rwa [inv_inv, inv_inv] at this
  have s := GlobalTheory.SchrMove.isSBHalf_comp hΛ' hΨ
  have h1 := GlobalTheory.SchrMove.isPlaceModel_move hW hΛ hTm (fun Φ hΦ => by rw [huniq Tm hTm Φ hΦ]; exact hth Φ hΦ) hc h0
  have h2 := (huniq _ h1 _ s).trans (huniq _ hTm _ s).symm
  have h3 : c⁻¹ • om (g, h) (Tm fun t => Ψ (actO S T g⁻¹ h⁻¹ (actO S T g h t))) = Tm fun y => Ψ (actO S T g⁻¹ h⁻¹ y) := h2
  simp only [hinv] at h3
  rw [← h3, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotSmallDict

namespace GlobalTheory.BotSmallDict

open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}

theorem finE_mem_St (hS : S.gram = 1) {βS : GL (Fin S.rank) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank)) {a : ℕ} (ha : S.rank = a) {k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ GlobalTheory.NormSum.intG D a) {g : Formalism.L2.Theta.GA D S} (hg : IsFinPt S g k) : Lev.finE S g ∈ Formalism.L2.DIV.St βS := by
  subst ha
  exact (GlobalTheory.BotClassDict.mem_level_iff S hS hβ g).2 (by rwa [GlobalTheory.BotClassDict.finStd_of_isFinPt S hS hg])

theorem stdSnd_eq_sum (hS : S.gram = 1) (hT : T.gram = 1) (hc : D.host.ccK = ⊤) {βS : GL (Fin S.rank) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank)) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {c : Formalism.L2.DIV.Pl D.host.E → ℕ} (he : GoodIdem e P) {o : ℕ} (ho : o + S.rank = T.rank)
    (h1 : ∀ w ∈ P, 1 ≤ c w) {ν : (Formalism.L2.Theta.AE D)ˣ →* Circle} {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq ν νH)
    (hexp : ∀ w ∈ P, GlobalTheory.CMVal.ExpAt νH w (c w)) {a : ℕ} (ha : S.rank = a) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a))
    (hR : ∀ r ∈ R, r ∈ GlobalTheory.NormSum.intG D a)
    (hR' : ∀ k ∈ GlobalTheory.NormSum.intG D a, ∃! r, r ∈ R ∧ CongOne D (D.host.conj • modul P c) (r⁻¹ * k))
    (g : Formalism.MainNotions.StandardLatticesGL3.GA D a → Formalism.L2.Theta.GA D S) (hg : ∀ r, IsFinPt S (g r) r) :
    ∃ ζ : ℂ, IsRootOne ζ ∧ stdSnd ν e (modul P c) o S T βS 1 =
      ζ • ∑ r ∈ R, (((ν (detIdl e S (g r)))⁻¹ : Circle) : ℂ) • fun y =>
        cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T (g r)⁻¹ 1⁻¹ y) := by
  subst ha
  obtain ⟨ζ, hζ, hval⟩ := GlobalTheory.T.standardPairSecond_unitBlockCoset_rootOfUnity S T hS hT hc βS hβ e P c he o ho h1 ν νH hν hexp
  refine ⟨ζ, hζ, funext fun y => ?_⟩
  rw [inv_one]
  have h01 : ∀ z : WO S T, cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) z ≠ 0 →
      cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) z = 1 := fun z hz => by
    unfold cosetFn at hz ⊢
    split_ifs at hz ⊢
    · rfl
    · exact absurd rfl hz
  have key : ∀ r ∈ R, cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T (g r)⁻¹ 1 y) ≠ 0 →
      stdSnd ν e (modul P c) o S T βS 1 y = (((ν (detIdl e S (g r)))⁻¹ : Circle) : ℂ) * ζ := fun r hr h => by
    have e1 := GlobalTheory.BotFinLevel.stdSnd_actO ν he.1 (modul P c) o S T βS 1 (finE_mem_St hS hβ rfl (hR r hr) (hg r))
      (actO S T (g r)⁻¹ 1 y)
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T (g r) 1 y
    rw [inv_one] at e2
    rw [e2, hval _ h] at e1
    exact e1
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  by_cases h0 : stdSnd ν e (modul P c) o S T βS 1 y = 0
  · rw [h0, Finset.sum_eq_zero, mul_zero]
    intro r hr
    by_contra hne
    have := key r hr (right_ne_zero_of_mul hne)
    rw [h0] at this
    exact mul_ne_zero (Circle.coe_ne_zero _) hζ.ne_zero this.symm
  · obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.exists_maximalLevel_moves_standardPairSupport_to_unitCoset S T hS hT hc βS hβ e P c he o ho ν y h0
    obtain ⟨r, ⟨hr, hr'⟩, hu⟩ := hR' k hk
    have hi := fun r' (h' : r' ∈ R) =>
      GlobalTheory.T.unitBlockCoset_iff_maximalLevel_congruent_conjIdeal S T hS e P c he.1 o ho k hk r' (hR r' h') (g k) (g r') (hg k) (hg r') y (hk' _ (hg k))
    rw [Finset.sum_eq_single_of_mem r hr, h01 _ ((hi r hr).2 hr'), key r hr ((hi r hr).2 hr'), mul_one, mul_comm]
    intro r' h' hne
    by_contra h
    exact hne (hu r' ⟨h', (hi r' h').1 (right_ne_zero_of_mul h)⟩)

theorem reads_sum {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {ι : Type} (R : Finset ι) {G : ι → VC D a d → ℂ}
    {f : ι → WO S T → ℂ} {G₀ : VC D a d → ℂ} {f₀ : WO S T → ℂ} (h₀ : Reads ψ θ hS hT ⊤ δ 1 G₀ f₀)
    (h : ∀ r ∈ R, Reads ψ θ hS hT ⊤ δ 1 (G r) (f r)) : Reads ψ θ hS hT ⊤ δ 1 (∑ r ∈ R, G r) (∑ r ∈ R, f r) := by
  induction R using Finset.induction_on with
  | empty => simpa using h₀.smul 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

theorem isFinPt_one (V : HSp D) {n : ℕ} (h : V.rank = n) : IsFinPt V 1 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  subst h
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  rw [map_one]
  simp only [OneMemClass.coe_one, Units.val_one, Fin.cast_eq_self, Matrix.one_apply]
  split_ifs <;> simp

theorem om_vac {T₀ : Type} {A A' WW : HSp D} {X : Tri T₀ A A' WW}
    {α β : T₀ → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T₀ → Formalism.L2.Host.HChar D.host.E}
    {S : T₀ → Finset (Formalism.L2.DIV.Pl D.host.E)} (hX : X.Is ψ θ α β νH S) (s : T₀)
    (hu : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S s, w.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (α s) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (β s) v)
    {k : Formalism.L2.Theta.GA D A'} (hk1 : k ∈ GfC A') (hk2 : Lev.finE A' k ∈ Formalism.L2.DIV.St X.rA'.β) :
    X.ω' s (k, 1) X.vac' = ((((α s / β s) (detIdl (X.e s) A' k))⁻¹ : Circle) : ℂ) • X.vac' := by
  have hW : IsWeilDatumO ψ A' WW (α s) (α s / β s) (X.ω' s) := hX.weil' s
  have he := hX.idem s
  have hP : ∀ w ∈ S s, Formalism.L2.NTheta.IsIdemAt (idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : Formalism.L2.Theta.AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have h1 : Lev.finE WW 1 ∈ Formalism.L2.DIV.St X.rW.β := by rw [map_one]; exact one_mem _
  have hv := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW hX.rigA'.1 hX.rigW.1 (S s) hP (GlobalTheory.LevelPlaces.under_injOn he)
    (fun v hv => ⟨(hu v hv).1, by
      rw [div_eq_mul_inv]
      exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul (hu v hv).1 (GlobalTheory.SeeSaw.WeilLines.charUnram_inv (hu v hv).2)⟩)
    k hk1 1 (one_mem _) (GlobalTheory.BotFinLevel.keeps_latHat hX.rigA'.2.1 hk2) (GlobalTheory.BotFinLevel.keeps_latHat hX.rigW.2.1 h1) X.vac'
    hX.isVac'.2.theta hX.isVac'.2.lat
  have hc : (∏ w ∈ S s, ((splitFacO (α s) (α s / β s) (detIdl (idemAt w) A' k) (detIdl (idemAt w) WW 1) : Circle) : ℂ)) =
      ((((α s / β s) (detIdl (X.e s) A' k))⁻¹ : Circle) : ℂ) := by
    rw [← GlobalTheory.BotFinLevel.prod_detIdl he hP, map_prod, ← Finset.prod_inv_distrib]
    rw [show ∀ f : Formalism.L2.DIV.Pl D.host.E → Circle, ((∏ w ∈ S s, f w : Circle) : ℂ) = ∏ w ∈ S s, (f w : ℂ) from
      fun f => map_prod Circle.coeHom f (S s)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [splitFacO, GlobalTheory.BotFinLevel.detIdl_one, map_one, mul_one]
  rw [hc] at hv
  exact hv

end GlobalTheory.BotSmallDict

namespace GlobalTheory.BotSmallDict

open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
  {A A' WW : HSp D} {X : Tri T A A' WW} {μ₀ : T} {δ t0 : ℂ} {s : T} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q}

theorem alpha_div_beta (G : GridData L sc) (s : T) (i j : Fin D.R.m) :
    (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) = G.nu s i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem hasFinPart (hL : L.Is μ₀) {𝔪 : Ideal (𝓞 D.host.E)} (hB : IsBottom G s i j 𝔪 P P') :
    HasFinPart (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) P'.W.chV P'.W.ep ∧
      HasFinPart (G.nu s i (j + 1)) P'.W.chV' (-P'.W.ep') := by
  refine ⟨fun x y h => ?_, fun x y h => ?_⟩
  · rw [hB.chars'.1 y]
    have e1 : (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) x = L.mu0 (j + 1) x * L.xi s x * L.eta x ^ (rankV D i j % 2) := rfl
    have e2 : (alphaH L s i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        (L.C.mu0 j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) * (L.xiH s).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) *
          L.C.eta.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) ^ (rankV D i j % 2) := by
      simp only [alphaH, Subgroup.coe_mul, SubmonoidClass.coe_pow, MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [e1, e2, Circle.coe_mul, Circle.coe_mul, Circle.coe_pow, GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ (hL.mu0 j) x y h, GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ (hL.xi s) x y h,
      GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ hL.eta x y h]
    simp
  · rw [zpow_neg, hB.chars'.2 y, GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ (chrEq_nu G s i j hL) x y h]
    congr 1

theorem setup (hc : D.host.ccK = ⊤) (hX : IsBottomTri W i j X) (hcrv : Crv D ⊤ δ) : Setup W.ψ W.θ A' WW ⊤ δ 1 :=
  ⟨hX.is.isVac'.1, hX.is.isVac'.2.inf, hX.std'.1, hX.stdW.1, hcrv, hc ▸ isScale_one D⟩

theorem weil_snd (hX : IsBottomTri W i j X) (s : T) :
    IsWeilDatumO W.ψ A' WW (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) (G.nu s i (j + 1)) (X.ω' s) := by
  rw [← alpha_div_beta]
  exact hX.is.weil' s

set_option maxHeartbeats 1600000 in

theorem reads_datum (hI : GlobalTheory.NormSum.Inp D) {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) (hL : L.Is μ₀) (hX : IsBottomTri W i j X)
    (hβ : X.rW.β = 1) (hB : IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P') (hS : A'.rank = P'.a) (hT : WW.rank = P'.d) {κ : ℂ}
    (hv : Reads W.ψ W.θ hS hT ⊤ δ 1 (κ • P'.e0) X.vac') :
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads W.ψ W.θ hS hT ⊤ δ 1 ((κ * ζ) • P'.F) (X.f' s) := by
  have hc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hset := setup hc hX P'.crv
  have hW := weil_snd hX s
  have he : GoodIdem (X.e s) (locPl G s) := ⟨hX.is.idem s, GlobalTheory.T.gridLocalTensorPlaces_coprime_two_q_d large₂ hR G hL s⟩
  obtain ⟨h1, hm⟩ := GlobalTheory.T.squareNuChar_conductorExponents_pos_prod_modulus G hL s i j (X.c s) (hX.is.expo s)
  have hm0 : modul (locPl G s) (X.c s) ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  have hm1 : D.host.conj • modul (locPl G s) (X.c s) ≠ ⊥ := fun h => hm0 (by
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
    simpa using this)
  have hSd : IsSelfDualC A' X.rA'.Λ := hX.is.rigA'.1
  have hTd : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hLS : IsStdLat X.rA'.Λ := hX.std'.2.1
  have hLT : IsStdLat X.rW.Λ := hX.stdW.2.1
  have hfr : Formalism.L2.DIV.IsFrame X.rA'.β (Formalism.L2.Col.stdLat D.host.E A'.rank) := hLS.eq_stdLat ▸ hX.is.rigA'.2.1
  have hee : X.e s * X.e s = X.e s := GlobalTheory.PlaceDatum.idemSum_mul_self he.1
  have hinf := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he.1)
  have sb := GlobalTheory.T.halfCosetIndicatorModIdeal_isSchwartzBruhatHalf A' WW X.rA'.Λ X.rW.Λ hSd.1 hTd.1 _ hinf _ hm1
  have sb0 := sb 0 fun _ _ => mul_zero _
  have sb1 := sb (unitPt A' WW (cA D (X.e s)) A.rank) fun a b => by
    unfold unitPt
    split_ifs
    · rw [← RingHom.map_mul, hee]
    · exact mul_zero _
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hX.is.snd s
  have hf := hall Tm hTm
  obtain ⟨ζ₁, z1, r1⟩ := GlobalTheory.T.level_indicator_reads_norm_power_unit_vector W.ψ W.θ A' WW hS hT δ hc hset _ _ hLS hLT hSd hTd _ _ (X.c s) he sb0 κ P'.e0 X.vac' P'.vac.1 hv
    hX.is.isVac'.2.lat Tm hTm
  obtain ⟨ζ₂, z2, r2⟩ := GlobalTheory.T.conjIdealIndicator_unitBlockTranslate_reads_weilOperator W.ψ W.θ A' WW hS hT δ hc hset _ _ hLS hLT hSd hTd _ _ (X.c s) he sb0 κ P'.e0 X.vac' P'.vac.1 hv
    hX.is.isVac'.2.lat Tm hTm _ A.rank r1
  have r3 : Reads W.ψ W.θ hS hT ⊤ δ 1 ((ζ₂ * (κ * ζ₁)) • cosetVec P' (D.host.conj • modul (locPl G s) (X.c s)) A.rank)
      (Tm (cosetFn (cA D (X.e s)) (D.host.conj • modul (locPl G s) (X.c s)) (unitPt A' WW (cA D (X.e s)) A.rank))) := by
    rw [GlobalTheory.FunObj.NormUniq.wd_smul, GlobalTheory.FunObj.NormUniq.wd_smul, smul_smul] at r2
    exact r2
  have hTT := GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P' hm1 A.rank
  obtain ⟨R, hR1, hR2, hF⟩ := hB.std'
  rw [← hm] at hR2 hF
  rw [← hX.rank] at hF
  choose g hg using fun r : Formalism.MainNotions.StandardLatticesGL3.GA D P'.a => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one A' hX.std'.1 r hS
  obtain ⟨ζ₃, z3, hsum⟩ := stdSnd_eq_sum hX.std'.1 hX.stdW.1 hc hfr he hX.is.rank h1 (chrEq_nu G s i j hL) (hX.is.expo s) hS R
    hR1 hR2 g hg
  obtain ⟨c1, c2⟩ := hasFinPart hL hB
  have h1W : Lev.finE WW 1 ∈ Formalism.L2.DIV.St X.rW.β := by rw [map_one]; exact one_mem _
  have r4 : ∀ r ∈ R, Reads W.ψ W.θ hS hT ⊤ δ 1
      ((ζ₂ * (κ * ζ₁)) • P'.W.Om r 1 (cosetVec P' (D.host.conj • modul (locPl G s) (X.c s)) A.rank))
      (Tm (((((G.nu s i (j + 1)) (detIdl (X.e s) A' (g r)))⁻¹ : Circle) : ℂ) • fun y =>
        cosetFn (cA D (X.e s)) (D.host.conj • modul (locPl G s) (X.c s)) (unitPt A' WW (cA D (X.e s)) A.rank)
          (actO A' WW (g r)⁻¹ 1⁻¹ y))) := fun r hr => by
    have hk := finE_mem_St hX.std'.1 hfr hS (hR1 r hr) (hg r)
    have a1 := reads_om hI P' hS hT hset hW c1 c2 (hg r) (isFinPt_one WW hT) (GlobalTheory.FunObj.NormUniq.tt_smul hTT _) r3
    have a2 := om_vac hX.is s (fun v hv => GlobalTheory.BotFinLevel.unram_off G hL s i j _ hv) (hg r).1 hk
    rw [alpha_div_beta] at a2
    rw [P'.W.smul _ _ _ _ hTT, om_placeModel hW hSd hTd he.1 hX.is.isVac'.2.theta hTm
      (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW _ _ _ _ hSd hTd hX.is.rigA'.2.1 hX.is.rigW.2.1 (g r) 1 hk h1W)
      (Circle.coe_ne_zero _) a2 sb1] at a1
    rwa [map_smul]
  have r5 := (reads_sum R hv r4).smul ζ₃
  rw [← Finset.smul_sum, ← hF, ← map_sum, ← map_smul, ← hsum, smul_smul] at r5
  refine ⟨ζ₃ * (ζ₂ * ζ₁), z3.mul (z2.mul z1), ?_⟩
  rw [hf, alpha_div_beta, hβ, show κ * (ζ₃ * (ζ₂ * ζ₁)) = ζ₃ * (ζ₂ * (κ * ζ₁)) by ring]
  exact r5

theorem period_ne_zero (hc : Crv D ⊤ δ) (τ : D.what₂.Tau) : GlobalTheory.NormExact.period D δ 1 τ ≠ 0 := by
  have hx := xiR_pos D
  have hp := Real.pi_pos
  rw [GlobalTheory.NormExact.period, map_one, mul_one]
  refine div_ne_zero (delta_ne_zero hc) ?_
  exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'

theorem ker'_eq (hI : GlobalTheory.NormSum.Inp D) (hc : D.host.ccK = ⊤) (hL : L.Is μ₀) (hX : IsBottomTri W i j X)
    {𝔪 : Ideal (𝓞 D.host.E)} (hB : IsBottom G s i j 𝔪 P P') (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) {c : ℂ} (hc0 : c ≠ 0)
    (hf : Reads W.ψ W.θ ea.symm ed.symm ⊤ δ 1 (c • P'.F) (X.f' s)) {h : Formalism.MainNotions.StandardLatticesGL3.GA D P'.d} {g : Formalism.L2.Theta.GA D WW}
    (hg : IsFinPt WW g h) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P'.a} {g' : Formalism.L2.Theta.GA D A'} (hg' : IsFinPt A' g' x)
    (T' : Tup D P'.a P'.d P'.n) :
    X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' =
      (∏ τ, GlobalTheory.NormExact.period D δ 1 τ ^ (P'.a * P'.n τ)) * c * P'.term x h T' := by
  have hset := setup hc hX P'.crv
  have hW := weil_snd hX s
  obtain ⟨c1, c2⟩ := hasFinPart hL hB
  have hF := GlobalTheory.NormSum.RepInv.test_mem (GlobalTheory.InducedType.induced_type D).1 P'.crv P' P'.level_pos
  have hcF := GlobalTheory.FunObj.NormUniq.tt_smul hF c
  have a1 := reads_om hI P' ea.symm ed.symm hset hW c1 c2 hg' hg hcF hf
  have a2 := GlobalTheory.T.fockVector_minorProduct_origin_eq_periods_jet W.ψ W.θ A' WW ea.symm ed.symm ⊤ δ 1 hset _ _ (P'.W.maps x h _ hcF).1 a1 P'.n T'
  have s1 : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
  have s2 : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
  have s3 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have s4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  rw [Tri.ker', thetaKO, s1, s2, s3, s4,
    GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ (X.ω' s) hW W.θ hset.inf _ hg'.1 _ hg.1 _ _ _ _ _ _ hf.1]
  refine a2.trans ?_
  rw [P'.W.smul _ _ _ _ hF, GlobalTheory.FunObj.NormUniq.applyAt0_smul _ hc0, GlobalTheory.NormSum.Pair.term, mul_assoc]

theorem kernel_eq_term : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₂ : ℂ, Ω₂ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ (x : GA D P'.a) (g' : GA D A'), GlobalTheory.BotFormula.IsFinPt A' g' x → ∀ T' : Tup D P'.a P'.d P'.n,
              X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' = Ω₂ * u * P'.term x h T' := by
  intro _ _ _ hI _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j A A' WW X δ t0 hX hβ
  have hc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  by_cases hex : ∃ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P'
  · obtain ⟨s₀, Q₀, P₀, P₀', hB₀⟩ := hex
    have s1 : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
    have s3 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have hv := hX.is.isVac'
    rw [s1, s3] at hv
    obtain ⟨κ, hκ, hvac⟩ := vac_const (hI D) hc (setup hc hX P₀'.crv) P₀'.pt0 hX.std'.2.1 hX.stdW.2.1 hv
    refine ⟨(∏ τ, GlobalTheory.NormExact.period D δ 1 τ ^ (P₀'.a * P₀'.n τ)) * κ,
      mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (period_ne_zero P₀'.crv τ)) hκ, fun s Q P P' hB => ?_⟩
    have hS : A'.rank = P'.a := hX.rank'.trans hB.rank.2.1.symm
    have hT : WW.rank = P'.d := by rw [hB.rank.2.2.2, hB.rank.2.2.1, ← hX.rank, ← hX.rank', hX.is.rank]
    obtain ⟨ζ, hζ, r1⟩ := hvac hS hT P'.e0 P'.vac P'.W.nz
    obtain ⟨ζ', hζ', r2⟩ := reads_datum (hI D) hR hL hX hβ hB hS hT r1
    have hu := hζ.mul hζ'.isAlgUnit
    refine ⟨ζ * ζ', hu.1, hu.2.1, fun p _ _ lam => hu.2.2 p lam, fun ea ed h g hg x g' hg' T' => ?_⟩
    obtain ⟨-, e1, -, e2, -⟩ := GlobalTheory.BottomReal.bottom_real_eq G hL hB₀ hB
    rw [ker'_eq (hI D) hc hL hX hB ea ed (mul_ne_zero (mul_ne_zero hκ hζ.1) hζ'.ne_zero) r2 hg hg' T', e1, e2]
    ring
  · exact ⟨1, one_ne_zero, fun s Q P P' hB => absurd ⟨s, Q, P, P', hB⟩ hex⟩

end GlobalTheory.BotSmallDict

end
