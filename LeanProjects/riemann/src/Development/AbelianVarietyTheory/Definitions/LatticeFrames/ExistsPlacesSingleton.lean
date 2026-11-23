import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsHaarZetaValueAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegment
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureCondition
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Model

open scoped ComplexConjugate Matrix NNReal ComplexOrder Kronecker
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem jpq_eq_one {A : HSp D} (hp : A.IsPosDef) (τ : D.what₂.Tau) :
    Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 = 1 := by
  have : IsEmpty (Fin (A.sig (tauE D τ)).2) := by rw [hp]; exact Fin.isEmpty'
  rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
  congr 1
  exact Subsingleton.elim _ _

theorem isCartanInv_one {A : HSp D} (hA : A.SigOK) (hp : A.IsPosDef) (τ : D.what₂.Tau) : IsCartanInv (gramAt D A τ) 1 := by
  obtain ⟨cA, hc⟩ := exists_isCartanFrame A hA
  obtain ⟨s, hs, hs'⟩ := IP.Model.exists_cartan (hA (tauE D τ)).choose
    (J := Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2)
    (by rw [jpq_eq_one hp, Matrix.mul_one]) (by rw [jpq_eq_one hp, Matrix.conjTranspose_one]) (IP.Model.gramAt_unit A τ) (hc τ)
  have h2 : gramAt D A τ * s = gramAt D A τ := by
    conv_lhs => rw [← hc τ, Matrix.mul_assoc, hs']
    rw [← hc τ, jpq_eq_one hp]; simp
  have h3 : s = 1 := by
    have := congrArg ((gramAt D A τ)⁻¹ * ·) h2
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (IP.Model.gramAt_unit A τ), Matrix.one_mul] using this
  exact h3 ▸ hs

theorem exists_defin {θ : InfFam D} (hθ : IsInfFam θ) {A : HSp D} (hA : A.SigOK) (hp : A.IsPosDef) :
    ∃ cA a, Defin θ A cA a := by
  obtain ⟨cA, hc⟩ := exists_isCartanFrame A hA
  obtain ⟨a, ha, -, ha'⟩ := exists_isMaj_frameInv_eq hθ (isCartanInv_one hA hp)
  refine ⟨cA, a, hθ, hA, hp, hc, isCartanInv_one hA hp, fun τ => by rw [jpq_eq_one hp]; simp, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (isMaj_iff hθ).1 ha τ
  conv_lhs => rw [← show frameInv θ A a τ = 1 from ha' τ, frameInv]
  calc _ = ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hε, diagonal_sign_mul_self]

theorem exists_places (A : HSp D) : ∃ β, ∀ Z : Finset (Formalism.L2.DIV.Pl D.host.E),
    (∀ w ∈ Z, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) →
    (∀ w ∈ Z, ∀ w' ∈ Z, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w = w') → Places A β Z := by
  have hL := isLattice_frameLat_host A
  obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame (F := D.host.F) (frameLat A) hL.fg hL.span_eq_top
  exact ⟨β, fun Z h1 h2 => ⟨hβ, GlobalTheory.GridIdem.exists_isIdemSum Z
    (fun w hw => GlobalTheory.WeilAtPlace.exists_isIdemAt_of_split (h1 w hw) rfl) h2, IP.Model.isSplit_two⟩⟩

theorem exists_places_singleton (A : HSp D) : ∃ β w, Places A β {w} := by
  obtain ⟨β, hβ⟩ := exists_places A
  have h2 : Ideal.span {(2 : 𝓞 D.host.E)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have := h.map (Algebra.norm ℤ)
    rw [show (2 : 𝓞 D.host.E) = algebraMap ℤ _ 2 from (map_ofNat _ 2).symm, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne',
      Int.isUnit_iff] at this
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h2
  have h2M : (2 : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨β, ⟨M, hM.isPrime, fun h => by simp [h] at h2M⟩, hβ _ (fun w hw => ?_) fun w hw w' hw' _ => ?_⟩
  · rw [Finset.mem_singleton.1 hw]
    refine IP.Model.isSplit_two _ ?_
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) 2 ∈ M
    rwa [map_ofNat]
  · rw [Finset.mem_singleton.1 hw, Finset.mem_singleton.1 hw']

theorem bcParam_rho {q : ℕ} (hq : q ≠ 0) (n : ℕ) : GlobalTheory.LGrp.bcParam n (LFun.Model.rhoU hq n) =
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str (Units.mk0 (q : ℂ) (by exact_mod_cast hq)) n := by
  have h := GlobalTheory.SphTheta.bcParam_map_mul 1 n (LFun.Model.rhoU hq n)
  simp only [one_mul, Multiset.map_id', LFun.Model.rhoU, ← zpow_neg] at h
  rw [h, Fin.sum_univ_eq_sum_range (fun k : ℕ => ({Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (k : ℤ)),
    Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ (-((n : ℤ) - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ)) (n / 2)]
  rcases Nat.even_or_odd' n with ⟨d, rfl | rfl⟩
  · rw [GlobalTheory.SphTheta.str_even _ d _ (by push_cast; rfl), show 2 * d / 2 = d by omega, show 2 * d % 2 = 0 by omega]
    simp
  · rw [GlobalTheory.SphTheta.str_odd _ d _ (by push_cast; rfl), show (2 * d + 1) / 2 = d by omega, show (2 * d + 1) % 2 = 1 by omega]
    simp

theorem seg_eq_str {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} (hq : q ≠ 0)
    (h : Ideal.absNorm w.asIdeal = q ^ 2) (n : ℕ) :
    LFun.seg w 1 n = GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str (Units.mk0 (q : ℂ) (by exact_mod_cast hq)) n := by
  have hu : ∀ f : ℕ → ℂˣ, (Finset.range n).val.map f = ∑ i ∈ Finset.range n, ({f i} : Multiset ℂˣ) := fun f => by
    rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton ((Finset.range n).val.map f), Multiset.map_map]; rfl
  rw [GlobalTheory.SphTheta.str_eq_sum, Int.toNat_natCast, LFun.seg, hu, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  congr 1
  refine Units.ext ?_
  rw [one_mul, LFun.coe_npowU, LFun.npow, h, Units.val_zpow_eq_zpow_val, Units.val_mk0, Nat.cast_sub (by omega),
    Nat.cast_sub (by omega), Nat.cast_pow, ← Complex.cpow_intCast, ← Complex.natCast_cpow_natCast_mul]
  congr 1
  push_cast
  ring

theorem isParamFun_one (V : HSp D) (S : Set (FinPl D)) :
    LFun.IsParamFun D.sp.cm.sig V.gram (frameLat V) S (fun _ => (1 : ℂ)) (LFun.segFam 1 V.rank) := by
  intro v _ w h
  have hH := isHermND_gram V
  have hL := isLattice_frameLat_host V
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    have := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h0 : (fun _ : GA D V => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hL.span_eq_top h hs hd
    exact Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w V.rank).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map
      (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0⟩
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hw' w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, -, hconj⟩ := (LFun.exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram (frameLat V) hH hL.fg hL.span_eq_top hd
    refine Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero v) V.rank).2 1
      (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0, ?_⟩
    rw [bcParam_rho]
    exact seg_eq_str (LFun.qV_ne_zero v) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

theorem form_one (θ : InfFam D) {A : HSp D} (hA : IsAniso A) (h5 : 5 ≤ A.rank) (cA : CptF A)
    (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    Form θ A cA β Z 1 0 A.rank (fun _ => 1) (LFun.segFam 1 A.rank) := by
  have hcc : (fun _ => (1 : ℂ)) ∈ cuspCont A := ⟨continuous_const, fun _ _ _ => rfl, fun r C hC => absurd hC (hA r C)⟩
  have hv : LFun.val (F := D.host.F) (1 : (AE D)ˣ →* Circle) = 1 := funext fun w => by simp [LFun.val, LFun.locChar]
  refine ⟨⟨⟨isAutFunSm_const θ A 1, .of_invariant fun _ _ _ => rfl⟩, hcc⟩, fun _ _ _ => rfl, isParamFun_one A _,
    fun w _ x _ => by simp [LFun.locChar], 0, (under Z).finite_toSet, by omega, fun w _ => ?_⟩
  rw [hv]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam]

theorem unrOff_pow {η : (AE D)ˣ →* Circle} (hη : UnramEverywhere D η) (n : ℕ) : GlobalTheory.StepLaw.UnrOff (η ^ n) ∅ :=
  fun v ε hε _ x h1 h2 h3 => by
    have : infPart D ((x : AE D) - 1) = 0 := by
      rw [← h1, RingHom.map_mul, GlobalTheory.WeilProduct.infPart_placeIdem hε, zero_mul]
    rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
    rw [MonoidHom.pow_apply, hη x this h2 h3, one_pow]

theorem detPlus_neg {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus 1 (-1) a b = 1 := by
  have h : ((-1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) = -1 := by
    rw [Matrix.transpose_one, ← neg_one_smul ℂ (1 : Matrix (Fin m) (Fin m) ℂ), Matrix.smul_kronecker,
      Matrix.one_kronecker_one, neg_one_smul]
  rw [GlobalTheory.WeilParts.detPlus, h, add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
  simp

theorem exists_occ {θ : InfFam D} (hθ : IsInfFam θ) {A W : HSp D} (hA : A.SigOK) (hp : A.IsPosDef) (hW : W.SigOK)
    (hn : ∀ τ, IsCartanInv (gramAt D W τ) (-1)) : ∃ ψ η om Φ, GlobalTheory.WeilParts.IsEtaTilde D η ∧
      IsWeilDatumO ψ A W (η ^ A.rank) (η ^ W.rank) om ∧ Φ ≠ 0 ∧ ∀ β, Formalism.L2.DIV.IsFrame β (frameLat A) →
      ∀ Z (m : Measure (GA D A)), m.IsHaarMeasure → Occ ψ θ (fun _ => -1) om m β Z (fun _ => 1) Φ := by
  obtain ⟨-, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have dA := GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A
  have dW := GlobalTheory.WeilAtPlace.isSelfDualC_frameLat W
  have cA := isCartanInv_one hA hp
  obtain ⟨om, hom, -, hv⟩ := GlobalTheory.WeilProduct.exists_weilDatum_etaTilde D ψ hψ A W θ hθ _ _ dA dW η hη
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ A W (fun _ => 1) (fun _ => -1) hA hW cA hn _ _ dA dW
  have hL := isLattice_frameLat_host W
  obtain ⟨γ, hγ⟩ := GlobalTheory.AdelicFrame.exists_isFrame (F := D.host.F) (frameLat W) hL.fg hL.span_eq_top
  refine ⟨ψ, η, om, Φ, hη, hom, (IP.Model.isSphOff_of_vac hΦ ∅).2.2, fun β hβ Z m hm => ⟨hn, (IP.Model.isSphOff_of_vac hΦ ∅).1,
    (IP.Model.isSphOff_of_vac hΦ _).2.1, fun κ hκ => ?_, fun ν 𝓕 hν mR hR => ?_⟩⟩
  · have := GlobalTheory.StepVecLaw.om_vac hom hA hW cA hn dA dW hβ hγ hΦ (P := ∅) (e := 0) ⟨⟨0, by simp, by simp⟩, zero_mul _⟩
      (aS := 1) (aT := 1) (by simp) (by simp) (unrOff_pow hη.2.1 _) (unrOff_pow hη.2.1 _) (g := κ) (h := 1) hκ.1 (one_mem _)
      hκ.2.1.1.1.2 (by rw [map_one]; exact one_mem _)
    simpa using this
  · have : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hA fun τ => Or.inl (hp τ))
    have h1 : ∀ b : GinfC A, wcoef om ν 𝓕 Φ Φ b = 1 := fun b => by
      have := hΦ.2.norm.2 (ν, 𝓕) hν
      rw [wcoef, hv (fun _ => 1) (fun _ => -1) cA hn b b.2 1 (one_mem _) (by simp) (by simp) Φ hΦ.2.theta hΦ.2.fock, ip]
      simp only [detPlus_neg, Finset.prod_const_one, one_smul, Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal]
      exact_mod_cast this
    have h2 : ∀ b : GinfC A, rcoef m (fun _ => 1) (fun _ => 1) (b : GA D A) = ((autMeasure A m).real Set.univ : ℝ) := fun b => by
      simp [rcoef, petersson, pet, AutomorphicL2Unitary.descend, rTr, autMeasure]
    simp only [h1, h2, one_mul, integral_const, Complex.real_smul]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨NeZero.ne _, measure_ne_top _ _⟩))
      (GlobalTheory.Eis.Model.vol_ne_zero A m)

theorem isCartanInv_neg {W : HSp D} (hW : W.SigOK) (hp : W.IsPosDef) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D (GlobalTheory.NegSpace.neg W) τ) (-1) := by
  have e : gramAt D (GlobalTheory.NegSpace.neg W) τ = -gramAt D W τ := Matrix.ext fun i j => map_neg (tauE D τ) (W.gram i j)
  have h := (isCartanInv_one hW hp τ).2.2
  rw [e]
  have key : ∀ {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ), (G * 1).PosDef → IsCartanInv (-G) (-1) := fun G h =>
    ⟨by simp, by simp, by simpa using h⟩
  exact key _ h

theorem hypotheses (D : D7) (n r : ℕ) : ∃ (ψ : _) (θ : _) (A W : HSp D) (χA χW : _) (om : WRep A W) (cA : _) (a : _) (β : _) (w : _)
    (m : Measure (GA D A)) (sW : RealMat W) (Φ : _), A.rank = n ∧ W.rank = r ∧ Defin θ A cA a ∧ W.SigOK ∧
    (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ IsWeilDatumO ψ A W χA χW om ∧ Places A β {w} ∧ m.IsHaarMeasure ∧
    Occ ψ θ sW om m β {w} (fun _ => 1) Φ ∧
    (r = 0 → 5 ≤ n → Form θ A cA β {w} χW W.rank n (fun _ => 1) (LFun.segFam 1 n)) := by
  let A : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  let W : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral r
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  have hA : A.SigOK := Examples₂.posSpace_sigOK _ _
  have hW : W.SigOK := Examples₂.posSpace_sigOK _ _
  have hW' := GlobalTheory.NegSpace.sigOK_neg _ W hW
  obtain ⟨cA, a, hd⟩ := exists_defin hθ hA fun _ => rfl
  obtain ⟨β, w, hP⟩ := exists_places_singleton A
  obtain ⟨ψ, η, om, Φ, hη, hom, -, hO⟩ := exists_occ (W := GlobalTheory.NegSpace.neg W) hθ hA (fun _ => rfl) hW'
    (isCartanInv_neg hW fun _ => rfl)
  refine ⟨ψ, θ, A, _, _, _, om, cA, a, β, w, Measure.haar, _, Φ, rfl, rfl, hd, hW', ⟨η, hη⟩, hom, hP, inferInstance,
    hO β hP.frame _ _ inferInstance, ?_⟩
  rintro rfl h5
  exact form_one θ (GlobalTheory.ThetaMean.Model.isAniso_posSpace n) h5 cA β _

theorem lev_prinDat (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z) = Formalism.L2.DIV.Kg D.sp.cm A.gram β Z := by
  refine le_antisymm (fun x hx => ⟨hx.1.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => ?_⟩)
    (Formalism.L2.DIV.Kg_le_lev subset_rfl (Finset.empty_subset _))
  have h1 := Formalism.L2.DIV.mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.1.1.2 PP) hP)
  have h2 : Formalism.L2.DIV.upperLeftBlock le_rfl (Formalism.L2.DIV.redFn β PP x) = 1 := congrFun (Subgroup.mem_bot.1 hx.2) ⟨PP, hP⟩
  have h3 := Formalism.L2.DIV.upper_block_val_submatrix le_rfl (Formalism.L2.DIV.blockTri_blkOf_le _ _ h1.2)
  refine Formalism.L2.DIV.mem_princAt.2 ⟨h1.1, Units.ext ?_⟩
  exact h3.symm.trans (congrArg Units.val h2)

theorem dblInt_delta {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χ : (AE D)ˣ →* Circle} {om : WRep A W}
    {omh : WRep (dblSp A) W} (h : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ThetaClause ψ A W χ om omh) (m : Measure (GA D A)) [m.IsHaarMeasure] (u : GA D A → ℂ)
    {f₁ f₂ : WO A W → ℂ} (h₁ : IsThetaFunO ψ A W f₁) (h₂ : IsThetaFunO ψ A W f₂) (x : GA D W) :
    Eis.dblInt A χ⁻¹ m (fun g => thetaKO omh g x (delta A W f₁ f₂)) (fun g => conj (u g)) (fun g => conj (u g)) =
      up om m f₁ u x * conj (up om m f₂ u x) := by
  rw [Eis.dblInt_of_factor (A := fun g => thetaKO om g x f₁) (B := fun g => thetaKO om g x f₂)
    fun g₁ g₂ => (((h f₁ f₂ h₁ h₂).2 g₁ g₂ x).2).trans (by rw [MonoidHom.inv_apply])]
  simp only [up, petersson, pet, AutomorphicL2Unitary.descend, ← integral_conj, map_mul, Complex.conj_conj]
  congr 1
  exact integral_congr_ae (.of_forall fun q => mul_comm _ _)

theorem noLift_of_kills {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χ : (AE D)ˣ →* Circle} {om : WRep A W}
    {omh : WRep (dblSp A) W} (h : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ThetaClause ψ A W χ om omh) {m : Measure (GA D A)} [m.IsHaarMeasure] {u : GA D A → ℂ}
    (hk : Kills ψ χ omh m u) : NoLift ψ om m u := fun f hf x => by
  have := (dblInt_delta h m u hf hf x).symm.trans (hk _ (h f f hf hf).1 x)
  simpa using this

theorem gap_of_form {θ : InfFam D} {A : HSp D} {cA : CptF A} {β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)}
    {Z : Finset (Formalism.L2.DIV.Pl D.host.E)} {χ : (AE D)ˣ →* Circle} {r t : ℕ} {u : GA D A → ℂ} {par : LFun.Fam D.host.E}
    (h : Form θ A cA β Z χ r t u par) : r + 5 ≤ t := h.str.choose_spec.2.1

theorem not_occ_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A W : HSp D} (hA : A.SigOK) (hp : A.IsPosDef) (sW : RealMat W)
    (om : WRep A W) (m : Measure (GA D A)) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E))
    (Φ : WO A W → ℂ) : ¬ Occ ψ θ sW om m β Z 0 Φ := fun h => by
  have : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hA fun τ => Or.inl (hp τ))
  obtain ⟨ν, 𝓕, hν⟩ := exists_isCovolOne D W.rank A.rank
  exact h.real ν 𝓕 hν Measure.haar inferInstance (by simp [rcoef, petersson, pet, AutomorphicL2Unitary.descend])

theorem not_form_one {θ : InfFam D} {A : HSp D} {cA : CptF A} {β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)}
    {Z : Finset (Formalism.L2.DIV.Pl D.host.E)} {χ : (AE D)ˣ →* Circle} {r t : ℕ} {par : LFun.Fam D.host.E}
    (hr : 0 < r) (hn : A.rank = r + t) : ¬ Form θ A cA β Z χ r t (fun _ => 1) par := fun h => by
  obtain ⟨v, hv, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem (GlobalTheory.AdelicU.isCMExt_host D) (under Z)
  have hs := GlobalTheory.LFun.SplitChart.isSplit_of_algHom (GlobalTheory.AdelicU.isCMExt_host D) τ
  obtain ⟨w, -, -, hw, -⟩ := id hs
  have hw' : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hw
  have e := (h.param v (by simpa using hv) w hw').unique_of_isSplit hs
    (isParamFun_one A (under Z : Set (FinPl D)) v (by simpa using hv) w hw')
  obtain ⟨c, -, ht, hc⟩ := h.str
  obtain ⟨-, hb, -, hx, hP⟩ := hc w (by simpa [LFun.above, hw'] using hv)
  have hN : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℕ) := by exact_mod_cast LFun.one_lt_absNorm w
  have hm : (1 * LFun.npowU w (((A.rank : ℂ) - 1) / 2 - (0 : ℕ))) ∈ par w := by
    rw [e, LFun.segFam, LFun.seg, Multiset.mem_map]
    exact ⟨0, (Finset.mem_range (n := A.rank)).2 (by omega), rfl⟩
  have hnorm : ‖((1 * LFun.npowU w (((A.rank : ℂ) - 1) / 2 - (0 : ℕ)) : ℂˣ) : ℂ)‖ =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((A.rank : ℝ) - 1) / 2) := by
    rw [one_mul, LFun.coe_npowU, LFun.norm_npow]
    congr 1
    norm_num [Complex.div_re, Complex.normSq_apply]
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (r : ℝ) + 5 ≤ t := by exact_mod_cast ht
  have hn' : (A.rank : ℝ) = r + t := by exact_mod_cast hn
  rw [hP, GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam, mul_inv_cancel, LFun.twist_one, Pi.add_apply, Multiset.mem_add] at hm
  rcases hm with hm | hm
  · have := hb _ hm
    rw [hnorm, Real.rpow_le_rpow_left_iff hN] at this
    linarith
  · rw [LFun.segFam, LFun.seg, Multiset.mem_map] at hm
    obtain ⟨i, -, hi⟩ := hm
    have := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) hi
    rw [hnorm, Units.val_mul, norm_mul, hx, one_mul, LFun.coe_npowU, LFun.norm_npow] at this
    have h2 := (Real.rpow_le_rpow_left_iff hN).1 this.ge
    have : (((t : ℂ) - 1) / 2 - (i : ℂ)).re = ((t : ℝ) - 1) / 2 - i := by simp
    rw [this] at h2
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith

theorem form_ne_zero {θ : InfFam D} {A : HSp D} {cA : CptF A} {β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)}
    {Z : Finset (Formalism.L2.DIV.Pl D.host.E)} {χ : (AE D)ˣ →* Circle} {r t : ℕ} {par : LFun.Fam D.host.E} {u : GA D A → ℂ}
    (h : Form θ A cA β Z χ r t u par) : u ≠ 0 ∧ A.rank = r + t := by
  obtain ⟨v, hv, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem (GlobalTheory.AdelicU.isCMExt_host D) (under Z)
  have hs := GlobalTheory.LFun.SplitChart.isSplit_of_algHom (GlobalTheory.AdelicU.isCMExt_host D) τ
  obtain ⟨w, -, -, hw, -⟩ := id hs
  have hw' : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hw
  have e := h.param v (by simpa using hv) w hw'
  obtain ⟨c, -, ht, hc⟩ := h.str
  obtain ⟨h1, -, -, -, hP⟩ := hc w (by simpa [LFun.above, hw'] using hv)
  refine ⟨e.ne_zero, ?_⟩
  rw [← e.card, hP, GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam, mul_inv_cancel, LFun.twist_one, Pi.add_apply, Multiset.card_add, h1,
    LFun.segFam, LFun.card_seg]

end GlobalTheory.Core.Rk.Exh.Model

end
