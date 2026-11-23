import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSBOfIsNatDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedChartThroughWCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHalvesEqLinearModelLagrangiansStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqSmulIntegralMatrixIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFrameLocalCompactMembershipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigZetaIntegralEqSmulSmallZetaIntegralOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralStandardPairFirstEqSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMemSchwartzBruhatOfConductorExponentStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}

theorem isLagrModel_chart {A A' B B' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))} {Z Z' : Type} [TopologicalSpace Z] [Add Z]
    [TopologicalSpace Z'] [Add Z'] {co : _ → Z} {co' : _ → Z'} {ι} (h : IsLagrModel M ψ v A A' co ι) (Θ : Z ≃ₜ Z')
    (hΘ : ∀ x y, Θ (x + y) = Θ x + Θ y) (hB : B = A) (hB' : B' = A') (hco : ∀ u, Θ (co u) = co' u) :
    IsLagrModel M ψ v B B' co' (LinearMap.funLeft ℂ ℂ Θ.symm ∘ₗ ι) := by
  subst hB hB'
  refine ⟨(bijOn_funLeft Θ).comp h.1, fun u hu φ hφ φ₁ h₁ ha z => ?_, fun u hu φ hφ φ₁ h₁ ha x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := Θ.surjective z
    rw [← hco, ← hΘ]
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Homeomorph.symm_apply_apply]
    exact h.2.1 u hu φ hφ φ₁ h₁ ha z
  · rw [← hco]
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Homeomorph.symm_apply_apply]
    exact h.2.2 u hu φ hφ φ₁ h₁ ha x hx

end Generic

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]

theorem smallP_smul [MeasurableSpace k] [BorelSpace k] (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (c : ℂ)
    (Ψ : Matrix A' C k → ℂ) : smallP μ σ ν α (c • Ψ) = c • smallP μ σ ν α Ψ := by
  funext h
  simp only [smallP, smallF, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem smallP_haarVol [MeasurableSpace k] [BorelSpace k] {J : Subgroup (GL A' k)} (ho : IsOpen (J : Set (GL A' k)))
    (hK : J ≤ KO k A') (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) :
    (haarVol (KO k A')).real J ≠ 0 ∧
      smallP (haarVol J) σ ν α Ψ = ((((haarVol (KO k A')).real J : ℝ) : ℂ))⁻¹ • smallP (haarVol (KO k A')) σ ν α Ψ := by
  obtain ⟨h0, h1⟩ := haar_ne_zero_ne_top (haarVol (KO k A')) ho hK
  have e : (haarVol (KO k A') J)⁻¹ • haarVol (KO k A') = haarVol J := by
    haveI : ((haarVol (KO k A') J)⁻¹ • haarVol (KO k A')).IsHaarMeasure :=
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0)
    exact eq_haarVol _ ho hK (by simp [ENNReal.inv_mul_cancel h0 h1])
  refine ⟨ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩, ?_⟩
  funext h
  rw [← e]
  simp only [smallP, smallF, integral_smul_measure, Pi.smul_apply, smul_eq_mul, Complex.real_smul, ENNReal.toReal_inv,
    Measure.real, Complex.ofReal_inv]
  ring

theorem fourierSum_ind (ψ : AddChar k Circle) {ϖ : kˣ} (hϖ : IsUnif ϖ) (P : Finset C) (c : ℂ) :
    IsNatDatum ϖ 0 (c • Set.indicator {Z : Matrix A C k | ∀ r s, Z r s ∈ (ValuativeRel.valuation k).integer} (1 : Matrix A C k → ℂ)) ∧
    fourierSum ψ ϖ 0 P (c • Set.indicator {Z : Matrix A C k | ∀ r s, Z r s ∈ (ValuativeRel.valuation k).integer} 1) 0 = c := by
  constructor
  · have := (depthSpace (A := A) ϖ 0 (stdLat k C)).smul_mem c (hasDepth_indicator hϖ 0 (stdLat k C))
    have e : {Z : Matrix A C k | ∀ r s, Z r s ∈ (ValuativeRel.valuation k).integer} = (matLat A (GlobalTheory.SplitFlip.stdLat k C) : Set _) :=
      Set.ext fun Z => mem_matLat_stdLat.symm
    rw [e]
    exact this
  · haveI : Subsingleton (Res k 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    haveI : Unique (A → P → Res k 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    rw [fourierSum_apply, if_pos (by simp), Fintype.sum_unique, Pi.smul_apply, Set.indicator_of_mem]
    · simp [pairCols]
    · intro r s
      simp only [setCols, Matrix.of_apply]
      split_ifs
      · exact liftRes_mem _ _ _
      · exact zero_mem _

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem notMem_of_standing {t : T} (hst : SquareStanding G t) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun hmem => hst.2 w hw (by
  have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
  rw [e]; exact Ideal.mul_mem_left _ _ hmem)

set_option maxHeartbeats 1000000 in

theorem local_charts (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E}
    {om : Rep D.sp.cm.sig Γ.V Γ.W} {om' : Rep D.sp.cm.sig Γ.V' Γ.W} (h : IsTripleOf W M t i j e Bs Γ X) {R Rf}
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf) (hti : IsDoublyCompatible t i j e Bs Γ X) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    ∃ (ιA ι : ToA G t i j w) (ιB ι' : ToB G t i j w) (l : ℂ), l ≠ 0 ∧ IsLinModelA W B t e Γ w ιA ∧ IsLinModelB W B t e Γ w ιB ∧
      IsMixModelA W B t e Γ w ι ∧ IsMixModelB W B t e Γ w ι' ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ m, IsNatDatum (unifAt w) m (ι φ) →
        ιA φ = fourierSum (psiAt W w)⁻¹ (unifAt w) m (Assignment.one.block _ _)ᶜ (ι φ)) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ m, IsNatDatum (unifAt w) m (ι' φ) →
        ιB φ = fourierSum (psiAt W w) (unifAt w) m (Assignment.one.block _ _) (ι' φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, zetaA G t i j w (ιA φ) = c • zetaB G t i j w (ιB φ') →
        Rf.p _ φ = (l * c) • Rf.p' _ φ' := by
  classical
  set v := w.under (𝓞 D.host.F) with hv
  letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv v
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv v
  have hT := hm.triple
  have hvT : v ∈ X.T := (hti.1.2.2.1 v).2 ⟨w, hw, rfl⟩
  let v' : Bs.P := ⟨v, hT.chars.sub hvT⟩
  have hτ : splitPrime (Bs.τ v') = w := hti.1.2.2.2 v' w hw rfl
  obtain ⟨ιA, ιB, hA, hB, -, -, hz⟩ := hm.fin.zeta v' hvT
  obtain ⟨jj, j1, j2, j3, j4⟩ := GlobalTheory.T.exists_placeIso_reading_components_characters hL W t i j X h.α h.β (Bs.τ v') w hτ
  let C0 : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
    ⟨basCols B e w, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1)))⁻¹.val (-(loc w (B.β (i + 1) j))⁻¹.val),
      by rw [basCols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, neg_mul_neg, Units.mul_inv, Units.mul_inv, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one],
      by rw [basCols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, neg_mul_neg, Units.inv_mul, Units.inv_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one]⟩
  let cj := GeneralLinearGroup.map (jj : Fv D.host.F v →+* Kw w) (Γ.W.bas v)
  have hcc : (Γ.W.bas v).val.map jj * (cj⁻¹ * C0).val = basCols B e w := congrArg Units.val (mul_inv_cancel_left cj C0)
  generalize cj⁻¹ * C0 = cc at hcc
  obtain ⟨g, hg, cA', lA⟩ := GlobalTheory.T.exists_mixed_chart_through_W_coordinate hL W B t i j M hst e Bs Γ X om om' h hT hti.1 v' w hτ jj j1 j2 cc hcc
  obtain ⟨g', cB, lB⟩ := GlobalTheory.T.square_standing_triple_theta_first hL W B t i j M hst e Bs Γ X om om' h hT hti v' w hτ jj j1 j2 cc hcc
  have hb := notMem_of_standing hst hw
  have hS := (Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2
  have hξ : (xiAt w)⁻¹ ≠ 0 := inv_ne_zero ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have dW : Γ.W.J.det ≠ 0 := h.JWW ▸ det_skewGram_ne _ _ e
  have dV : Γ.V.J.det ≠ 0 := by rw [h.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have dV' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (GlobalTheory.RouteCoords.gram_det_ne _)
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  rw [h.ψ] at hA hB
  obtain ⟨ι, i1, i2⟩ := exists_mixed (M := Γ.M) (ψ := W.ψ) hS.unif hS.cond j2 hξ j4 (h := invT cc) cA' hA.bij
    (fun u hu h0 φ hφ φ₁ h₁ ha => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew dV dW Γ.M W.ψ hstd _ _ _ u hu h0
      φ hφ φ₁ h₁ ha).1 ιA hA)
    fun x u hx hu => GlobalTheory.T.tensorSymplecticForm_at_split_finite_place hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew W.ψ _ _ _ x u hx hu
  obtain ⟨ι', k1, k2⟩ := exists_mixed (M := Γ.M') (ψ := W.ψ) hS.unif hS.inv.cond j2 hξ (χ := fun x => psiLoc W.ψ v (-x))
    (fun x => by rw [j4, AddChar.inv_apply, map_neg, mul_neg]) cB hB.bij
    (fun u hu h0 φ hφ φ₁ h₁ ha => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hT.base.cm Γ.V' Γ.W hT.geo.hV'.herm hT.geo.hW.skew dV' dW Γ.M' W.ψ hstd _ _ _ u hu
      ((pairM_comm _ _).trans h0) φ hφ φ₁ h₁ ha).2 ιB hB)
    fun x u hx hu => by
      rw [GlobalTheory.T.tensorSymplecticForm_at_split_finite_place hT.base.cm Γ.V' Γ.W hT.geo.hV'.herm hT.geo.hW.skew W.ψ (Bs.τ v') (Γ.V'.bas v) (Γ.W.bas v) x u hx hu, neg_sub]
  haveI := isHaarMeasure_haarVol (k := Kw w) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  haveI := isHaarMeasure_haarVol (k := Fv D.host.F v) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  obtain ⟨l₂, hl₂, z₂⟩ := GlobalTheory.T.zetaIdentity_persists_row_column_changes (Kw w) _ _ (rankW G t i j w) _ _ _ _ (finCongr (rankW₁ G t i j w)) (colsEq t e w) finSumFinEquiv
    (stdSplit ((locGrid G t w).rank_square i j)) (haarVol (KO (Kw w) _)) (haarVol (KO (Kw w) _))
    (unifAt w) ((locGrid G t w).nu i j) 1 g g' cc hg
  obtain ⟨l₁, hl₁, z₁⟩ := GlobalTheory.T.zetaIdentity_transport_localFieldIso (Fv D.host.F v) (Kw w) jj j2 (spW G i j).rank (Fin (spW₁ G i j).rank) _ finSumFinEquiv
    (haarVol (KO _ _)) (haarVol (KO _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (unifAt w) (exists_isUnif (k := Fv D.host.F v)).choose_spec
    hS.unif (chrW X.ν (Bs.τ v')) (chrW X.β (Bs.τ v')) _ 1 j3
  obtain ⟨ΘA, hΘA⟩ := exists_homeo jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) j2.1 j2.2.1
  obtain ⟨ΘB, hΘB⟩ := exists_homeo jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g' cc j2.1 j2.2.1
  have hfA := GlobalTheory.T.splitPlace_halves_eq_linear_model_lagrangians (Bs.τ v') w hτ (e.symm.trans finSumFinEquiv).symm _
    (GlobalTheory.RouteCoords.gram_det_ne (GlobalTheory.Grid.sgn true (spW G i j)))
  have hfB := GlobalTheory.T.splitPlace_halves_eq_linear_model_lagrangians (Bs.τ v') w hτ (e.symm.trans finSumFinEquiv).symm _ (GlobalTheory.RouteCoords.gram_det_ne (spW₁ G i j))
  have eA : ∀ φ Z, (LinearMap.funLeft ℂ ℂ ΘA.symm ∘ₗ ιA) φ (ΘA Z) = ιA φ Z := fun φ Z => congrArg (ιA φ) (ΘA.symm_apply_apply Z)
  have eB : ∀ φ Z, (LinearMap.funLeft ℂ ℂ ΘB.symm ∘ₗ ιB) φ (ΘB Z) = ιB φ Z := fun φ Z => congrArg (ιB φ) (ΘB.symm_apply_apply Z)
  refine ⟨LinearMap.funLeft ℂ ℂ ΘA.symm ∘ₗ ιA, ι, LinearMap.funLeft ℂ ℂ ΘB.symm ∘ₗ ιB, ι', l₁ * l₂, mul_ne_zero hl₁ hl₂,
    isLagrModel_chart (isLagrModel_of_isLin hA) ΘA (fun x y => by rw [hΘA, hΘA, hΘA, chart_add])
      (Set.ext fun u => (hfA u).1) (Set.ext fun u => (hfA u).2) fun u => (hΘA _).trans (lA u),
    isLagrModel_chart (isLagrModel_of_isLin hB) ΘB (fun x y => by rw [hΘB, hΘB, hΘB, chart_add])
      (Set.ext fun u => (hfB u).2) (Set.ext fun u => (hfB u).1) fun u => (hΘB _).trans (lB u),
    i1, k1, fun φ hφ m hm => funext fun S => ?_, fun φ hφ m hm => funext fun S => ?_, fun φ hφ φ' hφ' c hc => ?_⟩
  · obtain ⟨Z, rfl⟩ := ΘA.surjective S
    rw [eA, i2 φ hφ m hm, hΘA]
  · obtain ⟨Z, rfl⟩ := ΘB.surjective S
    rw [eB, k2 φ hφ m hm, hΘB, inv_inv]
  · have e6 : chrW X.α (Bs.τ v') = chrW X.ν (Bs.τ v') * chrW X.β (Bs.τ v') := by
      ext x
      simp [chrW, GlobalTheory.LFun.locChar, Chars.ν]
    rw [← map_smul]
    refine (hz φ hφ _ (Submodule.smul_mem _ _ hφ')).2 ?_
    rw [e6]
    rw [zetaA, zetaB, ← smallP_smul] at hc
    have := z₁ _ _ (z₂ _ _ hc)
    convert this using 2
    · funext Z
      rw [← eA, hΘA]
      rfl
    · funext Y
      rw [map_smul, Pi.smul_apply, ← eB, hΘB, smul_eq_mul, mul_assoc, mul_assoc]
      rfl

theorem zeta_flip (hL : L.Is μ₀) (W : G.Weil) {t : T} (i j : Fin D.R.m) (hst : SquareStanding G t) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) : levVol G t i j w ≠ 0 ∧ ∀ n Φ, depthAt G w ≤ n → IsNatDatum (unifAt w) n Φ →
      zetaA G t i j w (fourierSum (psiAt W w)⁻¹ (unifAt w) n (Assignment.one.block _ _)ᶜ (flipAt W t i j w n Φ)) =
        ((levVol G t i j w : ℝ) : ℂ)⁻¹ • zetaB G t i j w (fourierSum (psiAt W w) (unifAt w) n (Assignment.one.block _ _) Φ) := by
  have hS := (Good.isGood_of_notMem hL W hw (notMem_of_standing hst hw)).square i i.2 j j.2
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  haveI hμ := isHaarMeasure_haarVol h2.1 h2.2
  have key := smallP_haarVol h2.1 h2.2 (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    ((locGrid G t w).nu i j * 1)
  refine ⟨(key 0).1, fun n Φ hn hΦ => ?_⟩
  rw [flipAt, squareFlip, GlobalTheory.T.partialFourierSum_inverse_of_latticeDepth _ _ _ _ _ _ _ hS.unif hS.inv.cond _ (by
    rw [← latA_blockLat, ← Grid.alpha_div_beta]
    exact GlobalTheory.FrameDepth.hasDepth_phiA _ _ _ _ _ (hμ := hμ) _ _ _ _ _ _ hS.unif (hS.one_le.trans hn) (LocTensor.condLE_mono hS.unif hn hS.condν)
      (GlobalTheory.SplitFlip.FourierDepth.hasDepth_fourierSum hS.unif hS.cond n _ hΦ))]
  exact (GlobalTheory.T.primitiveFrameDatum_zetaIntegral_eq_smaller (Kw w) _ _ _ _ _ _ 1 _ n _ _ hS.unif).trans (key _).2

theorem zeta_std (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) {i j : Fin D.R.m} (X : TriG G i j) (hst : ∀ t, SquareStanding G t)
    (hA : IsFrame X.rA.β (G.Λ (.grid (i + 1) (j + 1)))) (hA' : IsFrame X.rA'.β (G.Λ (.grid i j))) (hX : IsFrame X.rW.β (latX G i j)) :
    ∃ x : ∀ w : Pl D.host.E, (Kw w)ˣ, ∀ t, ∀ w ∈ locPl G t, ValuativeRel.valuation (Kw w) (x w : Kw w) = 1 ∧
      locFst B t X w ∈ GlobalTheory.WeilM.SB _ ∧ locSnd B t X w ∈ GlobalTheory.WeilM.SB _ ∧
      zetaA G t i j w (locFst B t X w) = (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) • zetaB G t i j w (locSnd B t X w) := by
  have H : ∀ w : Pl D.host.E, ∃ x : (Kw w)ˣ, ∀ t, w ∈ locPl G t → ValuativeRel.valuation (Kw w) (x : Kw w) = 1 ∧
      zetaA G t i j w (locFst B t X w) = (((locGrid G t w).nu i j x : ℂˣ) : ℂ) • zetaB G t i j w (locSnd B t X w) := fun w => by
    by_cases hex : ∃ t, w ∈ locPl G t
    swap
    · exact ⟨1, fun t ht => absurd ⟨t, ht⟩ hex⟩
    obtain ⟨t₀, ht₀⟩ := hex
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.grid_frame_local_compact_membership hL B t₀ i j X (hst t₀) hA hA' hX w ht₀
    obtain ⟨x, hx, hz⟩ := GlobalTheory.T.bigZetaIntegral_eq_smul_smallZetaIntegral_of_integralChange (Kw w) _ _ _ _ (ordX G t₀ i j w) (stdSplit ((locGrid G t₀ w).rank_square i j)) finSumFinEquiv
      _ _ _ a1 a2 a3
    exact ⟨x, fun t _ => ⟨hx, hz (unifAt w) ((locGrid G t w).nu i j) 1 _ _
      (GlobalTheory.T.zetaIntegral_standardPair_first_eq_second (Kw w) ((locGrid G t w).nu i j) 1 (unifAt w) (X.c t w) _ _ (isUnif_unifAt w))⟩⟩
  choose x hx using H
  refine ⟨x, fun t w hw => ?_⟩
  have hS := (Good.isGood_of_notMem hL W hw (notMem_of_standing (hst t) hw)).square i i.2 j j.2
  obtain ⟨s1, s2⟩ := GlobalTheory.T.standardPair_mem_schwartzBruhat_of_conductorExponentLE (Kw w) ((locGrid G t w).nu i j) (unifAt w) _ (X.c t w) ((locGrid G t w).rank (i + 1, j + 1)) ((locGrid G t w).rank (i, j))
    hS.unif (by rw [← Grid.alpha_div_beta]; exact hS.condν)
  obtain ⟨ΘA, hΘA⟩ := exists_homeo (RingEquiv.refl (Kw w)) (Equiv.refl _) (ordX G t i j w) (chA B t X w) (invT (chX B t X w))
    continuous_id continuous_id
  obtain ⟨ΘB, hΘB⟩ := exists_homeo (RingEquiv.refl (Kw w)) (Equiv.refl _) (ordX G t i j w) (chB B t X w) (chX B t X w)
    continuous_id continuous_id
  refine ⟨(hx w t hw).1, ?_, ?_, (hx w t hw).2⟩
  · have : locFst B t X w = GlobalTheory.StdPairCone.stdA ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _ ∘ ΘA :=
      funext fun Z => by rw [Function.comp_apply, hΘA]; rfl
    rw [this]
    exact ⟨s1.1.comp_continuous ΘA.continuous, s1.2.comp_homeomorph ΘA⟩
  · have : locSnd B t X w = GlobalTheory.StdPairCone.stdB ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _ ∘ ΘB :=
      funext fun Z => by rw [Function.comp_apply, hΘB]; rfl
    rw [this]
    exact ⟨s2.1.comp_continuous ΘB.continuous, s2.2.comp_homeomorph ΘB⟩

end GlobalTheory.TopFlip

end
