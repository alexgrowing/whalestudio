import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumComplexConjugateOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReadsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTripleThetaKernelMinorsEqConstConjJet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotIntertw

open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)

variable {D : D7}

theorem xiN_of_reads {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem isFinPt_one (V : HSp D) {n : ℕ} (e : V.rank = n) :
    GlobalTheory.BotFormula.IsFinPt V 1 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  subst e
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  rw [map_one]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

theorem reads_of_fock {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} (hset : Setup ψ θ S T cc δ r)
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    ∃ G ∈ TT D (tor0 D cc δ) a d, Reads ψ θ hS hT cc δ r G f := by
  obtain ⟨G, hG, hR⟩ := GlobalTheory.VacLine.exists_reads hS hT hset hf hv
  have hRt : ∀ z, Reads ψ θ hS hT cc δ r (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G)
      (wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f) := fun z =>
    (GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hset G f hR z).smul _
  obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hset χS χT om hom 1 1 1 1 (isFinPt_one S hS) (isFinPt_one T hT) f hf 0
  refine ⟨G, ⟨hG, n, hn, fun x hx => ?_⟩, hR⟩
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ hset.crv.1.1 a d 1 1 _ _
    (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d) x hx
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hz
  have hp : n • pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ (n • z) := by
    funext τ i j
    simp [pt, embV, tor0]
    ring
  have h2 := hL (n • z) (fun i j => ⟨_, hz i j, by
    have h0 : (0 : Matrix (Fin d) (Fin a) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    simp⟩)
  have e1 : om (1, 1) = 1 := map_one om
  rw [e1, Module.End.one_apply, Module.End.one_apply] at h2
  have h3 := hRt (n • z)
  have h4 := hRt 0
  rw [GlobalTheory.NormSum.VacMove.pt_zero, GlobalTheory.NormSum.wd_zero] at h4
  rw [GlobalTheory.NormSum.VacMove.pt_zero] at h2
  rw [← h2] at h3
  rw [hp]
  exact GlobalTheory.VacLine.reads_inj hset h3 h4

theorem conj_datum {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (s : T) :
    IsThetaFunO W.ψ A WW (fun w => starRingEnd ℂ (X.f s w)) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ A WW) W.θ τ (cplxO 1 1) (fun w => starRingEnd ℂ (X.f s w)) := by
  have hI := hX.is
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) := (GlobalTheory.ConstRatio.theta_f hI s).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem s)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f s) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst s)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO W.ψ (GlobalTheory.ChiGrid.negSp A) WW (X.f s) from hf), fun τ => ?_⟩
  have h := hv τ
  rw [(hX.std.2.2 τ).1, (hX.stdW.2.2 τ).1] at h
  exact GlobalTheory.BotFormula.ConjJet.isFockVacAt_conj hψ hθ A WW _ hf τ h

theorem bottom_finParts {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    {i j : Fin D.R.m} {s : T} {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪 : Ideal (𝓞 D.host.E)}
    (hB : IsBottom G s i j 𝔪 P P') :
    HasFinPart (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))⁻¹ P.W.chV P.W.ep ∧
    HasFinPart ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
      (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ P.W.chV' (-P.W.ep') := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have h1 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) x y hxy
    have h2 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ hL.eta x y hxy
    have e : (betaH G i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((G.ch.chiH (D.R.m - i)).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) *
          L.C.eta.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) ^ (rankV D i j % 2))⁻¹ := rfl
    rw [hB.chars.1 y, e, MonoidHom.inv_apply, Circle.coe_inv, MonoidHom.mul_apply, MonoidHom.pow_apply, Circle.coe_mul,
      Circle.coe_pow, h1, h2]
    simp
  · have eν : ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
        (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ = G.nu s i (j + 1) := by
      rw [inv_div]; exact mul_div_mul_right_eq_div _ _ _
    have e : (nuH G s i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((nuH G s i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y))⁻¹ := rfl
    rw [eν, zpow_neg, hB.chars.2 y, e, inv_inv]
    exact GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy

theorem bottom_intertwining : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ (r : ℂ) (rc : ℝ), r ≠ 0 ∧ (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
          GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
          ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w))) := by
  intro _ _ _ hInp _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hstd i j A A' WW X δ t0 hX
  by_cases hC : Crv D ⊤ δ
  swap
  · refine ⟨1, 2 * Formalism.L2.Pj.xiR D, one_ne_zero, fun h => absurd h hC, fun τ => ?_, fun s Q P P' _ => absurd P.crv hC⟩
    rw [GlobalTheory.FockPos.norm_embedding_xi0_eq]; simp
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  refine ⟨-δ, (area (lamOf D ⊤ δ))⁻¹, neg_ne_zero.2 hδ, fun _ => rfl, fun τ => ?_, fun s Q P P' hB ea ed => ?_⟩
  · have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq]
    field_simp
  have hSet : Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hstd, W.θ_is, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hw := GlobalTheory.ConjWeilBack.weil_conjRep_of_neg W.ψ A WW _ _ (X.ω s) (hX.is.weil s)
  obtain ⟨hth, hfock⟩ := conj_datum hX s
  obtain ⟨G₀, hG₀, hR₀⟩ := reads_of_fock ea.symm ed.symm hSet hw hth hfock
  obtain ⟨hcS, hcT⟩ := bottom_finParts G hL hB
  have hTT0 : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := GlobalTheory.NormSum.VacMove.vac_TT (hInp D).g1 P.crv P.vac.1
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet _ hTT0
  refine ⟨?_, fun h g x y hg hy => ?_⟩
  · rw [xiN_of_reads W.θ_is _ _ hδ hR₀]; exact hG₀
  · have hv := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw (hInp D) t0 P.pt0
      P.even_mul P.vac hcS hcT x h y g hy hg f₀ hf₀
    have hm := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw P.vac.1 x h y g hy hg 1
      f₀ hf₀ (by rw [one_smul]; exact hv) G₀ hG₀ _ hR₀
    rw [one_smul] at hm
    have e1 : (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
        GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (fun w => starRingEnd ℂ (X.f s w)) := by
      change _ = GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (X.f s))
      rw [GlobalTheory.AdjTr.conjRep_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rfl
    rw [e1, xiN_of_reads W.θ_is _ _ hδ hm, xiN_of_reads W.θ_is _ _ hδ hR₀]

end GlobalTheory.BotIntertw

end
