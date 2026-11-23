import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleUnitConstant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleUnitConstantStatement

section
noncomputable section
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead
namespace GlobalTheory.StdRead
variable {D : D7}
variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
end GlobalTheory.StdRead
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.StdRead
theorem standard_module_bottom_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  intro _ _ _ hInp _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hW i j A A' WW X δ t0 hX hβ r rc _ hr hrc _
  have hI := hInp D
  by_cases hC : Crv D ⊤ δ
  swap
  · exact ⟨1, one_ne_zero, fun s Q P _ _ => absurd P.crv hC⟩
  obtain rfl := hr hC
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hIs := hX.is
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hs : GlobalTheory.NormExact.Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hW, hθ, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  have hrc' : rc = (area (lamOf D ⊤ δ))⁻¹ := by
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    have h1 := hrc τ
    have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    have hx := GlobalTheory.NormExact.xiR_pos D
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq] at h1
    field_simp
    have : 2 * Formalism.L2.Pj.xiR D * (rc * area (lamOf D ⊤ δ) - 1) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith
  subst hrc'
  have hΛ : ∀ {V : HSp D} (ρ : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), ρ.IsStd → ρ.Λ = stdL D V.rank := fun ρ h => by
    ext y
    rw [h.2.1]
    simp [stdL, Submodule.mem_pi, Submodule.mem_one]
  have hΛA := hΛ X.rA hX.std
  have hΛW := hΛ X.rW hX.stdW
  have hv : IsVacO W.ψ W.θ A WW (fun _ => 1) (fun _ => 1) (stdL D A.rank : Set (Fin A.rank → D.host.E))
      (stdL D WW.rank : Set (Fin WW.rank → D.host.E)) (fun w => starRingEnd ℂ (X.vac w)) := by
    have h := GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
    rwa [hΛA, hΛW, show X.rA.s = fun _ => 1 from funext fun τ => (hX.std.2.2 τ).1,
      show X.rW.s = fun _ => 1 from funext fun τ => (hX.stdW.2.2 τ).1] at h
  obtain ⟨G0, hG0, hne, hread⟩ := GlobalTheory.T.adelicVacuum_standardLattices_readsTheta W.ψ W.θ A WW rfl rfl δ hcc hs _ hv
  obtain ⟨κ, hκ, hc⟩ := exists_const hI δ t0 G0 hG0 hne
  have hc' : ∀ (a d : ℕ) (ea : a = A.rank) (ed : d = WW.rank) (e0 : VC D a d → ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
      oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 → ∃ u, IsPh u ∧ (κ * u) • e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) ∧
        GlobalTheory.NormExact.Reads W.ψ W.θ ea.symm ed.symm ⊤ δ 1 ((κ * u) • e0) (fun w => starRingEnd ℂ (X.vac w)) := by
    rintro a d rfl rfl e0 h1 h2 h3
    obtain ⟨u, hu, e⟩ := hc e0 hC h1 h2 h3
    exact ⟨u, hu, e ▸ hG0, e ▸ hread⟩
  refine ⟨κ, hκ, fun s Q P P' hB => ?_⟩
  have ea : P.a = A.rank := hB.rank.1.trans hX.rank.symm
  have ed : P.d = WW.rank := by rw [hB.rank.2.2.1, ← hIs.rank, hX.rank, hX.rank']
  obtain ⟨u, hu, hTh, hrd⟩ := hc' _ _ ea ed P.e0 P.pt0 P.vac P.W.nz
  obtain ⟨c0, cI⟩ := GlobalTheory.T.squareNuConductorExponents_pos_prod_eq_modulus G hL s i j (X.c s) (hIs.expo s)
  obtain ⟨q1, q2⟩ := GlobalTheory.SqTop.BotT.pde_ne_q hR
  have hm : GoodMod (X.e s) (GlobalTheory.SqTop.modT G s) := ⟨_, _, hIs.idem s, c0, cI.symm,
    GlobalTheory.FunObj.StdDatum.TwBig.modT_isCoprime_bb hL G s (GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent G.pl q1 q2)⟩
  have hν : GlobalTheory.NormExact.HasFinPart (G.nu s i (j + 1))⁻¹ P.W.chV' P.W.ep' := fun x y hxy => by
    rw [hB.chars.2 y, MonoidHom.inv_apply, Circle.coe_inv, GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy]
    exact (Units.val_inv_eq_inv_val _).symm
  obtain ⟨Tm, hTm, hf⟩ := GlobalTheory.T.schrodingerModel_complexConjugate_negForm W.ψ hW A WW _ _ _ _ _ _ (hIs.fst s)
  have eν : Lc.mu s (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu s i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have eI : X.ideal (locPl G) s = GlobalTheory.SqTop.modT G s := cI
  rw [hΛA, hΛW] at hTm
  rw [eν, eI, hβ] at hf
  obtain ⟨u', hu', hrf⟩ := reads_std hI P ea.symm ed.symm hcc hs hv hTh hrd hm hν (killsCong hL G s i j)
    (hΛA ▸ hIs.rigA.2.1) hB.std hTm hf
  have hw := (hu.mul hu').conj
  refine ⟨_, fun h => by simpa [h] using hw.1, hw.2.1, fun p _ _ lam => hw.2.2 p lam, fun ea' ed' => ?_⟩
  rw [xiN_eq hθ _ _ hδ hrf, Complex.conj_conj, mul_assoc]
end GlobalTheory.StdRead
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_module_bottom_datum_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  first | exact @_root_.GlobalTheory.StdRead.standard_module_bottom_datum | exact _root_.GlobalTheory.StdRead.standard_module_bottom_datum | (intros; apply _root_.GlobalTheory.StdRead.standard_module_bottom_datum <;> assumption)
end
