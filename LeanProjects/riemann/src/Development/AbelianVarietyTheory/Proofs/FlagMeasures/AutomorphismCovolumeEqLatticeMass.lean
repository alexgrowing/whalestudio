import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CovolIdx
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralStabiliserNormalisedHaarStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsTermAutomorphismsEqMovedStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPointsStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovMass

variable {D : D7} (X : HidaSetting D)

noncomputable def realPt (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : X.B.I.Ginf :=
  (Classical.choose ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1

theorem realPt_spec {γ : Formalism.HermitianLatticesTheory.isom (VS D).hT} {x : X.B.I.GA} (h : RatLink X x γ.1) : realPt X γ = x.1 := by
  have hs := Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)
  unfold realPt
  rw [hs.2 x h]

theorem realPt_link (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : ∃ x : X.B.I.GA, RatLink X x γ.1 ∧ realPt X γ = x.1 :=
  ⟨_, (Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1, rfl⟩

noncomputable def realPtHom : Formalism.HermitianLatticesTheory.isom (VS D).hT →* X.B.I.Ginf where
  toFun := realPt X
  map_one' := by
    obtain ⟨x, hx, e⟩ := realPt_link X 1
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x x _ _ hx hx)
    have h2 := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x (x⁻¹) _ _ hx h.2.1).1
    have h3 : RatLink X (x * x⁻¹) (1 : Formalism.HermitianLatticesTheory.isom (VS D).hT).1 := by simpa using h2
    rw [realPt_spec X h3]; simp
  map_mul' := by
    intro γ δ
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    obtain ⟨y, hy, ey⟩ := realPt_link X δ
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).1
    rw [realPt_spec X (γ := γ * δ) h, ex, ey]; rfl

theorem realPtHom_injective : Function.Injective (realPtHom X) := by
  intro γ δ h
  obtain ⟨x, hx, ex⟩ := realPt_link X γ
  obtain ⟨y, hy, ey⟩ := realPt_link X δ
  have h' : x.1 = y.1 := by rw [← ex, ← ey]; exact h
  exact Subtype.ext (((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).2.2 h')

theorem realPts_eq_map (H : Subgroup ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (hH : H ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    realPts X (H : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = ((H.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (realPtHom X) : Set X.B.I.Ginf) := by
  ext y
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨⟨n, hH hn⟩, hn, realPt_spec X (γ := ⟨n, hH hn⟩) hx⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    exact ⟨x, γ.1, hx, ex, hγ⟩

theorem realPts_countable (S : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) : (realPts X S).Countable := by
  have := Formalism.L2.SG.TermOp.Vanish.countable_nf X.B.I.E
  have hsub : realPts X S ⊆ ⋃ M : Fin X.B.I.n → Fin X.B.I.n → X.B.I.E,
      {y : X.B.I.Ginf | ∀ v, uMat (y v) = (X.B.I.P v)⁻¹ * (Matrix.of M).map (X.B.I.φ v) * X.B.I.P v} := by
    rintro _ ⟨x, n, ⟨M, -, h1, -⟩, rfl, -⟩
    exact Set.mem_iUnion.2 ⟨fun i j => (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) i j, h1⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun M => Set.Subsingleton.countable ?_)
  intro y hy y' hy'
  funext v
  exact Subtype.ext (Units.ext ((hy v).trans (hy' v).symm))

end GlobalTheory.CovMass

theorem GlobalTheory.CovMass.covol_eq_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∀ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ ROinf t₀ ∧ s * y ∈ K) → (μR K).toReal = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat ρ t₀.lam) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin K hK
  obtain ⟨hKm, hKu⟩ := hK
  have hlink := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hgrp := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).1
  obtain ⟨KA, ⟨hKAm, hKAu⟩, hKA⟩ :=
    GlobalTheory.T.covolume_integralStabiliser_normalisedHaar D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin
  have hRO := GlobalTheory.T.realPoints_termAutomorphisms_eq_movedStabilizer D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hfin1, hfin2⟩ := GlobalTheory.T.latticeStabiliser_commensurable_integralPoints (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ _ G hk (c.lat ρ t₀.lam) hterm.1

  let cj : ((VS D).V ≃ₗ[D.host.E] (VS D).V) →* G.GLV :=
    { toFun := c.grp ρ
      map_one' := by ext x; simp [GlobalTheory.HL.GCoord.grp]
      map_mul' := by intro m n; ext x; simp [GlobalTheory.HL.GCoord.grp] }
  have hcj : ∀ n, cj n = c.grp ρ n := fun _ => rfl
  have hcjs : Function.Surjective cj := fun x => hgrp.2.2.2.1 ρ x
  have hconj : ∀ n, c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * n * t₀.lin) = c.grp ρ n := by
    intro n
    have h1 : ∀ y, t₀.lin (t₀.lin⁻¹ y) = y := fun y => by
      show (t₀.lin * t₀.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    have h2 : ∀ z, t₀.lin ((ρ * t₀.lin).symm z) = ρ.symm z := fun z => by
      rw [LinearEquiv.eq_symm_apply]; exact (ρ * t₀.lin).apply_symm_apply z
    ext x
    simp only [GlobalTheory.HL.GCoord.grp, LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_trans_apply, h1, h2]

  have hStN : ∀ g, g ∈ G.St → g ∈ G.N := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').1, he⟩
  have hStN' : ∀ g, g ∈ G.St → g ∈ G.N' := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').2, he⟩
  have hK0St : G.K0 ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1.1, he⟩
  have hLSt : G.stabL (c.lat ρ t₀.lam) ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1, he⟩
  have hStI : G.St.comap cj ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn =>
    ((hgrp.1 n).2 (hStN _ hn)).1
  set P := G.K0.comap cj with hP
  set Q := (G.stabL (c.lat ρ t₀.lam)).comap cj with hQ
  have hPI : P ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hK0St hn)
  have hQI : Q ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hLSt hn)
  set A := (P.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hA
  set B := (Q.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hB
  have hAset : (A : Set X.B.I.Ginf) = realPts X {σ | c.grp ρ σ ∈ G.K0} :=
    (GlobalTheory.CovMass.realPts_eq_map X P hPI).symm
  have hBset : (B : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.ROinf t₀ := by
    rw [hRO]; exact (GlobalTheory.CovMass.realPts_eq_map X Q hQI).symm
  have hAmem : ∀ y, y ∈ A ↔ y ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} := fun y => by
    rw [← hAset]; rfl
  have hBmem : ∀ y, y ∈ B ↔ y ∈ Formalism.L2.SG.TermOp.ROinf t₀ := fun y => by
    rw [← hBset]; rfl

  obtain ⟨γw, s, s', μw, hγw, hs, hs', hdec, hμwH, hμwS, hμR⟩ := hPin
  have hH := Formalism.L2.SG.Pf.VolPinAsm.pinned_haar t₀ w γw s s' μw hs hs' hdec hμwH
  rw [← hμR] at hH
  have hAR : ∀ y ∈ A, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
    intro y hy
    obtain ⟨x, n, hx, rfl, hn⟩ := (hAmem y).1 hy
    have hnS : c.grp ρ n ∈ G.St := hK0St hn
    refine ⟨((hlink.2.2 u x n hx).1).1 ((hgrp.1 n).2 (hStN _ hnS)), ?_⟩
    have hm : t₀.lin⁻¹ * n * t₀.lin ∈ NRat (lf D (X.Fu u')) :=
      (hgrp.2.1 _).2 (by rw [hconj]; exact hStN' _ hnS)
    have hl : RatLink X (t₀.pt⁻¹ * x * t₀.pt) (t₀.lin⁻¹ * n * t₀.lin) :=
      (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ t₀.rep.2.1 t₀.rep.2.1).2.1 hx).1 t₀.rep.2.1).1
    have h2 := ((hlink.2.2 u' _ _ hl).1).1 hm
    simpa [Prod.fst_mul, Prod.fst_inv] using h2
  have hBR : ∀ y ∈ B, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := fun y hy =>
    Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset t₀ ((hBmem y).1 hy)
  haveI hCA : Countable A := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.K0}).to_subtype
    rw [← hAset] at this; exact this
  haveI hCB : Countable B := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)}).to_subtype
    rw [← hRO, ← hBset] at this; exact this

  have hiA : B.relIndex A = (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hPI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hiB : A.relIndex B = G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hQI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hcov := Formalism.L2.SG.Pf.CovolIdx.covol_commens μR (Formalism.L2.SG.TermOp.Vanish.Rset t₀) hH.2.2.1 A B
    (fun x hx => hH.2.2.2 x (hAR x hx)) (fun x hx => hH.2.2.2 x (hBR x hx))
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hAR x hx) hy)
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hBR x hx) hy) KA K hKAm hKm
    (fun y hy => by simpa only [hAmem] using hKAu y hy) (fun y hy => by simpa only [hBmem] using hKu y hy)
    (by rw [hiA]; exact hfin1) (by rw [hiB]; exact hfin2)
  rw [hiA, hiB, hKA] at hcov
  set a := (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 with ha
  set b := G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) with hb
  set gi : ℝ := ((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹ with hgi
  have hgi0 : 0 ≤ gi := by rw [hgi]; positivity
  have hbne : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hfin2
  have hKeq : μR K = ENNReal.ofReal gi * (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
    rw [hcov, ENNReal.mul_div_cancel_right hbne (by simp)]
  rw [hKeq, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hgi0]
  simp only [ENNReal.toReal_natCast]
  unfold GlobalTheory.HL.GFrames.mu GlobalTheory.HL.invVol
  rw [← ha, ← hb]
  ring
