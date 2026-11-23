import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyVacuumData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
set_option maxHeartbeats 4000000 in
theorem exists_locX_std_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX) (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u vac PP k _ _ _ _ _ _ q hidem hunder hunit hval
  have hI := hW.tr.ok
  obtain ⟨hsI, hXsp, hX'sp, -⟩ := hI.spaces
  have hLX : ∀ j, ((GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j)) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := fun j => GlobalTheory.AdForm.PinInhab.lat_X hI j
  have hLT : (((_root_.GlobalTheory.Fam.pk_z W).ΛX : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : Set (Fin (I.rec7 l Z).sp.X'.rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := by
    rw [GlobalTheory.XGeoStd.eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX]
    exact GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hsI _ hX'sp
  have hβ : (_root_.GlobalTheory.Fam.pk_z W).βX = 1 := hW.pk.bot.pins.betaStd.2
  have hm := (I.rec7 l Z).R.two_le_m
  obtain ⟨s, hs⟩ : ∃ s, s + 1 + 1 = (I.rec7 l Z).R.m := ⟨(I.rec7 l Z).R.m - 2, by omega⟩
  have rX : ∀ j, j ≤ s + 1 → (I.rec7 l Z).R.k + j + j * (I.rec7 l Z).R.t = ((I.rec7 l Z).sp.X j).rank := by
    intro j hj
    rw [Formalism.L2.Forms.rankN _ j (by omega)]
    show _ = (I.rec7 l Z).R.k + j * ((I.rec7 l Z).R.t + 1)
    ring
  have rT : (I.rec7 l Z).R.k + (s + 1) + (s + 2) * (I.rec7 l Z).R.t = (I.rec7 l Z).sp.X'.rank := by
    rw [Formalism.L2.Forms.rankP, show (I.rec7 l Z).R.N (I.rec7 l Z).R.m = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m * ((I.rec7 l Z).R.t + 1) from rfl,
      ← hs]
    have e : (s + 1 + 1) * ((I.rec7 l Z).R.t + 1) = (s + 2) * (I.rec7 l Z).R.t + (s + 1) + 1 := by ring
    rw [e]
    omega
  have rM : (I.rec7 l Z).sp.X'.rank + 1 = ((I.rec7 l Z).sp.X (s + 1 + 1)).rank := by
    rw [hs]; exact GlobalTheory.AdForm.LiveModel.rk_top _
  set κ := (I.rec7 l Z).R.k
  set τ := (I.rec7 l Z).R.t
  let eX : ∀ j (hj : j ≤ s + 1), XIx (Fin κ) (Fin τ) j ≃ Fin ((I.rec7 l Z).sp.X j).rank := fun j hj =>
    (GlobalTheory.Fam.Inhab.blockOrd κ τ j j).trans (finCongr (rX j hj))
  have oX : ∀ j hj, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (eX j hj) := fun j hj a => by
    simpa [eX] using GlobalTheory.Fam.Inhab.isOrd_xPos κ τ j a
  let eT : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (I.rec7 l Z).sp.X'.rank :=
    (GlobalTheory.Fam.Inhab.blockOrd κ τ (s + 1) (s + 2)).trans (finCongr rT)
  have oT : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eT := fun a => by
    simpa [eT] using GlobalTheory.Fam.Inhab.isOrd_zPos κ τ (s + 1) (s + 2) a
  let eM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit ≃ Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank :=
    ((Equiv.sumCongr eT (finOneEquiv.symm)).trans finSumFinEquiv).trans (finCongr rM)
  have eM_l : ∀ a, (eM (Sum.inl a) : ℕ) = eT a := fun a => by simp [eM]
  have eM_r : (eM (Sum.inr ()) : ℕ) = (I.rec7 l Z).sp.X'.rank := by simp [eM]
  set π := (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u) with hπ
  have hπ0 : π ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  let dM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit → k := Sum.elim (fun _ => 1) fun _ => π
  have hd0 : ∀ y, dM y ≠ 0 := by rintro (a | a) <;> simp [dM, hπ0]
  have hdv : ∀ y, valuation k (dM y) = 1 := by rintro (a | a) <;> simp [dM, hval]
  refine ⟨{ k := k, q := q, idem := hidem, under := hunder, unit := hunit, s := s, hs := hs,
             FX := fun j hj => GlobalTheory.Fam.Inhab.stdFr k (eX j hj), FT := GlobalTheory.Fam.Inhab.stdFr k eT, FM := diagFr eM dM hd0,
             last := ?_, latX := ?_, latM := ?_, latT := ?_, frameTop := ?_ },
    fun j hj => GlobalTheory.Fam.Inhab.isStdFr_stdFr (oX j hj), GlobalTheory.Fam.Inhab.isStdFr_stdFr oT⟩
  · have hpr1 : (GlobalTheory.LocMod.ofSplit q).pr (1 : (I.rec7 l Z).host.E) = 1 := by simp [GlobalTheory.LocMod.Place.pr]
    have hpr0 : (GlobalTheory.LocMod.ofSplit q).pr (0 : (I.rec7 l Z).host.E) = 0 := by simp [GlobalTheory.LocMod.Place.pr]
    ext r c
    rcases c with c | c
    · rw [Matrix.fromCols_apply_inl]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inl c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inl, mul_one]
      change (1 : Matrix _ _ k) r (eM (Sum.inl c)) =
        (((oTop l Z hI (s + 1 + 1) hs).iA.map (GlobalTheory.LocMod.ofSplit q).pr *
          (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT :
            Matrix (Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank) _ k) r c)
      exact entry_inl _ hpr0 hpr1 eT _ (oTop_iA l Z hI (s + 1 + 1) hs) r c _ (eM_l c)
    · rw [Matrix.fromCols_apply_inr]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inr c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inr]
      change (1 : Matrix _ _ k) r (eM (Sum.inr c)) * π =
        ((oTop l Z hI (s + 1 + 1) hs).iB.map (GlobalTheory.LocMod.ofSplit q).pr *ᵥ fun i => (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.zeta I l Z u i)) r
      exact entry_inr _ hpr0 hpr1 _ (oTop_iB l Z hI (s + 1 + 1) hs) _ (GlobalTheory.XGeoStd.piE I l Z u) (fun _ => rfl) r _ eM_r
  · intro j hj
    exact intIn_stdFr q _ _ (hLX j) (eX j hj)
  · exact intIn_diagFr q _ _ (hLX (s + 1 + 1)) eM dM hd0 hdv
  · exact intIn_stdFr q _ _ hLT eT
  · refine ⟨eT, oT, fun b hb => ?_⟩
    have h1 : b.map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
      have h2 : b.map (toEAf (I.rec7 l Z)) = (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank)
          (AE (I.rec7 l Z))).map (toEAf (I.rec7 l Z)) := by
        rw [hb, hβ, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [(GlobalTheory.LocMod.ofSplit q).map_pi_eq_of_toEAf h2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : (GlobalTheory.Fam.Inhab.stdFr k eT).β.submatrix id eT.symm = 1 := by
      change ((1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT).submatrix id eT.symm = 1
      rw [Matrix.submatrix_submatrix]
      simp
    rw [h3, show (GlobalTheory.XGeoStd.xgeo l Z hI vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX).bT = 1 from rfl, GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul, h1]
end GlobalTheory.XGeoStd.Frames
end
end
