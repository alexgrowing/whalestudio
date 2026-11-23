import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SymRead

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevPin
set_option maxHeartbeats 4000000 in
theorem exists_levelData_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b))), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ (l : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k), _root_.GlobalTheory.Fam.SymReadAlt W l S → (∀ PP, LocY (l PP) y v.N (_root_.GlobalTheory.Fam.pk_z W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc) → (∀ PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((l PP).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (l PP).FT) → ∃ JG eG eGT dG, ∃ (n : ℕ) (G : Fin n → GLoc { v with JG := JG, eG := eG, eGT := eGT, dG := dG }) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eG j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) (dG j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eGT j h)) ∧ (∀ j row col, _root_.GlobalTheory.Fam.LocalGroupReading (⟨mkGeo m b, j, row, col⟩ : _root_.GlobalTheory.Fam.FamilyCharacter W u) G pl) ∧ ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (G i).FT ∧ (G i).z₀ = fun r => (ofSplit (G i).q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ a y m b v hc hτ hNT hgP hTP l S hSym hY hStd
  classical
  have hψ : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hc.std
  choose ν hν using fun PP : (_root_.GlobalTheory.Fam.pk_z W).Pg => GlobalTheory.SplitWeil.exists_isUnitVol (l PP).k
  choose eg egT cg heg hegT hcm hcp hct sEg sCg using fun PP => exists_locComb (l PP) (S PP) (hY PP) (ν PP) hψ
  have hPv : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, (l PP).q.v ∈ v.gP := fun PP => (hgP _).2 ⟨PP.1, PP.2, (l PP).under⟩
  let n := Fintype.card (_root_.GlobalTheory.Fam.pk_z W).Pg
  let pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg := (Fintype.equivFin _).symm
  have hEG : ∀ j, ∃ c' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (eg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => eg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sEg (pl i) j w hw)) _
  choose eG hEGs hEGf using hEG
  have hDG : ∀ j, ∃ c' : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (cg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => cg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sCg (pl i) j w hw)) _
  choose dG hDGs hDGf using hDG
  have hsj : ∀ (i : Fin n) (j : ℕ), j + 2 * 0 + 2 = D.R.m → (l (pl i)).s = j := fun i j h => by
    have := (l (pl i)).hs
    omega
  let eT : ∀ (i : Fin n) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m), WO (Yc D (j + 1)) D.sp.X' →₀ ℂ := fun i j h =>
    cast (congrArg (fun n' => WO (Yc D (n' + 1)) D.sp.X' →₀ ℂ) (hsj i j h)) (egT (pl i))
  have hEGT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ,
      (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (eT i j h) f') f := fun j h =>
    exists_fold _ _ _ _ (fun i => eT i j h) (fun i => mxAt_cast (F := fun n' => Yc D (n' + 1)) (hsj i j h) _
      (fun w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w ((hegT (pl i)).1 w hw))) _
  choose eGT hEGTs hEGTf using hEGT
  let JG : ∀ j, Subgroup (GA D (Yc D j)) := fun j => GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ v.gP) ⊓
    ⨅ (i : Fin n) (a' : ℕ) (ha : j + a' = (l (pl i)).s + 1),
      frameSub ((GeneralLinearGroup.map (l (pl i)).q.pr).comp (matHom (Yc D j))) ((hY (pl i)).FY j a' ha)
        ((((S (pl i)).T (Fin D.R.t)).lev j a' ha).J)
  let v' : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)) := { v with JG := JG, eG := eG, eGT := eGT, dG := dG }
  let G : Fin n → GLoc v' := fun i =>
    { k := (l (pl i)).k
      ν := ν (pl i)
      unitVol := hν (pl i)
      q := (l (pl i)).q
      unit := (l (pl i)).unit
      s := (l (pl i)).s
      hs := (l (pl i)).hs
      S := S (pl i)
      char := hSym.char (pl i)
      FX := (l (pl i)).FX
      FT := (l (pl i)).FT
      FM := (l (pl i)).FM
      FY := (hY (pl i)).FY
      sc := (hY (pl i)).sc
      sc_unit := (hY (pl i)).sc_unit
      sc_step := (hY (pl i)).sc_step
      hz_unit := (hY (pl i)).hz_unit
      bes := (hY (pl i)).bes
      jac := (hY (pl i)).jac
      z₀ := fun r => (ofSplit (l (pl i)).q).pr (a.ζ₀ r)
      last := (l (pl i)).last
      tau := fun h => by
        rw [show v'.τ = y.τ from hτ]
        exact (hY (pl i)).tau h
      latX := (l (pl i)).latX
      latM := (l (pl i)).latM
      latY := (hY (pl i)).latY
      latT := by
        rw [show v'.NT = a.LT from hNT]
        exact (l (pl i)).latT
      eg := eg (pl i)
      eg_is := heg (pl i)
      egT := egT (pl i)
      egT_is := hegT (pl i)
      cg := cg (pl i)
      cg_mid := hcm (pl i)
      cg_pen := hcp (pl i)
      cg_top := hct (pl i) }
  refine ⟨JG, eG, eGT, dG, n, G, pl, ?_, fun j => ⟨hEGs j, hDGs j, hEGTs j⟩, ?_, fun i => ⟨(hStd (pl i)).1, (hStd (pl i)).2, rfl⟩⟩
  · refine ⟨fun i i' h => pl.injective (Subtype.ext (under_inj hTP (pl i).2 (pl i').2 ?_)), fun p => ?_, fun j _ g => ?_,
      fun j _ f _ => hEGf j f, fun j h => ⟨fun i => eT i j h, fun i => cast_heq _ _, fun f _ => hEGTf j h f⟩,
      fun j _ f _ => hDGf j f⟩
    · have e1 := (l (pl i)).under
      have e2 := (l (pl i')).under
      change (l (pl i)).q.v = (l (pl i')).q.v at h
      rw [← e1, ← e2, h]
    · change p ∈ v.gP ↔ ∃ i, p = (l (pl i)).q.v
      rw [hgP]
      constructor
      · rintro ⟨PP, hPP, rfl⟩
        refine ⟨pl.symm ⟨PP, hPP⟩, ?_⟩
        rw [(l _).under, Equiv.apply_symm_apply]
      · rintro ⟨i, rfl⟩
        exact ⟨(pl i).1, (pl i).2, (l _).under⟩
    · change g ∈ JG j ↔ _
      simp only [JG, Subgroup.mem_inf, Subgroup.mem_iInf, mem_frameSub]
      rfl
  · intro j row col
    refine ⟨fun i => ⟨(l (pl i)).idem, (l (pl i)).under⟩, fun i j h1 h2 => hSym.mu (pl i) j h1 h2,
      fun i j c hc => (hY (pl i)).frame j c hc, fun i => (l (pl i)).frameTop, fun g => ⟨?_, ?_⟩⟩
    · rw [hSym.grp g]
      constructor
      · intro h i
        exact h (pl i)
      · intro h PP
        obtain ⟨i, rfl⟩ := pl.surjective PP
        exact h i
    · intro hg x hx
      rw [hSym.chr g hg (Equiv.piCongrLeft (fun PP => (S PP).P.J) pl x) (fun PP => ?_)]
      · rw [← Equiv.prod_comp pl]
        simp only [Equiv.piCongrLeft_apply_apply]
        rfl
      · obtain ⟨i, rfl⟩ := pl.surjective PP
        rw [Equiv.piCongrLeft_apply_apply]
        exact hx i
end GlobalTheory.LevPin
end
