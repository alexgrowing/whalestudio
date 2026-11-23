import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

theorem GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q →
    ∀ x : GL (Fin (Vc D j).rank) (Lev.EAf D),
      (x ∈ lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
        x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) ∧
          X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U) ∧
      ∀ (hx : x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t))
        (hu : X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U),
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x : ℂˣ) : ℂ) =
          ((levFn (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x : ℂˣ) : ℂ) *
            Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  classical
  intro D X E Y i j b t h1 h2 x
  have hB := Y.Z.good.base i j b
  have hbo := GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hL : X.R.toLevCh.Is X.A3.A.μ0 := X.char.lev
  have hQe : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hce : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := by
    have g0 := Twist.triv_good (D := D) (A := Circle) splitSet_empty
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hce]; exact g0.isOpen
    · rw [hce]; exact g0.rat
    · rw [hce]; exact g0.real
    · rw [hQe]; exact g0.split
    · rw [hce, hQe]; exact g0.unram
    · rw [hQe]; intro PP hPP; exact absurd hPP (Finset.notMem_empty _)
  have hAdm : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by
    rw [hQe]
    exact ⟨by rw [Finset.union_empty]; exact hB.places, Finset.disjoint_empty_right _⟩
  have ht : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hce, mul_one]; exact h1, by rw [hQe, Finset.union_empty]; exact h2⟩
  obtain ⟨hPg, hQ, hcg, hxq⟩ := GlobalTheory.ConjTwist.Test.levS_chars hbo hL hB hψ hAdm ht
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have htW : (Vc D j).rank - (Wc D j).rank = D.R.t := by omega
  have eβ : (Y.Z.ρ.B i j b).F.βS = X.R.βV j := hbo.βS
  have ebo : blkOf ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).t =
      blkOf (n := (Vc D j).rank) (X.R.datVt j t).r (X.R.datVt j t).t := by
    show blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) = blkOf D.R.r D.R.t
    rw [htW, rW]
  have eb2 : blk2 (n := (Vc D j).rank) ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r = blk2 (X.R.datVt j t).r := by
    show blk2 (Wc D j).rank = blk2 D.R.r
    rw [rW]
  have hpar : ∀ y, y ∈ parLev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
      y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) := by
    intro y
    rw [mem_parLev, mem_parLev, eβ, ebo, eb2, hPg, hQ]

  have hrt : ∀ y (hy : y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t)),
      rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) y =
        Y.Z.ρ.eG i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) y)) := by
    intro y hy
    have hy' := (hpar y).2 hy
    funext PP
    obtain ⟨P, hP⟩ := PP
    have h' : P ∈ X.R.Pg := by rw [← hbo.Pg]; exact hP
    apply Units.ext
    ext a c
    have hg := Y.Z.pin.grp i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) y)) P hP h' a c
    refine Eq.trans ?_ hg.symm
    have m1 := blockTri_blkOf_le _ _ (parLev_g hy' hP)
    have m2 := blockTri_blkOf_le _ _ (parLev_g hy h')
    have hz := X.cG.symm_apply_apply (rTup (X.R.βV j) (X.R.datVt j t) y)
    rw [hz]
    simp only [rTup]
    rw [upper_block_val_submatrix _ m1, upper_block_val_submatrix _ m2]
    simp only [Matrix.submatrix_apply]
    rw [eβ]
    rfl

  refine ⟨?_, ?_⟩
  · rw [mem_lev, hpar x]
    constructor
    · rintro ⟨hx, hr⟩
      refine ⟨hx, ?_⟩
      rw [hrt x hx] at hr
      exact ((Y.Z.tie i j b).U_eq _).1 hr
    · rintro ⟨hx, hu⟩
      refine ⟨hx, ?_⟩
      rw [hrt x hx]
      exact ((Y.Z.tie i j b).U_eq _).2 hu
  · intro hx hu
    have hmem : Y.Z.ρ.eG i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) x)) ∈ (Y.Z.ρ.B i j b).G.P.H :=
      ((Y.Z.tie i j b).U_eq _).2 hu
    have hmem' : rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x ∈
        ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.H := by
      rw [hrt x hx]; exact hmem
    have f1 : ext1 ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.H ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.chi
        (rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x) =
        (Y.Z.ρ.B i j b).G.P.chi ⟨_, hmem⟩ := by
      rw [extendOne_of_mem _ hmem']
      congr 1
      exact Subtype.ext (hrt x hx)
    have f1' : ext1 (Lev.flagL (X.R.datVt j t)).P.H (Lev.flagL (X.R.datVt j t)).P.chi
        (rTup (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x) = 1 := by
      rw [extendOne_of_mem _ (show _ ∈ (Lev.flagL (X.R.datVt j t)).P.H from Subgroup.mem_top _)]
      rfl
    have f2 : (∏ PP ∈ ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).Pg,
        ∏ c ∈ Finset.range ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).s,
          ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).cg (c + 1) PP
            (dBlk (blkOf ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).t) (c + 1)
              (redFn (Y.Z.ρ.B i j b).F.βS PP x))) =
        ∏ PP ∈ (Lev.flagL (X.R.datVt j t)).Pg, ∏ c ∈ Finset.range (Lev.flagL (X.R.datVt j t)).s,
          (Lev.flagL (X.R.datVt j t)).cg (c + 1) PP
            (dBlk (blkOf (Lev.flagL (X.R.datVt j t)).r (Lev.flagL (X.R.datVt j t)).t) (c + 1) (redFn (X.R.βV j) PP x)) := by
      refine Finset.prod_congr hPg fun PP hP => Finset.prod_congr rfl fun c _ => ?_
      have h' : PP ∈ X.R.Pg := hP
      rw [hcg _ PP h', ebo, eβ]
      rfl
    have f3 : (∏ PP ∈ ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).Q,
          ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).xq PP
            (dBlk (blk2 ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r) 1 (redFn (Y.Z.ρ.B i j b).F.βS PP x))) =
        ∏ PP ∈ (Lev.flagL (X.R.datVt j t)).Q,
          (Lev.flagL (X.R.datVt j t)).xq PP (dBlk (blk2 (Lev.flagL (X.R.datVt j t)).r) 1 (redFn (X.R.βV j) PP x)) := by
      refine Finset.prod_congr hQ fun PP hP => ?_
      have h' : PP ∈ X.R.Q t := hP
      rw [hxq PP h', eb2, eβ]
      rfl
    unfold levFn
    rw [f1, f1', f2, f3, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_one,
      (Y.Z.tie i j b).psiU_eq ⟨_, hu⟩ hmem]
    ring
