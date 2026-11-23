import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.levS_iff_levG_and_levChi_eq :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ k : GA D (Vc D j), (k ∈ levS (Vc D j) (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) ↔ k ∈ Lev.levG (Vc D j) (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι))) ∧
      (k ∈ Lev.levG (Vc D j) (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) → Lev.levChi (Vc D j) (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) k = Lev.levChi (Vc D j) (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) k) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι k
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hbo := GlobalTheory.PinBase.baseOf_of_pin D X Z.ρ Z.good Z.pin (c.twI w) j (c.sd w)
  have hL : X.R.toLevCh.Is X.A3.A.μ0 := X.char.lev
  obtain ⟨hψ, hAdm, -⟩ := GlobalTheory.PlaceRead.twVia_good D c w Z.ρ Z.good H.ok j ι
  have ht := H.tup ι hι
  obtain ⟨hPg, hQ, hcg, hxq⟩ := GlobalTheory.ConjTwist.Test.levS_chars hbo hL hB hψ hAdm ht
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have htW : (Vc D j).rank - (Wc D j).rank = D.R.t := by omega
  have eβ : (Z.ρ.B (c.twI w) j (c.sd w)).F.βS = X.R.βV j := hbo.βS
  have ebo : blkOf ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).t =
      blkOf (n := (Vc D j).rank) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).t := by
    show blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) = blkOf D.R.r D.R.t
    rw [htW, rW]
  have eb2 : blk2 (n := (Vc D j).rank) ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r = blk2 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r := by
    show blk2 (Wc D j).rank = blk2 D.R.r
    rw [rW]
  have hPg' : ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Pg = (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Pg := hPg
  have hQ' : ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Q = (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Q := hQ
  have hpar : ∀ y, y ∈ parLev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) ↔
      y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) := by
    intro y
    rw [mem_parLev, mem_parLev, eβ, ebo, eb2, hPg', hQ']
  have hrt : ∀ y (hy : y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false))),
      rTup (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) y =
        Z.ρ.eG (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)) := by
    intro y hy
    have hy' := (hpar y).2 hy
    funext PP
    obtain ⟨P, hP⟩ := PP
    have h' : P ∈ X.R.Pg := by rw [← hbo.Pg]; exact hP
    apply Units.ext
    ext a b
    have hg := Z.pin.grp (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)) P hP h' a b
    refine Eq.trans ?_ hg.symm
    have m1 := blockTri_blkOf_le _ _ (parLev_g hy' hP)
    have m2 := blockTri_blkOf_le _ _ (parLev_g hy h')
    have hz := X.cG.symm_apply_apply (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)
    rw [hz]
    simp only [rTup]
    rw [upper_block_val_submatrix _ m1, upper_block_val_submatrix _ m2]
    simp only [Matrix.submatrix_apply]
    rw [eβ]
    rfl
  have hH : ∀ g : G0 X.R.Pg D.R.r, g ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H ↔ X.cG g ∈ D.nexp.U := by
    intro g
    have h1 := H.U_eq (X.R.eG.symm g)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    exact Iff.rfl
  have hlev : ∀ x, x ∈ lev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) ↔
      x ∈ lev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) := by
    intro x
    rw [mem_lev, mem_lev, hpar x]
    refine and_congr_right fun hx => ?_
    rw [hrt x hx]
    exact (hH _).trans ((Z.tie (c.twI w) j (c.sd w)).U_eq _).symm
  refine ⟨and_congr_right fun _ => hlev _, fun hk => ?_⟩
  have hk' : Lev.finE (Vc D j) k ∈ lev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) := hk.2
  unfold Lev.levChi
  generalize Lev.finE (Vc D j) k = x at hk'
  obtain ⟨hx, hm⟩ := mem_lev.1 ((hlev x).2 hk')
  have hmem' := (mem_lev.1 hk').2
  have hu : X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x) ∈ D.nexp.U := (hH _).1 hm
  have hmem : Z.ρ.eG (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x)) ∈ (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H :=
    ((Z.tie (c.twI w) j (c.sd w)).U_eq _).2 hu
  have f1 : ext1 ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).P.H ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).P.chi (rTup (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) x) =
      (Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi ⟨_, hmem⟩ := by
    rw [extendOne_of_mem _ hmem']
    congr 1
    exact Subtype.ext (hrt x hx)
  have hchi : ∀ (g : G0 X.R.Pg D.R.r) (hg : g ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H) (hu : X.cG g ∈ D.nexp.U),
      (((Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.chi ⟨g, hg⟩ : ℂˣ) : ℂ) =
        Z.ρ.e (c.twI w) (c.sd w) (D.nexp.psiU (c.twI w) (c.sd w) ⟨_, hu⟩ : (FractionRing (D.ntw.O (c.twI w)))ˣ) := by
    intro g hg hu
    obtain ⟨g₀, rfl⟩ := X.R.eG.surjective g
    have h0 : g₀ ∈ X.F.P0 := (H.U_eq g₀).1 hu
    rw [H.psi_eq (c.twI w) (c.sd w) ⟨g₀, h0⟩ hu]
    have h1 : X.R.eG.symm (X.R.eG g₀) ∈ X.F.P0 := by rw [MulEquiv.symm_apply_apply]; exact h0
    have e : (⟨g₀, h0⟩ : X.F.P0) = ⟨_, h1⟩ := Subtype.ext (X.R.eG.symm_apply_apply g₀).symm
    rw [e]
    exact Units.val_inv_eq_inv_val _
  have f1' : ext1 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.chi (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x) = (Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi ⟨_, hmem⟩ := by
    rw [extendOne_of_mem _ hm]
    exact Units.ext ((hchi _ hm hu).trans ((Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hu⟩ hmem).symm)
  have f2 : (∏ PP ∈ ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Pg, ∏ b ∈ Finset.range ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).s,
        ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).cg (b + 1) PP (dBlk (blkOf ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).t) (b + 1) (redFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS PP x))) =
      ∏ PP ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Pg, ∏ b ∈ Finset.range (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).s,
        (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).cg (b + 1) PP (dBlk (blkOf (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).t) (b + 1) (redFn (X.R.βV j) PP x)) := by
    refine Finset.prod_congr hPg' fun PP hP => Finset.prod_congr rfl fun b _ => ?_
    have h' : PP ∈ X.R.Pg := hP
    rw [hcg _ PP h', ebo, eβ]
    rfl
  have f3 : (∏ PP ∈ ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Q, ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).xq PP (dBlk (blk2 ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r) 1 (redFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS PP x))) =
      ∏ PP ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Q, (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).xq PP (dBlk (blk2 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r) 1 (redFn (X.R.βV j) PP x)) := by
    refine Finset.prod_congr hQ' fun PP hP => ?_
    have h' : PP ∈ X.R.Q (Y.tupT (D.what₂.muTw w)) := hP
    rw [hxq PP h', eb2, eβ]
    rfl
  show ((levFn (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x : ℂˣ) : ℂ) = ((levFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) x : ℂˣ) : ℂ)
  unfold levFn
  rw [f1, f1', f2, f3]
