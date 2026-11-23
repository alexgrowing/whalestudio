import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.RedAt

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
include hq

theorem val_lt_of_pr {y : D.host.E} (hy : valuation K (q.pr (incA D y)) < 1) : PP.valuation D.host.E y < 1 := by
  by_cases hle : PP.valuation D.host.E y ≤ 1
  · obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hle
    have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
      le_antisymm (LevelTest.val_le_one q _) (not_lt.1 fun h' => d.2 ((LevelTest.val_lt_one_iff q hq _).1 h'))
    have hr : r ∈ PP.asIdeal := by
      refine (LevelTest.val_lt_one_iff q hq r).1 ?_
      rw [show ((r : 𝓞 D.host.E) : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd,
        mul_one]
      exact hy
    have hdv : PP.valuation D.host.E ((d : 𝓞 D.host.E) : D.host.E) = 1 :=
      le_antisymm (PP.valuation_le_one _) (not_lt.1 fun h' => d.2 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 h'))
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).2 hr
    rw [← e, map_mul] at h1
    rwa [show algebraMap (𝓞 D.host.E) D.host.E (d : 𝓞 D.host.E) = ((d : 𝓞 D.host.E) : D.host.E) from rfl, hdv, mul_one] at h1
  · exfalso
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hle (by simp)
    have h1 : PP.valuation D.host.E y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (not_le.1 hle)
    have h2 := GlobalTheory.SeeSaw.LevChi.val_rat_lt q hq h1
    have h3 : q.pr (incA D y) * q.pr (incA D y⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
    have h4 := congrArg (valuation K) h3
    rw [map_mul, map_one] at h4
    have h5 : valuation K (q.pr (incA D y)) * valuation K (q.pr (incA D y⁻¹)) < 1 :=
      (mul_le_of_le_one_right' h2.le).trans_lt hy
    exact (ne_of_lt h5) h4

theorem hasRes_of_pr {z : AE D} (c : 𝓞 D.host.E) (hz : valuation K (q.pr z - q.pr (incA D (c : D.host.E))) < 1) :
    GlobalTheory.Mem.Col2.HasRes PP (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z)) (Ideal.Quotient.mk PP.asIdeal c) := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : Valued.v (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) < 1 := by
    rw [← GlobalTheory.Mem.Col2.adAt_inclE D.host.F, ← map_sub, e, add_sub_cancel_left]
    exact valued_nat_mul_lt hr hN'
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    refine GlobalTheory.SeeSaw.LevChi.val_pr_lt q hq ?_
    have e2 : toEAf D (z - incA D y) = toEAf D z - Formalism.UG.inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F) y := by
      rw [RingHom.map_sub]
      rfl
    rw [e2, map_sub, GlobalTheory.Mem.Col2.adAt_inclE]
    exact h1
  have h3 : valuation K (q.pr (incA D (y - (c : D.host.E)))) < 1 := by
    have e3 : q.pr (incA D (y - (c : D.host.E))) = (q.pr z - q.pr (incA D (c : D.host.E))) - q.pr (z - incA D y) := by
      rw [map_sub, map_sub, map_sub]
      ring
    rw [e3]
    exact Valuation.map_sub_lt _ hz h2
  have h4 := val_lt_of_pr q hq h3
  refine ⟨c, rfl, ?_⟩
  have e4 : GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E c) =
      (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) +
        algebraMap D.host.E (PP.adicCompletion D.host.E) (y - (c : D.host.E)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [e4]
  refine Valuation.map_add_lt _ h1 ?_
  rw [valued_algebraMap]
  exact h4

end Split

end GlobalTheory.FamTrace.RedAt

namespace GlobalTheory.FamTrace.RedAt

set_option maxHeartbeats 1000000 in

theorem inJ_red : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ (i : Fin a.n) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (i0 : Fin 2) (h : ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), (a.G i).q.v = v → (∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1)) → Formalism.L2.Forms.InJ (I.rec7 l Z).R.k (I.rec7 l Z).R.t ((I.rec7 l Z).R.N 0) false (Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((F0 W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy i v i0 h hv hM
  have hstd := hA.tr.std.some u
  obtain ⟨w, hw, ρ, hu, hres⟩ := GlobalTheory.Mem.Col2.TC.GLev0.exists_w (F0 W u).gl hstd.gl.piG i0 v h
  have hid := (ha.tie row col).2.idem i
  have hPg : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  have hwe : w = (a.pl i).1 := GlobalTheory.Mem.Col2.TC.GLev0.vGs_inj (X := X) hPg
    (GlobalTheory.Mem.Col2.TC.GLev0.mem_vGs.2 ⟨i0, hw⟩) (hu.trans (hv.symm.trans hid.2))
  subst hwe
  have hn : (I.rec7 l Z).R.N 0 = (I.rec7 l Z).R.k := by simp [Ranks.N]
  have hr := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  have key : ∀ r c : Fin ((I.rec7 l Z).R.N 0), c ≤ r →
      Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((F0 W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1)) r c =
        if r = c then 1 else 0 := by
    intro r c hcr
    obtain ⟨r', rfl⟩ : ∃ r', r = finCongr hr r' := ⟨(finCongr hr).symm r, by simp⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = finCongr hr c' := ⟨(finCongr hr).symm c, by simp⟩
    have hcr' : c' ≤ r' := hcr
    have hsm := (hM r' c').2 hcr'
    have hinj : (finCongr hr r' = finCongr hr c') ↔ r' = c' := (finCongr hr).injective.eq_iff
    have e1 : (a.G i).q.pr (incA (I.rec7 l Z) (((if r' = c' then 1 else 0 : 𝓞 (I.rec7 l Z).host.E)) : (I.rec7 l Z).host.E)) =
        (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r' c' := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have hR := hasRes_of_pr (a.G i).q hid.1 (z := mt ((I.rec7 l Z).sp.X 0) κ r' c') (if r' = c' then 1 else 0) (by
      rw [e1]
      exact hsm)
    have hyrc : y.1.1 (finCongr hr r') (finCongr hr c') = toEAf (I.rec7 l Z) (mt ((I.rec7 l Z).sp.X 0) κ r' c') := by
      rw [← hy]
      rfl
    rw [← hyrc] at hR
    obtain ⟨hh, e⟩ := hres _ _ hR
    rw [GlobalTheory.Mem.Col2.TC.GLev0.mat_one]
    unfold Formalism.L2.Forms.redM
    refine (dif_pos hh).trans (e.trans ?_)
    by_cases hrc : r' = c'
    · subst hrc
      rw [if_pos rfl, if_pos rfl, map_one]
      exact map_one ρ
    · rw [if_neg hrc, if_neg (fun e => hrc (hinj.1 e)), map_zero]
      exact map_zero ρ
  have hlt : ∀ x : Fin ((I.rec7 l Z).R.N 0), (x : ℕ) < (I.rec7 l Z).R.k := fun x => hn ▸ x.2
  have hb : ∀ x : Fin ((I.rec7 l Z).R.N 0), Formalism.L2.Forms.blkOf (I.rec7 l Z).R.k (I.rec7 l Z).R.t x = x :=
    fun x => if_pos (hlt x)
  refine ⟨fun x z hxz => ?_, fun x _ => ?_, fun x z hz => absurd hz (ne_of_lt z.2), fun h' => absurd h' (by simp)⟩
  · rw [hb, hb] at hxz
    rw [key x z (le_of_lt (show z < x from hxz)), if_neg (fun e => by subst e; exact lt_irrefl _ hxz)]
  · rw [key x x le_rfl, if_pos rfl]

end GlobalTheory.FamTrace.RedAt
