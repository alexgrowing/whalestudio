import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDual
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
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
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace

set_option maxHeartbeats 4000000 in

theorem bc_prV_mem_Uloc_off : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FamTrace.InLevG a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Formalism.L2.Forms.badG (I.rec7 l Z) → (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (F0 W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hin v hbad hTv
  obtain ⟨Fstd⟩ := hA.tr.std
  obtain ⟨k, hR⟩ := (Fstd u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb : ∀ x, x ∈ (F0 W u).cls0.lev.Lb ↔ x ∈ TC.baseL B _ (X.piT u) := fun x => hR.lb () x
  rw [(F0 W u).cls0.lev.Uloc_hyp v hbad hTv]
  have hx0 := (hat.pinX.xs 0 (Nat.zero_le _)).2.2
  have hsd := GlobalTheory.AdForm.intVec_isSelfDualC I hA.tr.ok l Z 0 (Nat.zero_le _) (a.g.x 0).L hx0
  have hmv := ((GlobalTheory.FinPl.movesLocal _ _ _ hsd κ).1 hin.1) v
  haveI : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x 0).L := hsd.1
  have hfg : (a.g.x 0).L.FG := Submodule.IsLattice.fg (A := (I.rec7 l Z).host.E)
  have hn := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  let Λ : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E) :=
    (a.g.x 0).L.comap (LinearMap.funLeft (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E (finCongr hn))
  have hb := bc_prV_mem_levelVL_of_moves (I.rec7 l Z) ((I.rec7 l Z).sp.X 0) _ hn (a.g.x 0).L Λ hfg (fun x => Iff.rfl) κ y.1 hy v hmv

  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E :=
    RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) :=
    fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hTdvd : X.piT u ∣ ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.E) := by
    refine ⟨s (X.piT u), ?_⟩
    have hsc' : ∀ x, algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E (s x) =
        (I.rec7 l Z).host.conj (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E x) := hsc
    apply RingOfIntegers.coe_injective
    push_cast
    erw [map_mul, hsc', ← (Fstd u).piU]
    exact (W.R.T.cols.forms u).atT.piU_norm.symm
  have hint : ∀ (j i : Fin ((I.rec7 l Z).R.N 0)), ∃ r : 𝓞 (I.rec7 l Z).host.E,
      (Pi.single j ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) : Fin _ → _) i = (r : (I.rec7 l Z).host.E) ∧
        (i.1 + 1 = (I.rec7 l Z).R.N 0 → X.piT u ∣ r) := by
    intro j i
    by_cases h : i = j
    · subst h
      exact ⟨((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.E), by simp, fun _ => hTdvd⟩
    · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
  have e : Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v
      (F0 W u).cls0.lev.Lb =
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v Λ := by
    refine levelVL_eq_of_std _ _ hTv (fun x hx j => ?_) (fun j => (hLb _).2 fun i => hint j i) (fun x hx j => ?_) (fun j => ?_)
    · obtain ⟨r, e, -⟩ := (hLb x).1 hx j
      exact ⟨r, e⟩
    · have h := (hx0 _).1 hx ((finCongr hn).symm j)
      simp only [LinearMap.funLeft_apply, Function.comp_apply, Equiv.apply_symm_apply] at h
      exact ⟨⟨x j, h⟩, rfl⟩
    · refine (hx0 _).2 fun i => ?_
      obtain ⟨r, hr, -⟩ := hint j (finCongr hn i)
      show IsIntegral ℤ ((Pi.single j _ : Fin _ → _) (finCongr hn i))
      rw [hr]
      exact r.isIntegral_coe
  rw [e]
  exact hb

end GlobalTheory.FamTrace

end
