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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemColGroupIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.AwayLevel.single_natCast_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (T : ℕ) (j b : Fin n) [Decidable (b = j)] :
    (Pi.single j (T : K) : Fin n → K) b = ((if b = j then (T : 𝓞 K) else 0 : 𝓞 K) : K) := by
  by_cases hb : b = j
  · subst hb
    simp
  · simp [hb]

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FinPl.AwayLevel.mem_levelVL_base : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => True) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v (F0 W u).cls0.lev.Lb := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a hat κ hκ y hy hmv v hv
  have hL := (hat.pinX.xs 0 (Nat.zero_le _)).2.2
  have hint := (GlobalTheory.SeeSaw.LevMem.moves_iff hL _ hy).1 hmv
  obtain ⟨k, hR⟩ := (hA.tr.std.some u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb : ∀ x, x ∈ (F0 W u).cls0.lev.Lb ↔ x ∈ TC.baseL B (B.R.N 0) (X.piT u) := hR.lb ()
  have hv' : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := hv
  have h1 : ∀ x ∈ (F0 W u).cls0.lev.Lb, ∀ j, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = r := fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have h2 : ∀ j, (Pi.single j ((B.T u : ℕ) : (I.rec7 l Z).host.E) : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E) ∈ (F0 W u).cls0.lev.Lb := fun j =>
    (hLb _).2 fun b => by
      have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
      refine ⟨if b = j then (B.T u : 𝓞 B.host.E) else 0, ?_, fun _ => ?_⟩
      · exact GlobalTheory.FinPl.AwayLevel.single_natCast_eq (K := B.host.E) (B.T u) j b
      · split_ifs
        · refine ⟨B.fields.conjO ((B.primes X).piT u), ?_⟩
          rw [hPr.piT_norm u]
        · exact dvd_zero _
  have hS := fun x => GlobalTheory.Mem.Col2.LevRead.mem_latS_iff hv' h1 h2 x
  have hmul : ∀ (N : GL (Fin ((I.rec7 l Z).R.N 0)) (Formalism.L2.DIV.AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), (∀ i j, N.1 i j ∈ Formalism.L2.DIV.RInt (I.rec7 l Z).host.F (I.rec7 l Z).host.E) →
      ∀ x : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F, (∀ b, x b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) →
        ∀ b, ((Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) N).1 *ᵥ x) b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v := fun N hN x hx b => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (Formalism.UG.P.afsplit_prV_int v _ (hN b j)) (hx j)
  refine Subgroup.mem_inf.2 ⟨GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2, fun x => ?_⟩
  rw [hS, hS]
  refine ⟨hmul _ hint.1 x, fun h b => ?_⟩
  have := hmul _ hint.2 _ h b
  rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
