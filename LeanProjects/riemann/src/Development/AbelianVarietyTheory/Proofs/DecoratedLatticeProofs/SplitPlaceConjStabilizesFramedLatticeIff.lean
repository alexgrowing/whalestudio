import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjFrameMatrixReindexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SplitStabConj

theorem eq_idempotent_mul_add_of_mul_sub_eq {R : Type*} [CommRing R] (ε m o : R) (h : ε * (m - o) = m - o) : m = ε * m + (1 - ε) * o := by
  linear_combination -h

theorem suppAt_conj {D : D7} {e : AE D} {V : HSp D} {g : GA D V} (h : Formalism.L2.Theta.SuppAt e V g) (b : GA D V) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hmul : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    simp [Formalism.L2.Theta.mt, map_mul]
  have hAB : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hmul, inv_mul_cancel]; simp [Formalism.L2.Theta.mt]
  have hm : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hmul, hmul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  have hg : Formalism.L2.Theta.mt V g - 1 = (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) := by
    ext i j; exact (h i j).symm
  intro i j
  rw [hm]
  conv_rhs => rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  rfl

end GlobalTheory.SplitStabConj

set_option maxHeartbeats 1000000 in
open GlobalTheory.SplitStabConj in

theorem GlobalTheory.splitStab_conj_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → b⁻¹ * g * b ∈ GfC V ∧ (Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β ↔ gk ∈ KO k Y) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V (b⁻¹ * g * b)) = 1 := by
  intro D k _ _ _ _ q PP he V β Λ N hSD Y _ _ F σ b hM g gk hL
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N hSD
  obtain ⟨c, hfr, -⟩ := hSD
  have hsg : Formalism.L2.Theta.SuppAt q.e V g := hL.1
  have hsκ : Formalism.L2.Theta.SuppAt q.e V (b⁻¹ * g * b) := suppAt_conj hsg b
  refine ⟨?_, ?_, ?_⟩
  · have hg := GlobalTheory.SplitHecke.Stab.mem_GfC q.split hsg
    rw [GfC, MonoidHom.mem_ker] at hg ⊢
    rw [map_mul, map_mul, hg, mul_one, ← map_mul, inv_mul_cancel, map_one]
  · obtain ⟨hX, hXi⟩ := GlobalTheory.T.splitPlace_conj_frameMatrix_reindex q he V β F σ b hM g gk hL
    obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
    rw [GlobalTheory.LocGl.mem_KO_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hyX : Formalism.L2.DIV.intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β := by
        rw [← hy]; simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, mul_assoc]
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · obtain ⟨i, rfl⟩ := σ.surjective a
        obtain ⟨j, rfl⟩ := σ.surjective a'
        rw [← hX i j, q.prF_mem_iff he, ← hyX]
        exact mul_mem hint (y.val i j).2
      · obtain ⟨i, rfl⟩ := σ.surjective a
        obtain ⟨j, rfl⟩ := σ.surjective a'
        rw [← hXi i j, q.prF_mem_iff he, ← hyX, ← map_inv]
        exact mul_mem hint ((y⁻¹).val i j).2
    · rintro ⟨h1, h2⟩
      have hA : IsIntM (toEAf D q.e • (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).1) := fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, ← q.prF_mem_iff he, hX]; exact h1 _ _
      have hB : IsIntM (toEAf D q.e • ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, ← q.prF_mem_iff he, hXi]; exact h2 _ _
      obtain ⟨hC, hD⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral V Λ β hsd hfr _ (GlobalTheory.LevSplit.finE_mem_UA V (b⁻¹ * g * b)) _ rfl q.e hA hB
      have hsum : IsIdemSum q.e {PP} := ⟨⟨fun _ => q.e, by simpa using he, by simp⟩, q.split.2.1⟩
      have hmt : Formalism.L2.Theta.mt V (b⁻¹ * g * b) = (q.e + cA D q.e) • Formalism.L2.Theta.mt V (b⁻¹ * g * b) +
          (1 - (q.e + cA D q.e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
        ext i j
        have := hsκ i j
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
        exact eq_idempotent_mul_add_of_mul_sub_eq _ _ _ this
      have hy := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame V β (b⁻¹ * g * b) (b⁻¹ * g * b) (q.e + cA D q.e) hmt
      exact (GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction V.rank β _ _ {PP} q.e hsum hA hB hC hD hy).1
  · intro PP' hne hS
    exact GlobalTheory.T.reduction_eq_one_off_splitPlace q he V β _ hsκ hS PP' hne
