import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
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
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPlMovesLoc

variable {D : D7}

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) {a : AE D} (ha : a ∈ idAt D Q) : a ∈ idAt D P := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  refine Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 hw ⟨w.1, fun hq => w.2 (h _ hq)⟩

theorem latV_mono {S : HSp D} {L : Lat S} {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) {y : Fin S.rank → AE D}
    (hy : y ∈ GlobalTheory.FinPl.latV S L Q) : y ∈ GlobalTheory.FinPl.latV S L P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy ⊢
  refine AddSubgroup.closure_mono ?_ hy
  rintro z ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  exact ⟨α, hαi, fun w hw => hα w (fun hq => hw (h w hq)), a, ha, x, hx, rfl⟩

theorem mulVec_idAt {S : HSp D} (g : GA D S) {Q : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D Q) :
    ∀ i, (mt S g *ᵥ y) i ∈ idAt D Q := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem latV_at_iff {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (· = v)) : y ∈ GlobalTheory.FinPl.latV S L (· = v) ↔ y ∈ GlobalTheory.FinPl.latV S L P := by
  constructor
  · exact latV_mono (fun w hw => hw ▸ hv)
  · intro h
    have h1 := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt (· = v)) h
    have h2 : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy i)
    rwa [h2] at h1

theorem moves_iff : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S), Submodule.IsLattice D.host.E L →
    ∀ (P : GlobalTheory.FinPl.Pl D → Prop), GlobalTheory.FinPl.Moves S g L L P ↔ ∀ v, P v → GlobalTheory.FinPl.Moves S g L L (· = v) := by
  intro D S g L hL P
  constructor
  · intro hM v hv y hy
    have hyP : ∀ i, y i ∈ idAt D P := fun i => idAt_mono (fun w hw => hw ▸ hv) (hy i)
    rw [latV_at_iff hv hy, latV_at_iff hv (mulVec_idAt g hy)]
    exact hM y hyP
  · intro hM y hy
    rw [GlobalTheory.FinPlLoc.part_lat P S L y hL, GlobalTheory.FinPlLoc.part_lat P S L _ hL]
    have hsupp : ∀ v, ∀ e ∈ intAt D (· = v), ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ he.1
    have hcomm : ∀ e : AE D, e • (mt S g *ᵥ y) = mt S g *ᵥ (e • y) := fun e => (Matrix.mulVec_smul _ _ _).symm
    constructor
    · rintro ⟨-, h⟩
      refine ⟨mulVec_idAt g hy, fun v hv e he => ?_⟩
      rw [hcomm]
      exact (hM v hv (e • y) (hsupp v e he)).1 (h v hv e he)
    · rintro ⟨-, h⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      refine (hM v hv (e • y) (hsupp v e he)).2 ?_
      rw [← hcomm]
      exact h v hv e he

end GlobalTheory.FinPlMovesLoc
