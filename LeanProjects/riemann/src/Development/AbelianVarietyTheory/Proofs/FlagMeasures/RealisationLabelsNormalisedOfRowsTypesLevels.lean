import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeriesStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open scoped TensorProduct

namespace GlobalTheory.LabPinAt

theorem mult_lev_left {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    (∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g) ∧ ∀ v, ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨hx.lev, fun v γ hγ g => (hx.aut v).left γ hγ g⟩
  | zero => exact ⟨fun v k _ g => by simp, fun v γ _ g => by simp⟩
  | add x y _ _ hx hy =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 v k hk g, hy.1 v k hk g]; ring
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2 v γ hγ g, hy.2 v γ hγ g]
  | smul c x _ hx =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 v k hk g]; ring
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2 v γ hγ g]

end GlobalTheory.LabPinAt

theorem GlobalTheory.LabPinAt.labTie_at : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (F : Face D A), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ y, ι (D.sEE y) = conjHH X G (j y)) → RowJ R eE X h G t j → LevelMatchA R F X h t → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → TypeLab D rep → GoodFTAll D → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep F hPsi hE hι hRJ hLev hIso hTL hGood
  have hM : ∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ Mult R.θ (R.MY 0) (JR R F) (chiR R F) := fun σ => (hIso σ).1.1
  refine GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries D X h t PY hF G' Pl0 T A Ks R eE G j ι rep (Minf R.θ PY (R.MY 0)) hPsi hE hι hRJ
    (fun σ => (hIso σ).2) ?_ ?_ hTL (fun σ => hGood (D.what₂.ft σ))
  · intro σ k hk v y
    obtain ⟨hk2, hc⟩ := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
    obtain ⟨hJ, hχ⟩ := hLev k hk2
    rw [(GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).1 v _ hJ y, show chiR R F (kap X h t k) = star (X.chi2 k) from hχ, hc,
      star_one, one_mul]
  · intro σ v γ hγ y
    exact (GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).2 v γ hγ y
