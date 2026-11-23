import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport

section Matrices
variable {k k' : Type} [Field k] [Field k'] {R C R' C' : Type}

def trM (j : k ≃+* k') (eR : R' ≃ R) (eC : C' ≃ C) (Z : Matrix R C k) : Matrix R' C' k' :=
  Matrix.of fun r c => j (Z (eR r) (eC c))

@[simp] theorem trM_apply (j : k ≃+* k') (eR : R' ≃ R) (eC : C' ≃ C) (Z : Matrix R C k) (r : R') (c : C') :
    trM j eR eC Z r c = j (Z (eR r) (eC c)) := rfl

@[simp] theorem trM_symm_trM (j : k ≃+* k') (eR : R' ≃ R) (eC : C' ≃ C) (Z : Matrix R C k) :
    trM j.symm eR.symm eC.symm (trM j eR eC Z) = Z := by
  ext r c; simp

@[simp] theorem trM_trM_symm (j : k ≃+* k') (eR : R' ≃ R) (eC : C' ≃ C) (Y : Matrix R' C' k') :
    trM j eR eC (trM j.symm eR.symm eC.symm Y) = Y := by
  ext r c; simp

theorem trM_injective (j : k ≃+* k') (eR : R' ≃ R) (eC : C' ≃ C) : Function.Injective (trM j eR eC) :=
  fun Z Z' h => by rw [← trM_symm_trM j eR eC Z, h, trM_symm_trM]

theorem trM_mul {M M' : Type} [Fintype M] [Fintype M'] (j : k ≃+* k') (eR : R' ≃ R) (eM : M' ≃ M) (eC : C' ≃ C)
    (X : Matrix R M k) (Y : Matrix M C k) : trM j eR eC (X * Y) = trM j eR eM X * trM j eM eC Y := by
  ext r c
  simp only [trM_apply, Matrix.mul_apply, map_sum, map_mul]
  exact (Fintype.sum_equiv eM _ _ fun m => rfl).symm

end Matrices

section Groups
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def glTrEquiv {k k' : Type} [Field k] [Field k'] (j : k ≃+* k') (e : n' ≃ n) : GL n k ≃* GL n' k' :=
  Units.mapEquiv ((j.mapMatrix (m := n)).toMulEquiv.trans (Matrix.reindexAlgEquiv k' k' e.symm).toMulEquiv)

@[simp] theorem glTrEquiv_val {k k' : Type} [Field k] [Field k'] (j : k ≃+* k') (e : n' ≃ n) (g : GL n k) :
    (glTrEquiv j e g).val = trM j e e g.val := by
  ext r c; rfl

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}

def glTr (hj : IsLocIso j) (e : n' ≃ n) : GL n k ≃ₜ* GL n' k' :=
  { glTrEquiv j e with
    continuous_toFun := GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous_iff.2 (by
      have : (fun g : GL n k => ((glTrEquiv j e g : GL n' k') : Matrix n' n' k')) =
          fun g : GL n k => ((g.val.map j).submatrix e e) := funext fun g => by ext; rfl
      show Continuous (fun g : GL n k => ((glTrEquiv j e g : GL n' k') : Matrix n' n' k'))
      rw [this]
      exact (Units.continuous_val.matrix_map hj.1).matrix_submatrix e e)
    continuous_invFun := GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous_iff.2 (by
      have : (fun g : GL n' k' => (((glTrEquiv j e).symm g : GL n k) : Matrix n n k)) =
          fun g : GL n' k' => ((g.val.map j.symm).submatrix e.symm e.symm) := funext fun g => by
        apply (trM_injective j e e)
        rw [← glTrEquiv_val, MulEquiv.apply_symm_apply]
        ext r c; simp
      show Continuous (fun g : GL n' k' => (((glTrEquiv j e).symm g : GL n k) : Matrix n n k))
      rw [this]
      exact (Units.continuous_val.matrix_map hj.2.1).matrix_submatrix e.symm e.symm) }

@[simp] theorem glTr_val (hj : IsLocIso j) (e : n' ≃ n) (g : GL n k) : (glTr hj e g).val = trM j e e g.val :=
  glTrEquiv_val j e g

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

def pullMeas (hj : IsLocIso j) (e : n' ≃ n) (μ : MeasureTheory.Measure (GL n' k')) : MeasureTheory.Measure (GL n k) :=
  μ.map (glTr hj e).symm

instance isHaar_pullMeas (hj : IsLocIso j) (e : n' ≃ n) (μ : MeasureTheory.Measure (GL n' k')) [μ.IsHaarMeasure] :
    (pullMeas hj e μ).IsHaarMeasure :=
  (glTr hj e).symm.isHaarMeasure_map μ

theorem map_pullMeas (hj : IsLocIso j) (e : n' ≃ n) (μ : MeasureTheory.Measure (GL n' k')) :
    (pullMeas hj e μ).map (glTr hj e) = μ := by
  have h1 : Measurable (glTr hj e) := (glTr hj e).continuous.measurable
  have h2 : Measurable (glTr hj e).symm := (glTr hj e).symm.continuous.measurable
  rw [pullMeas, MeasureTheory.Measure.map_map h1 h2]
  simp

end Groups

section Place
variable {D : D7} {v : Pl D.host.F}

theorem isEquiv_Fv_valued :
    (ValuativeRel.valuation (Fv D.host.F v)).IsEquiv (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem valued_complEquiv_symm (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hv : (splitPrime τ).under (𝓞 D.host.F) = v) (y : Kw (D := D) (splitPrime τ)) :
    Valued.v ((GlobalTheory.LFun.SplitTie.complEquiv τ hv).symm y) = Valued.v y := by
  conv_rhs => rw [← (GlobalTheory.LFun.SplitTie.complEquiv τ hv).apply_symm_apply y]
  rw [GlobalTheory.LFun.SplitTie.complEquiv_apply, GlobalTheory.LFun.SplitTie.valued_complMap]

theorem continuous_complEquiv_symm (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hv : (splitPrime τ).under (𝓞 D.host.F) = v) : Continuous (GlobalTheory.LFun.SplitTie.complEquiv τ hv).symm := by
  refine continuous_of_continuousAt_zero (GlobalTheory.LFun.SplitTie.complEquiv τ hv).symm ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨m, hm⟩ : ∃ m : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp m :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := D.host.E) (splitPrime τ) (-((m.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hm, valued_complEquiv_symm]
  exact ha.trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem isLocIso_complEquiv (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hv : (splitPrime τ).under (𝓞 D.host.F) = v) : IsLocIso (GlobalTheory.LFun.SplitTie.complEquiv τ hv) := by
  refine ⟨GlobalTheory.LFun.SplitChart.continuous_complMap _, continuous_complEquiv_symm τ hv, fun x => ?_⟩
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, (Good.isEquiv_Kw (D := D) _).le_one_iff_le_one,
    isEquiv_Fv_valued.le_one_iff_le_one, GlobalTheory.LFun.SplitTie.complEquiv_apply, GlobalTheory.LFun.SplitTie.valued_complMap]

end Place

section Lattices
variable {k k' : Type} [Field k] [ValuativeRel k] [Field k'] [ValuativeRel k'] {D D₂ : Type}

def LatCorr (j : k ≃+* k') (cD : D₂ ≃ D) (Λ : Submodule 𝒪[k] (D → k)) (Λ₂ : Submodule 𝒪[k'] (D₂ → k')) : Prop :=
  ∀ x : D → k, (fun c => j (x (cD c))) ∈ Λ₂ ↔ x ∈ Λ

end Lattices

end GlobalTheory.PureMatch.Transport
