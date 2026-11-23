import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitProjChart

variable {D : D7} {v : FinPl D}

def emb (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem emb_apply (φ : SplitProj D v) (x : D.host.E) : emb φ x = rdQ φ x := rfl

theorem splitProj_emb (φ : SplitProj D v) : GlobalTheory.AdelicU.splitProj (emb φ) = φ := by
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [GlobalTheory.AdelicU.splitProj_tmul, emb_apply, rdQ, ← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]

theorem chart_idem (φ : SplitProj D v) : GlobalTheory.SplitHecke.Chart (GlobalTheory.EmbChart.idem (emb φ)) v (rdA φ) := by
  have h := GlobalTheory.EmbChart.chart_idem (emb φ)
  rw [splitProj_emb] at h
  exact h

theorem rdA_idem (φ : SplitProj D v) : rdA φ (GlobalTheory.EmbChart.idem (emb φ)) = 1 := by
  change φ (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (GlobalTheory.EmbChart.idem (emb φ))) = 1
  rw [GlobalTheory.EmbChart.compFin_idem]
  nth_rewrite 1 [← splitProj_emb φ]
  exact GlobalTheory.AdelicU.splitProj_splitIdem _ _

theorem eq_idem {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : e = GlobalTheory.EmbChart.idem (emb φ) := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he.1 (GlobalTheory.EmbChart.isSplitIdem_idem _)).resolve_right fun h => ?_
  have := congrArg (rdA φ) h
  rw [map_mul, he.2.2, rdA_idem, map_zero, mul_one] at this
  exact one_ne_zero this

theorem rdE_toEAf (φ : SplitProj D v) (a : AE D) : rdE φ (toEAf D a) = rdA φ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem rdA_incA (φ : SplitProj D v) (x : D.host.E) : rdA φ (incA D x) = rdQ φ x := by
  change φ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one]; rfl

theorem continuous_rdA (φ : SplitProj D v) : Continuous (rdA φ) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (rdA φ) ?_
  have h1 : Continuous (GlobalTheory.AdelicU.evFin D.host.F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact h1.congr fun y => ((chart_idem φ).2.2.1 y).symm

theorem chart_rdA : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → GlobalTheory.SplitHecke.Chart e v (rdA φ) ∧ (∀ a : AE D, rdE φ (toEAf D a) = rdA φ a) ∧ (∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x) ∧ Continuous (rdA φ) ∧ ∀ e', IsIdemOf φ e' → e' = e :=
  fun _ _ φ _ he => ⟨eq_idem he ▸ chart_idem φ, rdE_toEAf φ, rdA_incA φ, continuous_rdA φ,
    fun _ he' => (eq_idem he').trans (eq_idem he).symm⟩

end GlobalTheory.SplitProjChart

end
