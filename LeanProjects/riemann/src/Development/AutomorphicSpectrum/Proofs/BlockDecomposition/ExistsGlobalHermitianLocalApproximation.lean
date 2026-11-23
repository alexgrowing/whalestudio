import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

open GlobalTheory.EmbChart (tensAt compFin_tensAt)

theorem compFin_tensAt_ne_place {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (y : Fv F v ⊗[F] E) :
    compFin F E u (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul a x =>
    change (evalV F u (singleFin v a)) ⊗ₜ[F] x = 0
    rw [evalV_singleFin_ne h, TensorProduct.zero_tmul]

theorem compInf_tensAt_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    compInf F E w (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul a x =>
    change (evInf F w (GlobalTheory.EmbChart.atPlace v a)) ⊗ₜ[F] x = 0
    rw [show evInf F w (GlobalTheory.EmbChart.atPlace v a) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul]

theorem cA_tensAt (D : D7) (v : Pl D) (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    cA D (tensAt D.host.E v y) = tensAt D.host.E v (sigR (Fv D.host.F v) D.sp.cm.sig y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => rfl

theorem splitProj_sigR (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    splitProj τ (sigR (Fv D.host.F v) D.sp.cm.sig y) = splitProj (τ.comp D.sp.cm.sig) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => rfl

theorem exists_herm_at (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (X : Matrix (Fin n) (Fin n) (Fv D.host.F v)) :
    ∃ x : hermA D n, (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧
      (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧ tauC τ x.1 = X ∧
      ((∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) →
        ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) := by
  have h := isCMExt_host D
  set M := splitPairMat h τ X Xᵀ with hM
  have p1 : ∀ i j, splitProj τ (M i j) = X i j := fun i j => by
    have := congrArg Prod.fst ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have p2 : ∀ i j, splitProj (τ.comp D.sp.cm.sig) (M i j) = X j i := fun i j => by
    have := congrArg Prod.snd ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have hs : ∀ i j, sigR (Fv D.host.F v) D.sp.cm.sig (M j i) = M i j := fun i j => by
    apply (splitAlgEquiv h τ).injective
    rw [splitAlgEquiv_apply, splitAlgEquiv_apply, splitProj_sigR, splitProj_comp_sigR h, p1, p2, p1, p2]
  have hc : ∀ i j, cv D v (tensAt D.host.E v (M i j)) = M i j := fun i j => compFin_tensAt v _
  refine ⟨⟨Matrix.of fun i j => tensAt D.host.E v (M i j), ?_⟩, ?_, ?_, ?_, ?_⟩
  · change adj _ = _
    ext i j
    change cA D (tensAt D.host.E v (M j i)) = tensAt D.host.E v (M i j)
    rw [cA_tensAt, hs]
  · intro w i j
    exact compInf_tensAt_eq_zero w v _
  · intro v' hv i j
    exact compFin_tensAt_ne_place hv _
  · refine Matrix.ext fun i j => ?_
    change splitProj τ (cv D v (tensAt D.host.E v (M i j))) = X i j
    rw [hc, p1]
  · intro hX i j
    change cv D v (tensAt D.host.E v (M i j)) ∈ _
    rw [hc, mem_intLoc_iff_split h τ, p1, p2]
    exact ⟨hX i j, hX j i⟩

end GlobalTheory.CompanionTheory.Jp

end
