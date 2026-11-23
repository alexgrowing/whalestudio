import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VacExpand

theorem symp_add_self_expand : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : E, θ + σ θ = 1 →
    ∀ γ γ' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
      GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ') =
        GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                     (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ' +
          2 * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY θ hθ γ γ'
  have hinv : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hcc : ∀ z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hinv]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcI : ∀ x : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    intro x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR]
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E ≃ₐ[AF F] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E :=
    AlgEquiv.ofAlgHom (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
  have htr : ∀ z, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) z := fun z => Algebra.trace_eq_of_algEquiv e z
  set A := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J with hA
  set Bm := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J with hBm
  set c := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ with hc
  have key : ∀ f : Fin n → Fin d → Fin n → Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E,
      ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    intro f
    calc _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  have hconj : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
      c (GlobalTheory.WeilM.hTens c A Bm x y) = -GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y
    simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, hcc, hA, hBm, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hcI,
      hX.herm, hY.skew, map_neg]
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
      GlobalTheory.WeilM.hTens c A Bm (x + y) (x + y) = GlobalTheory.WeilM.hTens c A Bm x x + GlobalTheory.WeilM.hTens c A Bm y y +
        GlobalTheory.WeilM.hTens c A Bm x y + GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y
    simp only [GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hθ' : σ θ = 1 - θ := eq_sub_of_add_eq' hθ
  have hcΘ : c (inclR (F := F) (AF F) θ) = 1 - inclR (F := F) (AF F) θ := by
    rw [hc, hcI, hθ', map_sub, map_one]
  have hswap : Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ γ') +
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) ((-1) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
    have h1 : GlobalTheory.WeilM.hTens c A Bm γ' γ = -c (GlobalTheory.WeilM.hTens c A Bm γ γ') := by rw [hconj]; ring
    have h2 : inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ =
        -c ((1 - inclR (F := F) (AF F) θ) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
      rw [h1, map_mul, ← hcΘ, hcc]; ring
    rw [h2, map_neg, htr]
    simp only [sub_mul, one_mul, neg_mul, map_sub, map_neg]
    ring
  simp only [GlobalTheory.WeilM.symp]
  rw [hexp, mul_add, mul_add, mul_add, map_add, map_add, map_add, hswap]
  ring

end GlobalTheory.VacExpand
