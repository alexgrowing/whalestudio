import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumFourSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairChangeBasis

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.SplitSymp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA' {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_incl {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (e : E) :
    piW τ (inclR (F := F) (AF F) e) = τ e := by
  change GlobalTheory.AdelicU.evFin F v 1 * τ e = τ e
  simp

end GlobalTheory.FlipMatch.SplitSymp

namespace GlobalTheory.FlipMatch.SplitSymp

theorem pairM_comm {K : Type} [CommRing K] {n d : ℕ} (P Q : Matrix (Fin n) (Fin d) K) :
    pairM P Q = pairM Q P := by
  simp only [pairM, mul_comm]

theorem pairM_chart {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    pairM ((b⁻¹).1 * P * (c⁻¹).1ᵀ) (-(b.1ᵀ * A * Q * Bᵀ * c.1)) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  first
  | exact @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | (apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis ..)

theorem sum_four_swap_pairs_alt {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  first
  | exact @_root_.GlobalTheory.SumFourSwap.sum_four_swap
  | exact _root_.GlobalTheory.SumFourSwap.sum_four_swap
  | (apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumFourSwap.sum_four_swap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumFourSwap.sum_four_swap ..)

theorem symp_at_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → ∀ (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)),
    At (evFin F v) x → At (evFin F v) u →
    ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u) - pairM (coY σ X Y t b c x) (coX t b c u)) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hX hY ψ v t b c x u hx hu
  have hss := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hz : At (evFin F v) ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) *
      GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) := by
    intro r hr
    have h : ∀ i j, r • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx r hr) i) j
      simpa using this
    rw [← mul_smul_comm]
    unfold GlobalTheory.WeilM.hTens
    simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hz]
  change psiLoc ψ v _ = psiLoc ψ v _
  congr 1
  rw [pairM_comm (coY σ X Y t b c x), coX, coX, coY, coY, pairM_chart, pairM_chart]
  simp only [map_mul, map_neg, map_one, neg_one_mul, GlobalTheory.WeilM.hTens, map_sum, piW_cA', piW_incl,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hss, AlgHom.comp_apply, hX, hY]
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_neg]
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.FlipMatch.SplitSymp
