import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfMatrixMoveDeepCongruenceBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatApprox

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem actO_actO' {D : D7} (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem isHalf_actO' {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

end GlobalTheory.AdForm.RatApprox

namespace GlobalTheory.AdForm.RatApprox

set_option maxHeartbeats 2000000 in

theorem approx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have hi' : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨NB, hNB⟩ := GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent (I.rec7 l Z) (A.chr (i + 1)) (hA.chr ⟨i, hi⟩).1
  have hee : A.e * A.e = A.e := GlobalTheory.PlaceDatum.idemSum_mul_self hA.idem
  have hez : IsHalf A.e (z.map fun r => A.e * incA (I.rec7 l Z) r) := fun r s => by
    simp only [Matrix.map_apply, ← mul_assoc, hee]
  have hM := isHalf_actO' κ.1⁻¹ κ'.1⁻¹ hez
  obtain ⟨NC, hNC⟩ := GlobalTheory.T.halfMatrix_move_deepCongruence_bound (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i hi') (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hM k hk
  have hfin : ∀ j (hj : j ≤ B.R.m) (β : Ch j), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (A.K j hj β).lev := fun j hj β => by
    obtain ⟨n, hn, h⟩ := hA.fin j hj β
    exact ⟨n, hn, fun κ _ => h κ⟩
  have step : ∀ j (hj : j ≤ B.R.m) (β : Ch j) (g : A.U j β), ∃ w : A.U j β, A.chi j β w = 1 ∧
      (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) (g * w).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧
      ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin (B.R.N j)), Valued.v (adAt (I.rec7 l Z).host.F P (finM _ (rankN (I.rec7 l Z) j hj) w.1 r s - (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ)) := by
    intro j hj β g
    obtain ⟨g₀, hg₀⟩ := ((hA.U j hj β g.1).1 g.2).2
    obtain ⟨zz, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes I hI hP l Z a _ j hj _ (A.K j hj β).lev (hfin j hj β) (max NB NC) (show TC.GA B (B.R.N j) from g₀.1)
    obtain ⟨w, hw⟩ := GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift I hI hP l Z u a Ch A hA j hj β zz
    refine ⟨w, ?_, fun P hPQ => ?_, fun P r s => ?_⟩
    · rw [hA.chi j hj β w zz hw, hz1]
    · obtain ⟨M, hM⟩ := hz2 P hPQ
      refine ⟨M, fun r s => ?_⟩
      rw [← hM r s, Subgroup.coe_mul, GlobalTheory.RepLattice.finM_mul', ← hg₀, ← hw]
      rfl
    · rw [← hw]
      exact hz3 P r s
  obtain ⟨w, hw1, hw2, hw3⟩ := step i hi' α κ
  obtain ⟨w', hw1', hw2', hw3'⟩ := step (i + 1) hi γ κ'
  have hwG : w.1 ∈ GfC _ := ((hA.U i hi' α w.1).1 w.2).1
  have hwG' : w'.1 ∈ GfC _ := ((hA.U (i + 1) hi γ w'.1).1 w'.2).1
  have dB : ∀ {n : ℕ} (f : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))), (∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ))) → ∀ N₀ : ℕ, N₀ ≤ max NB NC → ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-(N₀ : ℤ)) := by
    intro n f hf N₀ hN P r s
    exact (hf P r s).trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hN)))
  obtain ⟨x₁, hx₁, hcx⟩ := hNB _ (rankN (I.rec7 l Z) i hi') κ.1 w.1 hwG (dB _ hw3 NB (le_max_left _ _)) x hx
  obtain ⟨y₁, hy₁, hcy⟩ := hNB _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 w'.1 hwG' (dB _ hw3' NB (le_max_left _ _)) y hy
  obtain ⟨t, ht, hth, hte⟩ := hNC w.1 w'.1 hwG hwG' (dB _ hw3 NC (le_max_right _ _)) (dB _ hw3' NC (le_max_right _ _))
  refine ⟨κ * w, κ' * w', x₁, y₁, t, hw2, hw2', hx₁, hy₁, hcx, hcy, ?_, ?_, ht, hth, ?_⟩
  · rw [map_mul, hw1, mul_one]
  · rw [map_mul, hw1', mul_one]
  · rw [← hte, actO_actO']
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev]

end GlobalTheory.AdForm.RatApprox
