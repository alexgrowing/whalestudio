import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaHalf

variable {D : D7}

theorem isHalf_iff_smul {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := by
  constructor
  · intro h; ext i j; rw [Matrix.smul_apply, smul_eq_mul, h i j]
  · intro h i j; have := congrFun (congrFun h i) j; rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem isHalf_mul_left {k m n : ℕ} {e : AE D} (A : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (A * u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.mul_smul, hu]

theorem isHalf_mul_right {k m n : ℕ} {e : AE D} {u : Mx D k m} (B : Mx D m n) (hu : IsHalf e u) :
    IsHalf e (u * B) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.smul_mul, hu]

theorem isHalf_smul {m n : ℕ} {e : AE D} (c : AE D) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (c • u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [smul_comm, hu]

theorem isHalf_adj_of_cA {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf (cA D e) z) :
    IsHalf e (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  conv_lhs => rw [← GlobalTheory.DualPairCheck.cA_cA e]
  rw [← map_mul, hz j i]

theorem isHalf_cA_adj {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf e z) :
    IsHalf (cA D e) (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← map_mul, hz j i]

theorem isHalf_ofAdj {L S : HSp D} {e : AE D} {z : Mx D L.rank S.rank} (hz : IsHalf e (adj z)) :
    IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S z) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  exact isHalf_smul _ (isHalf_mul_left _ (isHalf_mul_right _ hz))

theorem ofAdj_rat_mul_half : ∀ (D : D7) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (e : AE D) (y : WO S L''), (IsHalf (cA D e) y → IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) ∧ (IsHalf e y → IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) := by
  intro D L S L'' τ e y
  exact ⟨fun h => isHalf_ofAdj (isHalf_adj_of_cA (isHalf_mul_left _ h)),
    fun h => isHalf_ofAdj (isHalf_cA_adj (isHalf_mul_left _ h))⟩

end GlobalTheory.KappaHalf

end
