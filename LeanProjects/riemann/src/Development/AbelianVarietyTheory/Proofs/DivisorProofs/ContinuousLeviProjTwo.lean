import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatDistributionEqZeroBaire
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlParabolicOrbitRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitStabilizerDeterminantCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

noncomputable section

namespace GlobalTheory.LocRankBig

open GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem totallyDisconnected : TotallyDisconnectedSpace k := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem nonarchimedeanGroup_GL (n : ℕ) : NonarchimedeanGroup (GL (Fin n) k) := by
  haveI := totallyDisconnected (k := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (GL (Fin n) k) :=
    ⟨isTotallyDisconnected_of_image (f := fun g : GL (Fin n) k => g.val) Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  haveI : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  haveI : NonarchimedeanGroup (KO k (Fin n)) := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  exact NonarchimedeanGroup.nonarchimedean_of_emb (KO k (Fin n)).subtype
    GlobalTheory.SplitFlip.isOpen_KO.isOpenEmbedding_subtypeVal

@[reducible] def act (k : Type) [Field k] (n x x' : ℕ) :
    MulAction (GL (Fin n) k × parab k (GlobalTheory.ThK.MidJac.e2 x x')) (Matrix (Fin n) (Fin (x + x')) k) where
  smul γ X := (γ.1 : Matrix (Fin n) (Fin n) k) * X *
    Matrix.transpose ((γ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)
  one_smul X := by
    show ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      Matrix.transpose ((1 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) = X
    simp
  mul_smul γ δ X := by
    show ((γ.1 * δ.1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      Matrix.transpose ((γ.2.1 * δ.2.1 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) =
      (γ.1 : Matrix (Fin n) (Fin n) k) * ((δ.1 : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose ((δ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)) *
        Matrix.transpose ((γ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)
    simp [Matrix.transpose_mul, Matrix.mul_assoc]

def chi (n x x' : ℕ) (α β : kˣ →* ℂˣ) : GL (Fin n) k × parab k (GlobalTheory.ThK.MidJac.e2 x x') →* ℂˣ :=
  ((deltaHalf k _ * GlobalTheory.ThK.DetProd.twoDet x x' α β).comp
      ((leviProj k (GlobalTheory.ThK.MidJac.e2 x x')).comp (MonoidHom.snd _ _))) *
    ((detChar _ (β * absPow k ((-(n : ℝ) / 2 : ℝ) : ℂ)))⁻¹.comp
      ((parab k (GlobalTheory.ThK.MidJac.e2 x x')).subtype.comp (MonoidHom.snd _ _))) *
    ((detChar _ (β * α⁻¹ * absPow k ((-((x + x' : ℕ) : ℝ) / 2 : ℝ) : ℂ)))⁻¹.comp (MonoidHom.fst _ _))

end Local

end GlobalTheory.LocRankBig
