import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.MultOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagSM (l d : ℕ) : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d) :=
  ⟨fun i j => if i = j then d else 0, fun i => by simp, fun j => by simp⟩

theorem entry_le {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (i j : Fin l) : b.1 i j ≤ d := by
  calc b.1 i j ≤ ∑ j, b.1 i j :=
        Finset.single_le_sum (f := b.1 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = d := by simpa using b.2.1 i

theorem isSmooth_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _

theorem isSmooth_piTensor_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (piTensor (segTerm σ.ρ l)) :=
  isSmooth_piTensor fun a => isSmooth_segTerm σ a

theorem isIrreducible_piTensor_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ l)).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => isIrreducible_segTerm σ a)
    fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (isSmooth_segTerm σ a)
      (isIrreducible_segTerm σ a) φ hφ

theorem hasFiniteLength_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    HasFiniteLength (segTerm σ.ρ l a) :=
  (⟨_, segTerm σ.ρ l a, isSmooth_segTerm σ a, isIrreducible_segTerm σ a⟩ :
    IrrRep (GL (Fin d) k)).hasFiniteLength

theorem isIrreducible_piTensor_cls {ι : Type} [Finite ι] {n : ι → ℕ}
    (s : ∀ j, IrrCl (GL (Fin (n j)) k)) : (piTensor fun j => (s j).rep.ρ).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => (s j).rep.irr)
    fun j φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (s j).rep.smooth (s j).rep.irr φ hφ

theorem exists_other {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    {i j : Fin l} (h : b.1 i j < d) : ∃ j', j' ≠ j ∧ 0 < b.1 i j' := by
  by_contra hc
  push Not at hc
  have h2 := b.2.1 i
  simp only [Fintype.card_fin] at h2
  rw [Finset.sum_eq_single j (fun j' _ hj' => Nat.le_zero.1 (hc j' hj')) (by simp)] at h2
  omega

theorem cell_eq_zero_of_mid (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin d)
    (h : ∃ i j, 0 < b.1 i j ∧ b.1 i j < d) :
    jhMult (piTensor (segTerm σ.ρ l)) (cellFunctor f g (piTensor (segTerm σ.ρ l))) = 0 := by
  obtain ⟨i₀, j₀, h0, h1⟩ := h
  obtain ⟨j₁, hj, h2⟩ := exists_other b h1
  have hcs := (hG k).2 (Fin l) (Fin l) (fun _ => Fin d) (fun _ => Fin d)
    (fun i j => Fin (b.1 i j)) f g (fun _ => σ.V) (segTerm σ.ρ l) (isSmooth_segTerm σ) (hasFiniteLength_segTerm σ)
  obtain ⟨T, -, hT⟩ := hcs
  rw [hT ⟨_, piTensor (segTerm σ.ρ l), isSmooth_piTensor_segTerm σ, isIrreducible_piTensor_segTerm σ⟩]
  refine Finset.sum_eq_zero fun s _ => mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i₀) ?_) _
  have hc : IsCuspidal (segTerm σ.ρ l i₀) := GlobalTheory.LocGL.isCuspidal_twist hσ (isSmoothChar_of_isUnram (isUnram_absPow k _))
  have hne : unipRad k (f i₀) ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    have e0 : blk (f i₀) (f i₀ ⟨j₀, ⟨0, h0⟩⟩) = j₀ := by simp [blk]
    have e1 : blk (f i₀) (f i₀ ⟨j₁, ⟨0, h2⟩⟩) = j₁ := by simp [blk]
    rcases lt_or_gt_of_ne hj with hlt | hlt
    · exact ⟨_, _, e1.symm ▸ e0.symm ▸ hlt⟩
    · exact ⟨_, _, e0.symm ▸ e1.symm ▸ hlt⟩
  haveI := hc.2 l (fun j => b.1 i₀ j) (f i₀) hne
  exact jhMult_of_subsingleton (isIrreducible_piTensor_cls _) _

end PositivityTheory.Pf1.SegRepC.MultOne

end
