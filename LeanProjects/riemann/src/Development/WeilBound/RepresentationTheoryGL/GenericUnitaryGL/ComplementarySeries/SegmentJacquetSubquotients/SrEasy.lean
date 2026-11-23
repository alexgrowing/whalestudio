import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
import Development.WeilBound.CoreStatements.PublishedTheorems.SegmentRepresentations.IsIrreduciblePiTensorSegTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrEasy

theorem isSmooth_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _

private theorem isSmooth_segTerm_segment_jacquet_subquotients {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth ((isSmoothChar_absPow _).comp _ continuous_glDet)

theorem hasFiniteLength_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := by
  have h := GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k l (l * d)
    (fun _ => d)
    (fun a => ⟨σ.V, segTerm σ.ρ l a, isSmooth_segTerm_segment_jacquet_subquotients σ a, isIrreducible_twist σ.irr _⟩)
    (consecBlocks l d)
  exact h

theorem isSmooth_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  have h := hπ (v : V)
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hg
    exact congrArg Subtype.val hg
  · intro hg
    exact Subtype.ext hg

end SrEasy

open SrEasy

private theorem exists_irreducible_subrep_le_of_ne_bot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hwf : WellFoundedLT (Subrepresentation ρ))
    (T : Subrepresentation ρ) (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation ρ, S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  obtain ⟨S, ⟨hS0, hST⟩, hmin⟩ := hwf.wf.has_min
    {S : Subrepresentation ρ | S.toSubmodule ≠ ⊥ ∧ S.toSubmodule ≤ T.toSubmodule} ⟨T, hT, le_rfl⟩
  refine ⟨S, ?_, hST⟩
  let img : Subrepresentation S.toRepresentation → Subrepresentation ρ := fun U =>
    ⟨U.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨S.toRepresentation g w, U.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hne : (⊥ : Subrepresentation S.toRepresentation) ≠ ⊤ := by
    intro h
    apply hS0
    rw [eq_bot_iff]
    intro v hv
    have h1 : (⟨v, hv⟩ : S.toSubmodule) ∈ (⊤ : Subrepresentation S.toRepresentation).toSubmodule :=
      show _ ∈ (⊤ : Submodule ℂ S.toSubmodule) from Submodule.mem_top
    rw [← h] at h1
    have h0 : (⟨v, hv⟩ : S.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 h1
    have h2 : v = 0 := congrArg Subtype.val h0
    rw [h2]
    exact Submodule.zero_mem _
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun U => ?_ }
  by_cases hU : U.toSubmodule = ⊥
  · left
    exact Subrepresentation.ext hU
  · right
    have himg0 : (img U).toSubmodule ≠ ⊥ := by
      intro h
      apply hU
      apply Submodule.map_injective_of_injective S.toSubmodule.injective_subtype
      rw [Submodule.map_bot]
      exact h
    have himgS : img U ≤ S := by
      rintro _ ⟨w, _, rfl⟩
      exact w.2
    have heq : img U = S := by
      by_contra hne'
      exact hmin (img U) ⟨himg0, le_trans himgS hST⟩ (lt_of_le_of_ne himgS hne')
    apply Subrepresentation.ext
    apply eq_top_iff.2
    intro w _
    have hw : (w : V) ∈ (img U).toSubmodule := by
      rw [heq]
      exact w.2
    obtain ⟨u, hu, hu'⟩ := hw
    have : u = w := Subtype.ext hu'
    rw [← this]
    exact hu

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  have hfl := hasFiniteLength_prod (l := l) σ
  rw [hasFiniteLength_iff_wellFounded] at hfl
  exact exists_irreducible_subrep_le_of_ne_bot hfl.2 T hT

set_option synthInstance.maxHeartbeats 400000 in

theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2

private theorem hasFiniteLength_subrepresentation {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : HasFiniteLength π) (S : Subrepresentation π) :
    HasFiniteLength S.toRepresentation :=
  GlobalTheory.ProdLength.hasFiniteLength_of_injective
    (LinearMap.intertwiningMap_of_isIntertwiningMap S.toRepresentation π S.toSubmodule.subtype
      (fun _ _ => rfl))
    (fun a b h => Subtype.ext h) hπ

set_option synthInstance.maxHeartbeats 400000 in

theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation
    (isSmooth_sub (isSmooth_prod σ) S) (hasFiniteLength_subrepresentation (hasFiniteLength_prod σ) S)

end PositivityTheory.RgGu.SRC

end
