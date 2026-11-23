import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA

noncomputable section

open NumberField
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.TreeNode

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mulChi_absC_mulChi (n : ℕ) (z z' : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E z) (mulChi n (Model.absC E z') φ) = mulChi n (Model.absC E (z' + z)) φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
    ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem tw_tw {n : ℕ} (V : Submodule ℂ (Sm E n)) (a b : ℂ) : tw (tw V a) b = tw V (a + b) := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨φ, hφ, (mulChi_absC_mulChi n b a φ).symm⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨φ, hφ, rfl⟩, mulChi_absC_mulChi n b a φ⟩

theorem map_mem_finVec {n : ℕ} {V : Submodule ℂ (Sm E n)} (f : Sm E n →ₗ[ℂ] Sm E n)
    (heq : ∀ o, ∀ φ ∈ V, f (act o φ) = act o (f φ)) {φ : Sm E n} (hφ : φ ∈ V)
    (hfin : φ ∈ finVec (cptRep E n)) : f φ ∈ finVec (cptRep E n) := by
  have h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k φ)) := hfin
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k (f φ)))
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k φ)).map f) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, heq (.cpt k) φ hφ⟩

theorem nodeEmb : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.NodeEmb := by
  rintro E _ _ _ r s V V₁ V₂ z₁ z₂ hV ⟨f, hf, hinj, heq⟩
  refine ⟨f, fun φ hφ => Submodule.subset_span ⟨?_, ?_⟩, hinj, heq⟩
  · have e₁ : tw (tw V₁ (z₁ - (s : ℂ) / 2)) ((s : ℂ) / 2) = tw V₁ z₁ := by
      rw [tw_tw, sub_add_cancel]
    have e₂ : tw (tw V₂ (z₂ + (r : ℂ) / 2)) (-(r : ℂ) / 2) = tw V₂ z₂ := by
      rw [tw_tw, neg_div, add_neg_cancel_right]
    change MemInd2 (tw (tw V₁ (z₁ - (s : ℂ) / 2)) ((s : ℂ) / 2)) (tw (tw V₂ (z₂ + (r : ℂ) / 2)) (-(r : ℂ) / 2)) (f φ)
    rw [e₁, e₂]
    exact hf φ hφ
  · exact map_mem_finVec f heq hφ (hV.aut φ hφ).kfin

end GlobalTheory.CompanionTheory.TreeNode

end
