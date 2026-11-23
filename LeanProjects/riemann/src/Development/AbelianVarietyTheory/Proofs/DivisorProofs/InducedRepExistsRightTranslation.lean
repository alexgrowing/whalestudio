import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalInducedSpaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL

noncomputable section

open GlobalTheory.RankFibre

namespace GlobalTheory.KSplit.RightTr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lid_tmul_one (t : ℂ ⊗[ℂ] ℂ) : (TensorProduct.lid ℂ ℂ t) ⊗ₜ[ℂ] (1 : ℂ) = t := by
  apply (TensorProduct.lid ℂ ℂ).injective
  simp

theorem lid_law (ν β : kˣ →* ℂˣ) (a b : ℕ) (p : parab k (blocks a b)) (t : ℂ ⊗[ℂ] ℂ) :
    TensorProduct.lid ℂ ℂ (((twist ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) (deltaHalf k (Two (Fin a) (Fin b)))).comp
        (leviProj k (blocks a b))) p t) =
      ofChar (parChar ν β a b) p (TensorProduct.lid ℂ ℂ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul c d =>
    simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe]
    simp [parChar, detRep, ofChar_apply]
    ring
  | add s t hs ht => simp only [map_add, hs, ht]

theorem indScalVal_mem (ν β : kˣ →* ℂˣ) (a b : ℕ)
    (F : IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) :
    indScalVal ν β a b F ∈ indScal ν β a b := by
  refine ⟨?_, fun p x => ?_⟩
  · have hF := isSmooth_parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) F
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hF.mem_nhds (by exact LinearMap.congr_fun (map_one (parInd _ _)) F)) fun g hg => ?_)
    have hg' : parInd _ _ g F = F := hg
    funext x
    show TensorProduct.lid ℂ ℂ (F.1.1 (x * g)) = TensorProduct.lid ℂ ℂ (F.1.1 x)
    rw [← parInd_apply, hg']
  · show TensorProduct.lid ℂ ℂ (F.1.1 (p * x)) = _
    rw [F.1.2 p x]
    exact lid_law ν β a b p _

def scalEquiv (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    indScal ν β a b ≃ₗ[ℂ] IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
  LinearEquiv.symm
    { (indScalVal ν β a b).codRestrict (indScal ν β a b) (indScalVal_mem ν β a b) with
      invFun := fun f => indScalLift ν β a b f.2
      left_inv := fun F => by
        apply Subtype.ext; apply Subtype.ext; funext x
        exact lid_tmul_one (F.1.1 x)
      right_inv := fun f => Subtype.ext (indScal_scal_lift ν β a b f.2) }

def rep (ν β : kˣ →* ℂˣ) (a b : ℕ) : Representation ℂ (GL (Fin (a + b)) k) (indScal ν β a b) where
  toFun g := (scalEquiv ν β a b).symm.toLinearMap ∘ₗ
    prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β) g ∘ₗ (scalEquiv ν β a b).toLinearMap
  map_one' := by
    ext f : 1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_one, map_mul, Module.End.one_apply,
    Module.End.mul_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    ext f : 1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_one, map_mul, Module.End.one_apply,
    Module.End.mul_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem rep_apply (ν β : kˣ →* ℂˣ) (a b : ℕ) (g : GL (Fin (a + b)) k) (f : indScal ν β a b) (x : GL (Fin (a + b)) k) :
    ((rep ν β a b g f : indScal ν β a b) : GL (Fin (a + b)) k → ℂ) x = (f : GL (Fin (a + b)) k → ℂ) (x * g) :=
  indScal_lift_apply ν β a b f.2 (x * g)

theorem scal_main (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    ∃ ρ : Representation ℂ (GL (Fin (a + b)) k) (indScal ν β a b),
      (∀ g f x, ((ρ g f : indScal ν β a b) : GL (Fin (a + b)) k → ℂ) x = (f : GL (Fin (a + b)) k → ℂ) (x * g)) ∧
      IsSmooth ρ ∧ Nonempty (ρ.Equiv (prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β))) := by
  refine ⟨rep ν β a b, rep_apply ν β a b, fun f => ?_, ⟨Representation.Equiv.mk (scalEquiv ν β a b) fun g => ?_⟩⟩
  · have hs := isSmooth_prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β) (scalEquiv ν β a b f)
    convert hs using 1
    ext g
    simp only [Set.mem_setOf_eq]
    show (scalEquiv ν β a b).symm _ = f ↔ _
    rw [LinearEquiv.symm_apply_eq]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  · ext f : 1
    simp only [rep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

end GlobalTheory.KSplit.RightTr

namespace GlobalTheory.KSplit

theorem indSp_rightTr_equiv_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ)
    (α β : kˣ →* ℂˣ), IsSmoothChar α → IsSmoothChar β →
    ∃ ρ : Representation ℂ (GL (Fin (a + a')) k) (GlobalTheory.KSplit.indSp a a' α β),
      (∀ g f x, ((ρ g f : GlobalTheory.KSplit.indSp a a' α β) : GL (Fin (a + a')) k → ℂ) x = (f : GL (Fin (a + a')) k → ℂ) (x * g)) ∧
      IsSmooth ρ ∧ Nonempty (ρ.Equiv (prod₂ (detRep (Fin a) α) (detRep (Fin a') β))) := by
  intro k _ _ _ _ a a' α β _ _
  have h := GlobalTheory.KSplit.RightTr.scal_main (α * β⁻¹) β a a'
  have hα : α * β⁻¹ * β = α := by ext x; simp
  rw [hα, ← indSp_eq_indScal] at h
  exact h

end GlobalTheory.KSplit

end
