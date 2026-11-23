import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightRepresentationIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def wspToVV (lam : InfinitePlace E → DomWeight n) : Wsp lam →ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam :=
  PiTensorProduct.lift (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam)

def vvToWsp (lam : InfinitePlace E → DomWeight n) : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] Wsp lam :=
  (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Wsp lam) (PiTensorProduct.tprod ℂ)).exists.choose

theorem vvToWsp_tenMul (lam : InfinitePlace E → DomWeight n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    vvToWsp lam (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = PiTensorProduct.tprod ℂ u :=
  (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Wsp lam) (PiTensorProduct.tprod ℂ)).exists.choose_spec u

theorem wspToVV_tprod (lam : InfinitePlace E → DomWeight n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    wspToVV lam (PiTensorProduct.tprod ℂ u) = GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u := by
  simp [wspToVV]

theorem wInf_tprod (lam : InfinitePlace E → DomWeight n) (g : UA E n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    wInf lam g (PiTensorProduct.tprod ℂ u) =
      PiTensorProduct.tprod ℂ fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g) (u v) :=
  PiTensorProduct.map_tprod _ _

theorem rep_tenMul (lam : InfinitePlace E → DomWeight n) (x : infU E n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) =
      GlobalTheory.CoefIrred.tenMul (K := ℂ) lam fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x.1) (u v) :=
  GlobalTheory.DefU.rhoK_tenMul lam (GlobalTheory.DefU.cAll x.1) u

def wspEquivVV (lam : InfinitePlace E → DomWeight n) : Wsp lam ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam :=
  LinearEquiv.ofLinear (wspToVV lam) (vvToWsp lam)
    (by
      have hu := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Formalism.L2.DIV.VV ℂ lam) (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam)).unique
        (y₁ := wspToVV lam ∘ₗ vvToWsp lam) (y₂ := LinearMap.id)
        (fun u => by simp [vvToWsp_tenMul, wspToVV_tprod]) (fun u => rfl)
      exact hu)
    (by
      apply PiTensorProduct.ext
      ext u
      simp [wspToVV_tprod, vvToWsp_tenMul])

theorem wspEquivVV_wInf (lam : InfinitePlace E → DomWeight n) (x : infU E n) (w : Wsp lam) :
    wspEquivVV lam (wInf lam x.1 w) = GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x (wspEquivVV lam w) := by
  have h : wspToVV lam ∘ₗ wInf lam x.1 = GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x ∘ₗ wspToVV lam := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun u => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [wInf_tprod, wspToVV_tprod, wspToVV_tprod, rep_tenMul]
  exact LinearMap.congr_fun h w

def wInfU (lam : InfinitePlace E → DomWeight n) : Representation ℂ (infU E n) (Wsp lam) :=
  (wInf lam).comp (infU E n).subtype

theorem isIrreducible_wInfU (lam : InfinitePlace E → DomWeight n) : (wInfU lam).IsIrreducible :=
  (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv id Function.surjective_id (wspEquivVV lam)
    (ρ := wInfU lam) (σ := GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam)
    (fun x w => wspEquivVV_wInf lam x w)).2 (GlobalTheory.DefU.Wt.isIrreducible_rep E n lam)

theorem span_wInf_infU_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n),
    Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) = ⊤ := by
  intro E _ _ _ n lam
  exact GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible (infU E n) (Wsp lam) (wInfU lam) (isIrreducible_wInfU lam)

end GlobalTheory.BCT.TrKer
