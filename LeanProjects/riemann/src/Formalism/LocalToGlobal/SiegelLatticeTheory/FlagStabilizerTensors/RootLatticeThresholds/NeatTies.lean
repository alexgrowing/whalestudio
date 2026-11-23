import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat

noncomputable section
open scoped Classical InnerProductSpace ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf

section FinXN

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} (Y : Full X)

theorem sharp_bij_of_neat (u : D.what₂.Word) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Function.Bijective (sharp Y.hK (Y.cs u)) := by
  have hst : Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u Y.hK) := hN
  let cls : (Y.cs u).Cl → Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) :=
    fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)
  have hcls : Function.Bijective cls := by
    refine ⟨fun ρ ρ' h => ?_, fun c => ?_⟩
    · obtain ⟨a, ⟨γ, rfl⟩, κ, hκ, hab⟩ := (DoubleCoset.eq _ _ _ _).1 h
      obtain ⟨ρ0, _, huniq⟩ := Y.colReps u ((Y.cs u).h ρ')
      have h1 := huniq ρ ⟨γ, ⟨κ, hκ⟩, hab⟩
      have h2 := huniq ρ' ⟨1, 1, by simp⟩
      exact h1.trans h2.symm
    · induction c using Quotient.inductionOn' with
      | h g =>
        obtain ⟨ρ, ⟨γ, κ, hg⟩, _⟩ := Y.colReps u g
        refine ⟨ρ, ?_⟩
        show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ g
        rw [DoubleCoset.eq]
        exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hg⟩
  let ec := Equiv.ofBijective cls hcls
  let s : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Hfin X u := fun c => (Y.cs u).h (ec.symm c)
  have hs : ∀ c, DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (s c) = c := fun c => ec.apply_symm_apply c
  obtain ⟨e, he⟩ := Formalism.L2.SG.ColsDim.columns_decomposition (Gam X u) (Hinf X u) (Hfin X u) ℂ (X.Vpi u) (iotaI X u)
    (iotaF X u) (Ku X u Y.hK) (psiK X u Y.hK) (piRep X u) s hs hst
  have key : ∀ T ρ, (sharp Y.hK (Y.cs u) T) ρ =
      (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (e T (cls ρ))) := by
    intro T ρ
    have hsρ : s (cls ρ) = (Y.cs u).h ρ := by
      show (Y.cs u).h (ec.symm (ec ρ)) = _
      rw [ec.symm_apply_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm
      (LinearMap.toContinuousLinearMap ((LinearMap.proj ((1 : Hinf X u), (Y.cs u).h ρ)).comp T.1)) = _
    congr 2
    refine LinearMap.ext fun ξ => ?_
    refine Eq.trans ?_ (he T (cls ρ) ξ).symm
    rw [hsρ]
    rfl
  refine ⟨fun T T' h => ?_, fun x => ?_⟩
  · apply e.injective
    funext c
    obtain ⟨ρ, rfl⟩ := hcls.2 c
    have h1 : (sharp Y.hK (Y.cs u) T) ρ = (sharp Y.hK (Y.cs u) T') ρ := by rw [h]
    rw [key T ρ, key T' ρ] at h1
    exact LinearMap.toContinuousLinearMap.injective ((InnerProductSpace.toDual ℂ (X.Vpi u)).symm.injective h1)
  · let d : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Module.Dual ℂ (X.Vpi u) :=
      fun c => LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm c)))
    refine ⟨e.symm d, ?_⟩
    ext ρ
    refine (key (e.symm d) ρ).trans ?_
    rw [e.apply_symm_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm (ec ρ)))))) = x ρ
    rw [LinearEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply, ec.symm_apply_apply]

theorem finX_of_neat (hN : ∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) (hin : ∀ u, InHH X u Y.hK) (hfin : FiniteDimensional ℂ (HHX X))
    (hfib : ∀ u u' (t : RT Y u u'), Finite (fib Y t))
    (hpi : ∀ u u' (s₁ s₂ s₁' s₂' : TT Y u u'), s₁.toTerm = s₁'.toTerm → s₂.toTerm = s₂'.toTerm →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁' = rowOf Y.TR (Y.cs u) (Y.cs u') s₂' →
      s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂')) (hG : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F)
    (hvol : VolPosC) : FinX Y where
  shInj u := (sharp_bij_of_neat Y u (hN u)).1
  shSurj u := (sharp_bij_of_neat Y u (hN u)).2
  inHH := hin
  puLin u := Formalism.L2.SG.PoincareInHH.Cut.puLinear_holds X u Y.hK (Y.Dt u)
  finHH := hfin
  fibFin := hfib
  pairIndep := hpi
  Greal := hG
  cdEx n ε := cd_haar_scaling D.cd n ε
  volPos u := hvol D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X)

end FinXN

end Formalism.L2.SG.Pf
