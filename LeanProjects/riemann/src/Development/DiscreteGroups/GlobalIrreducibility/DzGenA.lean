import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzGenDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace DiscreteGroups.sglob.DzType

theorem genA : GenA := by
  intro H k _ _ _ _ m

  obtain ⟨E⟩ := GlobalTheory.LocGL.DetQuot.nonempty_equiv_multiProd (k := k) (eOne m)
    (θ := fun _ : Fin m => (1 : kˣ →* ℂˣ)) (Θ := (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (fun g => by simp)
  have hs1 : IsSmoothChar (detChar (Fin 1) (1 : kˣ →* ℂˣ)) := by
    show IsOpen ((detChar (Fin 1) (1 : kˣ →* ℂˣ)).ker : Set (GL (Fin 1) k))
    convert isOpen_univ
    ext g
    simp
  have hs : ∀ _ : Fin m, IsSmooth (detRep (Fin 1) (1 : kˣ →* ℂˣ)) := fun _ => (isSmooth_ofChar_iff _).2 hs1
  have hi : ∀ _ : Fin m, (detRep (Fin 1) (1 : kˣ →* ℂˣ)).IsIrreducible := fun _ => isIrreducible_ofChar _
  have hu : ∀ _ : Fin m, IsUnitarisable (detRep (Fin 1) (1 : kˣ →* ℂˣ)) := fun _ =>
    (isUnitarisable_ofChar_iff _).2 fun g => by simp
  have hirr := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd H (eOne m)
    (σ := fun _ : Fin m => detRep (Fin 1) (1 : kˣ →* ℂˣ)) hs hi hu
  refine ⟨(GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv E).2 hirr, ?_, ?_⟩
  ·
    obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (eOne m)
      (ρ := ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (x := (1 : ℂ)) fun g _ => by simp
    show fixed (parInd (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ))) (GlobalTheory.SplitWeil.KO k (Fin m)) ≠ ⊥
    intro hbot
    have h0 : f ∈ (⊥ : Submodule ℂ _) := hbot ▸ hf
    rw [Submodule.mem_bot] at h0
    rw [h0] at hf1
    exact absurd hf1 (by simp)
  ·
    have hc : HasCentralChar (multiProd (eOne m) fun _ : Fin m => detRep (Fin 1) (1 : kˣ →* ℂˣ)) 1 := by
      intro z f
      rw [GlobalTheory.BoundaryMaps.multiProd_scalar (eOne m) _ (fun _ => (1 : kˣ →* ℂˣ))
        (fun _ => by simpa using GlobalTheory.BoundaryMaps.hasCentralChar_detRep (k := k) 1 (1 : kˣ →* ℂˣ)) z f]
      simp
    exact GlobalTheory.LocGL.hasCentralChar_of_equiv E.symm hc

end DiscreteGroups.sglob.DzType
