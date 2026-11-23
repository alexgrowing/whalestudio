import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EtAICPf

def Split : Prop := ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], AIC T →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j))

def DomOpen : Prop := ∀ (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D] [Algebra.Etale T D],
  AIC T → IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap T D)))

theorem EtAIC_of (hS : Split) (hD : DomOpen) : LateralTheory.E.t_E1Cut.EtAIC := by
  intro T C _ _ _ _ _ hT
  obtain ⟨n, e, he, hdom⟩ := hS T C hT
  refine ⟨n, e, he, fun j => ?_⟩
  have : Algebra.Etale C (Localization.Away (e j)) := inferInstance
  have : Algebra.Etale T (Localization.Away (e j)) := Algebra.Etale.comp T C _
  have h := hD T (Localization.Away (e j)) hT
  rwa [IsScalarTower.algebraMap_eq T C (Localization.Away (e j))] at h

end LateralTheory.E.EtAICPf
