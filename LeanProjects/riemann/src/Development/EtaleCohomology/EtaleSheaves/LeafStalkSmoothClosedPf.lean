import Development.EtaleCohomology.EtaleSheaves.LeafSmoothOfNormalPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order

namespace LateralTheory.E.LeafStalkSmoothClosedPf

theorem coheight_le_topDim {X : Scheme.{0}} (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let := specializationOrder X
  have h := coheight_le_krullDim
    (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)
  rwa [coheight_orderIso] at h

theorem stalk_not_isField {X : Scheme.{0}} [IsIntegral X] (y : X) (hy : y ≠ genericPoint X) :
    ¬ IsField (X.presheaf.stalk y) := by
  intro hF
  let := hF.toField
  have h0 : ringKrullDim (X.presheaf.stalk y) = 0 := ringKrullDim_eq_zero_of_field _
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have hc : coheight y = 0 := by exact_mod_cast h0
  rw [coheight_eq_zero] at hc
  have h1 : y ≤ genericPoint X := genericPoint_specializes y
  have h2 : genericPoint X ≤ y := hc h1
  exact hy (Specializes.antisymm (h2 : y ⤳ genericPoint X) (h1 : genericPoint X ⤳ y)).eq

theorem stalk_dvr {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (y : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk y)) (hd : topologicalKrullDim X = 1)
    (hy : y ≠ genericPoint X) : IsDiscreteValuationRing (X.presheaf.stalk y) := by
  have hc : coheight y ≤ 1 := by
    have := (coheight_le_topDim y).trans hd.le
    exact_mod_cast this
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hc
  have : Ring.DimensionLEOne (X.presheaf.stalk y) :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain (X.presheaf.stalk y) := {}
  exact ((IsDiscreteValuationRing.TFAE _ (stalk_not_isField y hy)).out 2 0).mp this

set_option backward.isDefEq.respectTransparency false in
theorem LeafStalkSmoothClosed_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed := by
  intro Ω _ _ C c _ hc hn hd y hy
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have := hn y
  have : IsDiscreteValuationRing (C.presheaf.stalk y) := stalk_dvr y (hn y) hd hy
  have hE := LocallyOfFiniteType.stalkMap c y
  algebraize [(c.stalkMap y).hom]
  let p : Spec (CommRingCat.of Ω) := c y
  let K' := (Spec.structureSheaf Ω).presheaf.stalk p
  let e : Ω ≃ₐ[Ω] K' := IsLocalization.atUnits _ p.asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic Ω K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField Ω)).toField
  let : Field ((Sp Ω).presheaf.stalk (c y)) := this
  have : PerfectField ((Sp Ω).presheaf.stalk (c y)) :=
    Algebra.IsAlgebraic.perfectField (K := Ω) (L := (Spec.structureSheaf Ω).presheaf.stalk p)
  exact GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _

end LateralTheory.E.LeafStalkSmoothClosedPf
