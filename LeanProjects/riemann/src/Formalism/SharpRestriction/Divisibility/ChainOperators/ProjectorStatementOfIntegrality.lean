import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV

def AIntO (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw) (b : Bool), ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
    MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b

theorem projector_statement_of_integrality (D : D7) (h1 : AIntO D) (hS : ThetaNormsAndLinks.SupLatticeGroupStable D) : PDVN.ConjugationNormInvariance D := by
  refine ⟨h1, ?_⟩
  rintro i j hj b _ ⟨x, hx, rfl⟩
  obtain ⟨hxB, hxF⟩ := hx
  obtain ⟨c, hc⟩ := h1 i b
  have hz : IntegralHeckeForms.AO D.nexp i j b x = IntegralHeckeForms.zO D.nexp i j b c x := by
    simp only [IntegralHeckeForms.AO, IntegralHeckeForms.zO, IntegralHeckeForms.eO, IntegralHeckeForms.eG, hc, LinearMap.smul_apply, LinearMap.coe_restrictScalars,
      Nat.cast_smul_eq_nsmul]
    rw [map_nsmul, LinearMap.smul_apply]
  have hB : IntegralHeckeForms.AO D.nexp i j b x ∈ D.nexp.Bsup i j b := by
    rw [hz]
    exact ThetaNormsAndLinks.zO_mem D i j b (fun g => hS i j hj b g) c x hxB
  have hV : IntegralHeckeForms.AO D.nexp i j b x ∈ IntegralHeckeForms.V0 D.nexp i j b := by
    have e : IntegralHeckeForms.AO D.nexp i j b x = IntegralHeckeForms.eG D.nexp i j b ((D.what₂.restRowsFiniteGroupCard : ℕ) • x) := by
      simp only [IntegralHeckeForms.AO, IntegralHeckeForms.eO, LinearMap.smul_apply, LinearMap.coe_restrictScalars, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [e]
    exact ⟨_, Submodule.smul_of_tower_mem _ _ hxF, rfl⟩
  exact ⟨⟨hB, ThetaNormsAndLinks.hermFramePairNormalForm_frameSpan_le_of_generators D i j b hV⟩, hV⟩

end Formalism.MainNotions.DIV

end
