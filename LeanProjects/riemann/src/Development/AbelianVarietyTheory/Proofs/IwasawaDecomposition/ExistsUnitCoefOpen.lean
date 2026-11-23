import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpen

theorem glue_units {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens) (P : Z.Opens → Prop)
    (hP : ∀ p ∈ V, ∃ W : Z.Opens, IsAffineOpen W ∧ W ≤ V ∧ P W ∧ p ∈ W)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → P W → ∃ a : Γ(Z, W)ˣ,
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a.val)) :
    ∃ a : Γ(Z, V)ˣ, ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a.val) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V ∧ P W}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2.1 i.2.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨W, hW, hWV, hPW, hpW⟩ := hP p hp
    exact ⟨⟨W, hW, hWV, hPW⟩, hpW⟩
  have hcov : V ≤ iSup fun i : I => i.1 := fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)
  have key : ∀ (i j : I) (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (i.1 ⊓ j.1)),
      ev z _ hz (resG Z inf_le_left (a i).val) = ev z _ hz (resG Z inf_le_right (a j).val) := by
    intro i j L _ z hz
    have hi := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
    have hj := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
    rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
    exact uniq L z (GlobalTheory.FlagMod.le_preimage_mono i.2.2.1 hi) _ _ (ha i L z hi) (ha j L z hj)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i).val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i).val) (b := resG Z inf_le_right (a j).val)
        fun L _ z hz => key i j L z hz)
  obtain ⟨t, ht, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i)⁻¹.val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i)⁻¹.val) (b := resG Z inf_le_right (a j)⁻¹.val)
        fun L _ z hz => by
          have e := key i j L z hz
          have e₁ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_left)) : Γ(Z, i.1) →+* L) (a i)
          have e₂ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_right)) : Γ(Z, j.1) →+* L) (a j)
          simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂
          rw [e₁, e₂, e])
  obtain ⟨s, t, hs, ht⟩ : ∃ s t : Γ(Z, V), (∀ i : I, resG Z i.2.2.1 s = (a i).val) ∧
      ∀ i : I, resG Z i.2.2.1 t = (a i)⁻¹.val := ⟨s, t, hs, ht⟩
  have hval : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ∃ i : I, ∃ hi : ⊤ ≤ z ⁻¹ᵁ i.1,
      ev z V hz s = ev z i.1 hi (a i).val ∧ ev z V hz t = ev z i.1 hi (a i)⁻¹.val := by
    intro L _ z hz
    obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
    have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
    exact ⟨i, hi', (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz s).symm.trans (congrArg _ (hs i)),
      (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz t).symm.trans (congrArg _ (ht i))⟩
  have hst : s * t = 1 := GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => by
    obtain ⟨i, hi, e₁, e₂⟩ := hval L z hz
    rw [map_mul, map_one, e₁, e₂, ← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, fun L _ z hz => ?_⟩
  obtain ⟨i, hi, e₁, -⟩ := hval L z hz
  show R L z (ev z V hz s)
  rw [e₁]
  exact ha i L z hi

end GlobalTheory.KeyOpen

namespace GlobalTheory.KeyOpen

end GlobalTheory.KeyOpen
