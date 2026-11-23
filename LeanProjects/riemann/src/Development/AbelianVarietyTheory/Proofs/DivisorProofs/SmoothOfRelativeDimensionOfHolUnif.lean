import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusAction

theorem smoothOfRelativeDimension_of_holUnif (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    {g : ℕ} (u : HolUnif A L g) : SmoothOfRelativeDimension g A.hom := by
  haveI := hA.comm
  haveI := hA.proper
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ A hA
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  obtain ⟨u₀⟩ := RealMultChart.exists_holUnif_of_compact A d hd (RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => RealMultChart.exists_pow_eq A hA a n hn)
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u₀ hd
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ d g u₀ h₁ h₂
    u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  rw [Obj.holUnif_dim_eq_of_linear u u₀ T hT]
  exact hd

open GlobalTheory.ComplexPoints in

theorem exists_oAct_of_map_lattice :
    ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (u : HolUnif A L g) (O : Type) [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)),
    (∀ a, ∀ z ∈ u.Λ, ρ a z ∈ u.Λ) → ∃ act : OAct O A, ∀ a z, u.ex (ρ a z) = u.ex z ≫ act.act a := by
  intro g A _ hA L u O _ ρ hρ
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  haveI : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hA.smooth
  choose ψ hhom hlift using fun a => GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA
    (smoothOfRelativeDimension_of_holUnif A hA u) L u (ρ a) (hρ a)
  have hext : ∀ f f' : A ⟶ A, (∀ z, u.ex z ≫ f = u.ex z ≫ f') → f = f' := fun f f' h =>
    over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u.ex_onto x
      exact h z
  refine ⟨⟨ψ, hhom, ?_, ?_, ?_⟩, hlift⟩
  · refine hext _ _ fun z => ?_
    rw [← hlift, map_one, Module.End.one_apply, Category.comp_id]
  · intro a b
    refine hext _ _ fun z => ?_
    rw [← hlift, ← Category.assoc, ← hlift, ← hlift, mul_comm, map_mul, Module.End.mul_apply]
  · intro a b
    refine hext _ _ fun z => ?_
    rw [← hlift, comp_mul, ← hlift, ← hlift, map_add, LinearMap.add_apply, u.ex_add]

end GlobalTheory.TorusAction
