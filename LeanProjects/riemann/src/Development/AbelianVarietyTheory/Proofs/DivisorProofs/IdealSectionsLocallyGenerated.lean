import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem Twist.exists_secs_generating_ideal : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := by
  intro X M hM I hg
  obtain ⟨n, a, ha⟩ := isGloballyGenerated_iff_spanStalks.1 hg
  refine ⟨n, fun k => Twist.secOfTwist (idealModuleι I) (a k), ?_, ?_⟩
  · intro k i W h
    have hW : W.1 ≤ ⊤ ⊓ M.U i := le_inf le_top h
    rw [Twist.secOfTwist_f, LB.resG_resG]
    refine (exists_idealModuleι_app_eq_iff_mem I W _).1
      ⟨Twist.resM _ hW (Twist.coord (a k) i), ?_⟩
    rw [Twist.app_resM]
    exact structureModuleSectionsEquiv_res hW _
  · intro x i hx W hxW f hf
    obtain ⟨t, rfl⟩ := (exists_idealModuleι_app_eq_iff_mem I W f).2 hf
    let l := (structureModuleStalkEquiv x).toLinearMap ∘ₗ stalkLinear (idealModuleι I) x ∘ₗ
      (Twist.stalkEquiv (idealModule I) hM i hx).toLinearMap
    have hm : x ∈ ⊤ ⊓ M.U i := ⟨trivial, hx⟩
    have e : (l ∘ fun k => ((twist (idealModule I) M).presheaf.germ ⊤ x trivial (a k) :
        ((twist (idealModule I) M).presheaf.stalk x :))) =
        fun k => X.presheaf.germ (M.U i) x hx ((Twist.secOfTwist (idealModuleι I) (a k)).f i) := by
      funext k
      rw [Twist.secOfTwist_f, X.presheaf.germ_res_apply (homOfLE _) x hx]
      rw [Function.comp_apply, ← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
      exact congrArg (fun u => structureModuleStalkEquiv x (stalkLinear (idealModuleι I) x u))
        (Twist.stalkEquiv_germ hM i hx (V := ⊤) trivial (a k))
    have hu : X.presheaf.germ W.1 x hxW
        (structureModuleSectionsEquiv W.1 ((idealModuleι I).app W t)) =
        l ((Twist.stalkEquiv (idealModule I) hM i hx).symm
          ((idealModule I).presheaf.germ W.1 x hxW t)) := by
      simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        stalkLinear_germ, structureModuleStalkEquiv_germ]
    have hmem : (Twist.stalkEquiv (idealModule I) hM i hx).symm
        ((idealModule I).presheaf.germ W.1 x hxW t) ∈ Submodule.span (X.presheaf.stalk x)
          (Set.range fun k => ((twist (idealModule I) M).presheaf.germ ⊤ x trivial (a k) :
            ((twist (idealModule I) M).presheaf.stalk x :))) := by
      rw [ha x]; exact Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span l hmem
    rw [← Set.range_comp, e] at h2
    rw [hu]
    exact h2

end GlobalTheory
