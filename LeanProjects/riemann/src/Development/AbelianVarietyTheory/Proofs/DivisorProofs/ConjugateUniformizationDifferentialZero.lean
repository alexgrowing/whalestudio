import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjTangent

theorem isDiff_zero_of_isGrpPullback : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (n n' : ℕ) (u : HolUnif A L n)
    (u' : HolUnif A' L' n') (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
    v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff 0 v → u'.IsDiff 0 v' := by
  intro A A' _ _ p g h L L' n n' u u' v v' e hd U hU f
  haveI : IsIso (spMap (g : ℂ →+* ℂ)) :=
    (inferInstance : IsIso (Spec.map (g.toCommRingCatIso).hom))
  haveI : IsIso p := h.1.isIso_fst_of_isIso
  have e2 : v'.left = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv p).2 e
  have h2 : ⊤ ≤ v.left ⁻¹ᵁ (inv p ⁻¹ᵁ U) := by
    refine (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).2 fun q _ => ?_
    have hq := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).1 hU (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    have hs : ∀ a b : PrimeSpectrum (DualNumber ℂ), a = b := fun a b => by
      obtain ⟨a, rfl⟩ := GlobalTheory.TangentOrigin.spMap_fst_surjective a
      obtain ⟨b, rfl⟩ := GlobalTheory.TangentOrigin.spMap_fst_surjective b
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) a b]
    rw [e2] at hq
    change v.left (spMap GlobalTheory.TangentOrigin.fstC q) ∈ inv p ⁻¹ᵁ U
    rw [hs (spMap GlobalTheory.TangentOrigin.fstC q)
      (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) (spMap GlobalTheory.TangentOrigin.fstC q))]
    exact hq
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p →
      TangentOrigin.evalPt y U hy f = Chart.dualMapR (g : ℂ →+* ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) v.left _ h2 (((inv p).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv p).app U).hom f)
  rw [map_zero] at e3 ⊢
  simp only [Chart.dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact (congrArg (g : ℂ →+* ℂ) e3).trans (map_zero _)

end GlobalTheory.ConjTangent
