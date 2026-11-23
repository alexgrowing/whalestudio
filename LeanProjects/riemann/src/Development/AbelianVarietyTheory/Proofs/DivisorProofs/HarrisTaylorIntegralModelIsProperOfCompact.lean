import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

lemma specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem isProper_model_of_compact (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R]
    [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (M : Model b N)
    (hc : 2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) : IsProper M.s := by
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  refine GlobalTheory.T.isProper_of_lift_completeDvr_charZero R M.X M.s M.qproj inferInstance ?_
  intro V K _ _ _ _ _ _ _ _ β x hx

  obtain ⟨oK, ⟨hK⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp K) M.s x M.univ
  generalize hs : x ≫ M.s = s₀ at oK hK
  obtain rfl : s₀ = spMap ((algebraMap V K).comp β) := hs.symm.trans hx

  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomp, _, hloc, _, G, _, hmod, hab⟩ :=
    GlobalTheory.T.harrisTaylorModuliObject_potentiallyGoodReduction p D R b N V K ((algebraMap V K).comp β) oK hc

  obtain ⟨oL, ⟨hL⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N (Sp K) (Sp L) (spMap ((algebraMap V K).comp β))
    (spMap (algebraMap K L)) oK
  have hLs : spMap (algebraMap K L) ≫ spMap ((algebraMap V K).comp β) =
      spMap ((algebraMap W L).comp ((algebraMap V W).comp β)) := by
    rw [specMap_contravariant_comp_ringHom, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hcomp]
  generalize hs' : spMap (algebraMap K L) ≫ spMap ((algebraMap V K).comp β) = s₁ at oL hL
  obtain rfl : s₁ = spMap ((algebraMap W L).comp ((algebraMap V W).comp β)) := hs'.symm.trans hLs
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L oK.A G hmod oL.A hL.φ hL.cart
  obtain ⟨oW, ⟨hW⟩⟩ := GlobalTheory.T.harrisTaylorObject_extends_over_dvr_of_abelianModel p D R b N W L ((algebraMap V W).comp β) oL G φ hab hφ
  obtain ⟨f, ⟨hfs, ⟨hf⟩⟩, -⟩ := M.rep (Sp W) _ oW
  obtain ⟨h₁⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ oL oW M.univ _ _ hW hf
  obtain ⟨h₂⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ oL oK M.univ _ _ hL hK
  obtain ⟨g, -, hg⟩ := M.rep (Sp L) _ oL
  have e₁ : spMap (algebraMap W L) ≫ f = g := hg _ ⟨by rw [Category.assoc, hfs, specMap_contravariant_comp_ringHom], ⟨h₁⟩⟩
  have e₂ : spMap (algebraMap K L) ≫ x = g := hg _ ⟨by rw [Category.assoc, hx, hLs], ⟨h₂⟩⟩
  exact ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcomp, hloc, f, e₂.trans e₁.symm⟩

end GlobalTheory.UPel.HT
