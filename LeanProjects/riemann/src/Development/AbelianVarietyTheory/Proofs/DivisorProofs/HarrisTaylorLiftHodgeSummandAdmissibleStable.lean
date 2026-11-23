import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform

open GlobalTheory.Published.GrothendieckMessing in

theorem liftFil_isCompl_red_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _
  have HC := canonical_of_abelianDeRham GlobalTheory.T.abelianScheme_firstDeRham_structure (isDPNilpotent_squareZero hsq) hπ rfl
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  obtain ⟨bij, ⟨M, hM⟩, hAdm⟩ := HC g o₀.A o.A m.φ m.cart o.ab hg
  have bijD := HC.crysToDR_bijective m.cart o.ab hg
  let e := LinearEquiv.ofBijective (crysToDR (divided₂ hsq) m.cart) bijD
  refine ⟨⟨M.comap (crysToDR (divided₂ hsq) m.cart), (Submodule.orderIsoMapComap e).symm.isCompl hM⟩,
    fun y ↦ ?_, fun c d hd ↦ ?_⟩
  · rw [hAdm y]
    constructor
    · rintro ⟨x, hx, ex⟩
      obtain ⟨d, rfl⟩ := bijD.2 x
      exact ⟨d, hx, (corr_crysToDR_iff rfl m.cart bij.2 d y).1 ex⟩
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, hd, (corr_crysToDR_iff rfl m.cart bij.2 d y).2 ed⟩
  · haveI := o₀.act.hom c
    haveI := o.act.hom c
    exact push_mem_liftFil (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm hd

end GlobalTheory.HTDeform
