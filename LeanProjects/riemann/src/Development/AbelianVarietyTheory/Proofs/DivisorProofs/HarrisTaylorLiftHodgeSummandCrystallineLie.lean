import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

namespace GlobalTheory.HTLiftLie

theorem lie_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) m.cart → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) m.cart) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) m.cart := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m hs _ d hd
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have bij : Function.Bijective (crysToDR (divided₂ hsq) m.cart) :=
    GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective GlobalTheory.abelianDeRham.2.2.2.1 o.ab hg (isDPNilpotent_squareZero hsq) hπ rfl
      m.cart
  have key : ∀ (c : D.O) (x : Crys (divided₂ hsq) (spMap π) o₀.A),
      crysToDR (divided₂ hsq) m.cart (haveI := o₀.act.hom c; push (divided₂ hsq) (spMap π) (o₀.act.act c) x) =
        GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act c (crysToDR (divided₂ hsq) m.cart x) := by
    intro c x
    haveI := o₀.act.hom c
    haveI := o.act.hom c
    rw [GlobalTheory.HTSummand.crysAct_apply]
    exact crysToDR_push (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm x
  have hy : GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) (crysToDR (divided₂ hsq) m.cart d) -
      tR b.ρ • crysToDR (divided₂ hsq) m.cart d ∈ Fil o.A := by
    have h' := hd
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, key] at h'
    exact h'
  obtain ⟨w', hw', hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C tR s hs o _ hy
  choose w hw using fun i => bij.2 (w' i)
  refine ⟨w, fun i c => ?_, ?_⟩
  · rw [liftFil, Submodule.mem_comap, map_sub, map_smul, key, hw i]
    exact hw' i c
  · rw [liftFil, Submodule.mem_comap, map_sub, map_sum]
    simp only [hw]
    exact hsum

end GlobalTheory.HTLiftLie
