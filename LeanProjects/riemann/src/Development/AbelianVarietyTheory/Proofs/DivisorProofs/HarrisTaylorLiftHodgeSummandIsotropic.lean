import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrysForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual

namespace GlobalTheory.HTLiftIso

theorem liftFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _ φ hφ x hx y hy
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl o.ab hg o.ab hg m.cart m.cart
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have CD := cupSquare_of_free ADR.1 hAB (smooth_prod hg hg)
  obtain ⟨φd, hφd⟩ := exists_isCorrForm CD o.isLB o.rig₁ o.rig₂
  obtain ⟨φ₀, hφ₀, e₀⟩ := GlobalTheory.Published.AbelianDualCrystal.exists_crystal_pairing κ m.cart m.cart m.sq.1 m.sq.2
    o.isLB o₀.isLB (LBIso.symm m.pol) hφd
  obtain rfl := hφ.unique CS o₀.isLB hφ₀
  rw [e₀]
  obtain ⟨ψ, hψ, eψ⟩ := hφd.isPolForm
  have iso := (ADR.2.2.2.2 C _ _ hAB (smooth_prod hg hg) o.P o.isLB ψ hψ).1
  have hx' : crysToDR κ m.cart x ∈ Fil o.A := hx
  have hy' : crysToDR κ m.cart y ∈ Fil o.A := hy
  have h := iso _ (push_mem_Fil (inl o.A o.A) hx') _ (push_mem_Fil (inr o.A o.A) hy')
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_push _ _ _ (lift_snd _ _)] at h
  simpa [push_id, push_one] using h

end GlobalTheory.HTLiftIso
