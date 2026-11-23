import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace ModelDimension

open GlobalTheory.FlatLine GlobalTheory.CompHS in

theorem evR_eq_of_sec₀_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) {e : Ix Dw → ℤ}
    (f g : secZ Xo c e) (h : sec₀ X Z e f = sec₀ X Z e g) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (hy : LiesOn Z y) : evR Xo c f.1 y = evR Xo c g.1 y := by
  by_cases ht : Tested y
  swap
  · unfold evR evalAt
    rw [dif_neg ht, dif_neg ht]
  have key : ∀ a : Rul Xo c, evR Xo c (idem Z * a) y = evR Xo c a y := fun a => by
    have e : evR Xo c (idem Z * a) y = evR Xo c (idem Z) y * evR Xo c a y :=
      evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) a y
    rw [e, evR_idem hy ht, one_mul]
  have hm := idem_mul_mem Z (f - g).2
  have h0 : sec₀ X Z e ⟨_, hm.1⟩ = 0 := by
    rw [sec₀_mul X Z (zero_add e) ⟨idem Z, idem_mem_secZ Z⟩ (f - g) ⟨_, hm.1⟩ rfl, map_sub (sec₀ X Z e), h,
      sub_self, map_zero]
  have h1 : idem Z * (f.1 - g.1) = 0 := congrArg Subtype.val (eq_zero_of_sec₀ X Z (f := ⟨_, hm.1⟩) hm.2 h0)
  rw [mul_sub, sub_eq_zero] at h1
  rw [← key f.1, h1, key]

theorem cusp_form_extension_vanishing : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ TF.X (exOf (T.Q.Dw j) u 0), ∃ g ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ w ∈ framesOn (Y.U σ) Z, rdU (Y.U σ) f w.1 w.2 = rdU (Y.U σ) g w.1 w.2 := by
  intro D T j Y e o hG hf Z TF u f hfv
  have hfs := GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ_le_secZ TF.X _ hfv
  obtain ⟨s, hs, hsf⟩ := GlobalTheory.CompanionTheory.Ar.OntoDef.exists_vanBd_of_mem_extVanZ (X := TF.X) (la := u) (f := ⟨f, hfs⟩) hfv Z
  obtain ⟨g, hg⟩ := GlobalTheory.HSApp.vanBd_le_space D T j Y e o hG hf Z TF u hs
  refine ⟨g.1, g.2, fun σ _ w hw => ?_⟩
  obtain ⟨k, y⟩ := w
  obtain ⟨hd, hl⟩ := hw
  have h := evR_eq_of_sec₀_eq TF.X Z ⟨f, hfs⟩ ⟨g.1, GlobalTheory.CompHS.cusp_le_secZ Z Y.U u g.2⟩ (hsf.symm.trans hg.symm) _ hl
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hd]
  exact congrArg _ h

end ModelDimension
