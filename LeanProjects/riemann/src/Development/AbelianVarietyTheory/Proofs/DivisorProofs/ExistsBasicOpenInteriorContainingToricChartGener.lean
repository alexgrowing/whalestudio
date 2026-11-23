import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem exists_basicOpen_chartHom_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U W : Y.X.affineOpens), W.1 = U.1 ⊓ interior Y → ∀ (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∃ h : Γ(Y.X, U.1), Y.X.basicOpen h ≤ W.1 ∧ GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y U W hW k _ m d ξ hx hbd
  let gp : Sp (ChartRing k m d) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (ChartRing k m d))
  have hprod : (∏ i, bdParam k m d i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ hX => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) hX
      simp at this
  have hgbd : ξ gp ∉ genBd Y := by
    rw [hbd]
    exact fun h => hprod ((Submodule.mem_bot _).1 h)
  have hgab : genι Y (ξ gp) ∈ interior Y := by
    have := (mem_genBd_iff (Y := Y) (x := ξ gp)).not.1 hgbd
    rw [not_not, ← coe_interior] at this
    exact this
  have hsp : gp ⤳ closedPoint (ChartRing k m d) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (fun x hx => by
      rw [(Submodule.mem_bot _).1 hx]; exact Ideal.zero_mem _)
  have hgU : ξ gp ∈ genι Y ⁻¹ᵁ U.1 :=
    (hsp.map ξ.continuous).mem_open (genι Y ⁻¹ᵁ U.1).isOpen hx
  have hyW : genι Y (ξ gp) ∈ W.1 := by
    rw [hW]; exact ⟨hgU, hgab⟩
  obtain ⟨h, hle, hmem⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨_, hyW⟩ hgU
  refine ⟨h, hle, fun h0 => ?_⟩
  have hg0 : gp ∈ ξ ⁻¹ᵁ (gen Y).basicOpen (((genι Y).app U.1).hom h) := by
    show ξ gp ∈ (gen Y).basicOpen _
    rw [← Scheme.preimage_basicOpen]; exact hmem
  rw [Scheme.preimage_basicOpen] at hg0
  have e := congrArg (fun q => q.hom (((genι Y).app U.1).hom h)) (Scheme.germ_stalkClosedPointTo ξ _ hx)
  simp only [chartHom, RingHom.comp_apply] at h0
  change (Scheme.stalkClosedPointTo ξ).hom (((gen Y).presheaf.germ _ _ hx).hom _) = 0 at h0
  rw [← CommRingCat.comp_apply] at h0
  rw [e] at h0
  have h1 := h0
  rw [CommRingCat.comp_apply] at h1
  have hz : (ξ.app (genι Y ⁻¹ᵁ U.1)).hom (((genι Y).app U.1).hom h) = 0 :=
    (ConcreteCategory.bijective_of_isIso _).1 (h1.trans (map_zero _).symm)
  rw [hz, Scheme.basicOpen_zero] at hg0
  exact hg0

end GlobalTheory.LocReg
