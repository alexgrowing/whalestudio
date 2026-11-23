import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TraitGeneric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem eq_of_specializes_of_dim_zero' {X : Scheme.{0}} (q η : X) (hd : ringKrullDim (X.presheaf.stalk q) ≤ 0)
    (h : η ⤳ q) : η = q := by
  have : η ∈ Set.range (X.fromSpecStalk q) := by rw [Scheme.range_fromSpecStalk]; exact h
  obtain ⟨p, rfl⟩ := this
  haveI : Ring.KrullDimLE 0 (X.presheaf.stalk q) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hp : p = IsLocalRing.closedPoint _ :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal p.isPrime.isMaximal')
  rw [hp]; exact Scheme.fromSpecStalk_closedPoint

theorem range_j_subset_abLocus' {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have hw : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  show (Y.jQ ≫ pullback.fst _ _) w ∈ _
  rw [Scheme.Hom.comp_apply]
  exact hw

theorem subsingleton_of_closed_dim_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W],
    CDvr W → ∀ (χ : Sp W ⟶ Z.X) (tW : SAB H (Sp W)) (_ : SABMap tW Z.t χ) (PW : PELUnif (maximalIdeal W) tW),
    Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) ≤ 0 →
    Subsingleton PW.D.toPre.X := by
  intro E _ _ _ H D l Xo c Z W _ _ _ hW χ tW m PW hr hd
  obtain ⟨h₁, h₂, h₃⟩ := hW
  let T : CDVR := { V := W }
  let g : Sp (FractionRing W) := ⟨⊥, Ideal.isPrime_bot⟩
  have hsp : jK W g ⤳ closedPoint W := by
    exact (PrimeSpectrum.le_iff_specializes (R := W) (jK W g) (closedPoint W)).1
      (IsLocalRing.le_maximalIdeal (jK W g).isPrime.ne_top)
  have hsp' : χ (jK W g) ⤳ χ (closedPoint W) := hsp.map χ.continuous
  have he : χ (jK W g) = χ (closedPoint W) := eq_of_specializes_of_dim_zero' _ _ hd hsp'
  have hab : χ (closedPoint W) ∈ abLocus Z.t.G := by
    rw [← he]
    exact range_j_subset_abLocus' Z (hr ⟨g, Scheme.Hom.comp_apply (jK W) χ g⟩)
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus tW.G :=
    (abLocus_pullback abLocusOne Z.t.semi m.cart.1 _).1 hab
  exact (closed_mem_abLocus_iff T PW).1 hc

end GlobalTheory.TraitGeneric
