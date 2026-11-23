import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAndMultiplicityPullbackIsIsoOpenStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalFormStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy.CanonIso

theorem isNormalScheme_of_smooth' {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem ring_ne_top' {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : E.ring ≠ ⊤ := fun h =>
  IsDiscreteValuationRing.not_isField E.ring (by
    rw [h]
    exact MulEquiv.isField (Field.toIsField X.functionField) Subring.topEquiv.toMulEquiv)

theorem isAt_of_through' {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {z : X} {E F : DivOver p} (hF : F.IsAt z) (hE : E.Through z) : E.IsAt z := by
  have hle : F.ring ≤ E.ring := fun f hf => hE f ((hF f).1 hf)
  have := ValuationSubring.eq_of_le_of_ne_top F.ring hle (ring_ne_top' E)
  exact fun f => this ▸ hF f

theorem not_mem_supp_sub_pullCart : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)] (U : Y₀.Opens), (U : Set Y₀).Nonempty → IsIso (t ∣_ U) → ∀ (η : RatForms q n), η ≠ 0 → ∀ (K₀ : CartierDiv Y₀) (K₁ : CartierDiv Y₁), IsDivOfForm K₀ η → IsDivOfForm K₁ (EtaleKlt.ratPull q t n η) → ∀ y : Y₁, t y ∈ U → y ∉ (K₁ - pullCart t K₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ U hU hiso η hη K₀ K₁ h₀ h₁ y hy
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)
  haveI : GlobalTheory.IsNormalScheme Y₀ := isNormalScheme_of_smooth' q
  haveI : GlobalTheory.IsNormalScheme Y₁ := isNormalScheme_of_smooth' (t ≫ q)
  have hbir := GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' Y₀ Y₁ t U hU hiso
  have hpull : EtaleKlt.ratPull q t n η ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k Y₀ Y₁ q t hbir n).1 (h.trans (map_zero _).symm))
  rw [(GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (K₁ - pullCart t K₀)).2.1 y]
  rintro ⟨z, hzy, hz⟩
  apply hz
  have htz : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  obtain ⟨hc, hm⟩ := GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hiso z htz
  have hsub : (K₁ - pullCart t K₀).mult z = K₁.mult z - (pullCart t K₀).mult z := by
    have := CartierDiv.mult_add (K₁ - pullCart t K₀) (pullCart t K₀) z
    rw [sub_add_cancel] at this
    omega
  rw [hsub, hm K₀, sub_eq_zero]
  by_cases h1 : Order.coheight z = 1
  · obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := t ≫ q) h1
    obtain ⟨E, hO⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k Y₀ Y₁ q t hbir E'
    obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) (z := t z) (hc ▸ h1)
    have hthr : E.Through (t z) := by
      intro f hf
      obtain ⟨a, rfl⟩ := hf
      exact (hO _).2 ((hE' _).2 ⟨t.stalkMap z a, (GlobalTheory.functionFieldMap_algebraMap t z a).symm⟩)
    have hE : E.IsAt (t z) := isAt_of_through' hF hthr
    rw [← GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y₁ (t ≫ q) n _ hpull K₁ h₁ E' z hE',
      ← GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y₀ q n η hη K₀ h₀ E (t z) hE]
    exact GlobalTheory.T.form_order_birational_pullback k Y₀ Y₁ q t hbir E' E hO n η hη
  · have a : K₁.mult z = 0 := by_contra fun h => h1 (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    have b : K₀.mult (t z) = 0 :=
      by_contra fun h => h1 (hc ▸ CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    rw [a, b]

end GlobalTheory.Discrepancy.CanonIso
