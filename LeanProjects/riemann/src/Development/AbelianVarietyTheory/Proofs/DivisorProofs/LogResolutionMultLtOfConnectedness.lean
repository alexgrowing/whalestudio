import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftedFunctionOnLogResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtNormalPointOfDivisorsStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLiftStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DiscrepancyFormulaDivisor
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.LogResConn

theorem mult_le_ord_of_regularAt {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {F : CartierDiv Y} {v : Y} {f : Y.functionField} (h : (-F).RegularAt v f) (hf : f ≠ 0)
    (hv : Order.coheight v = 1) : F.mult v ≤ Scheme.ord f v := by
  obtain ⟨g, hg⟩ := F.exists_isEqn v
  obtain ⟨a, ha⟩ := hg.neg.regularAt_iff.1 h
  have hg0 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hf hg0 ha.symm
  have h2 := ord_algebraMap hv ha0
  rw [ha, Scheme.ord_mul hf hg0] at h2
  have h3 := Scheme.ord_mul (x := v) (Units.ne_zero g) hg0
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, (unitAt_one v).ord_eq_zero] at h3
  rw [hg.mult_eq]
  have : (0 : ℤ) ≤ ((Module.length (Y.presheaf.stalk v) (Y.presheaf.stalk v ⧸ Ideal.span {a})).toNat : ℤ) :=
    Int.natCast_nonneg _
  omega

theorem mem_ring_of_regularAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {E : DivOver q} {F : CartierDiv Y} {w : Y}
    {f : Y.functionField} (hE : E.IsAt w) (h : (-F).RegularAt w f) (hF : 0 ≤ F.mult w) :
    f ∈ E.ring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  have h1 := mult_le_ord_of_regularAt h hf hE.coheight_eq_one
  have h2 := hE.ord_eq (Units.mk0 f hf)
  have h3 := (E.ord_nonneg_iff (Units.mk0 f hf)).1 (by rw [h2]; simpa using hF.trans h1)
  simpa using h3

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]

theorem regAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : RegAt y f) : RegAt v (functionFieldMap s f) := by
  obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k X Y p s hbir E'
  have ht := GlobalTheory.T.primeDivisorCentre_through_image k X Y p s E' E hE v (hE'.through specializes_rfl)
  exact (hE' _).1 ((hE f).1 ((ht.of_specializes hsv) f hf))

theorem unitAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : UnitAt y f) : UnitAt v (functionFieldMap s f) := by
  have hf0 := hf.ne_zero
  obtain ⟨h1, h2⟩ := (unitAt_iff hf0).1 hf
  refine (unitAt_iff ((map_ne_zero _).2 hf0)).2 ⟨regAt_pull (p := p) s hbir hv hsv h1, ?_⟩
  rw [← map_inv₀]
  exact regAt_pull (p := p) s hbir hv hsv h2

end GlobalTheory.LogResConn

namespace GlobalTheory.LogResConn

theorem mult_lt_of_connected : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro X _ _ p n hp hn η m G N Y _ _ s _ K B F hη hm hres hF hcoh y σ hyint hdisc hσ hsσ hnear
    v hvσ hsv
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hFσ : F.mult σ = 1 := by rw [hF, hσ]; exact Int.ediv_self hm'.ne'
  have hFle : ∀ z, F.mult z ≤ 0 ↔ (pullCart s G - m • K).mult z < m := fun z => by
    rw [hF, ← Int.lt_add_one_iff, zero_add, Int.ediv_lt_iff_lt_mul hm', one_mul]
  have hFnn : ∀ z, 0 ≤ (pullCart s G - m • K).mult z → 0 ≤ F.mult z := fun z hz => by
    rw [hF]; exact Int.ediv_nonneg hz hm'.le
  by_cases hvc : Order.coheight v ≠ 1
  · have : (pullCart s G - m • K).mult v = 0 := by
      by_contra h0
      exact hvc (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    rw [this]; exact hm'
  push_neg at hvc
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper (s ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB (s ≫ p)).1 hres.proj).1
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  haveI : IsProper s := IsProper.of_comp s p
  have hbir := hres.bir
  have hσc : Order.coheight σ = 1 :=
    CartierDiv.coheight_eq_one_of_mult_ne_zero (by rw [hσ]; exact_mod_cast hm.ne')
  obtain ⟨h, hσreg, hreg⟩ := GlobalTheory.T.exists_lifted_function_on_logResolution X p n hp hn η m G N Y s K B F hres hcoh y σ
    (fun v w h1 h2 h3 h4 => (hFle v).2 (hnear v w h1 h2 h3 h4)) hsσ hσc
  obtain ⟨h₀, rfl⟩ := hbir.2 h

  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1 (h0.trans (map_zero _).symm))

  have hDnn : ∀ (z : X), z ⤳ y → ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), E.IsAt z →
      DivOver.Over s E' E → ∀ w, s w = z → E'.IsAt w → 0 ≤ F.mult w := by
    intro z hz E E' hE hE'E w hwz hw
    subst hwz
    obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
    have hd := hdisc (s w) hz E hE g hg
    have h1 := GlobalTheory.T.discrepancy_formula_divisor ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m hm
      hres.div E' w (fnPull s g) hw (isEqn_pullCart s hg)
    have h2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
      unfold discrep
      rw [GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hbir E' E hE'E n η hη, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hbir E' E hE'E g]
    rw [h2] at h1
    rw [h1] at hd
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) := by
      rw [neg_div, neg_nonpos] at hd
      exact (div_nonneg_iff.1 hd).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hmq))
    exact hFnn w (by exact_mod_cast this)

  have hreg0 : RegAt y h₀ := by
    refine GlobalTheory.T.regular_at_normal_point_of_divisors X p hp y hyint h₀ fun z hz E hE => ?_
    obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hbir E
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.divisor_point_proper_lift ℂ X Y p s hbir inferInstance E' E hE'E z hE
    have hFw := hDnn z hz E E' hE hE'E w hwz hw
    have hsw : s w ⤳ y := hwz ▸ hz
    rw [hE'E h₀]
    by_cases hwσ : w = σ
    · subst hwσ
      have := mem_ring_of_regularAt hw hσreg hFw
      simpa using add_mem this (one_mem E'.ring)
    · exact mem_ring_of_regularAt hw (hreg w hwσ hw.coheight_eq_one hsw) hFw

  have hunit0 : UnitAt y h₀ := by
    by_cases hh1 : functionFieldMap s h₀ - 1 = 0
    · have : h₀ = 1 := hbir.1 (by rw [map_one]; exact sub_eq_zero.1 hh1)
      rw [this]; exact unitAt_one y
    have hnu : ¬ UnitAt y (h₀ - 1) := fun hu => by
      have hu' := unitAt_pull (p := p) s hbir hσc hsσ hu
      rw [map_sub, map_one] at hu'
      have := mult_le_ord_of_regularAt hσreg hh1 hσc
      rw [hu'.ord_eq_zero, hFσ] at this
      omega
    obtain ⟨a, ha, e⟩ := zeroAt_iff.2 ⟨hreg0.add ⟨-1, by rw [map_neg, map_one]⟩, by
      rwa [sub_eq_add_neg] at hnu⟩
    have h1a : (1 + a) ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := fun h' => by
      have h1 : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        simpa using sub_mem h' ha
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    exact ⟨1 + a, IsLocalRing.notMem_maximalIdeal.1 h1a, by rw [map_add, map_one, e]; ring⟩
  have hu := unitAt_pull (p := p) s hbir hvc hsv hunit0
  have := mult_le_ord_of_regularAt (hreg v hvσ hvc hsv) hu.ne_zero hvc
  rw [hu.ord_eq_zero] at this
  exact (hFle v).1 this

end GlobalTheory.LogResConn
