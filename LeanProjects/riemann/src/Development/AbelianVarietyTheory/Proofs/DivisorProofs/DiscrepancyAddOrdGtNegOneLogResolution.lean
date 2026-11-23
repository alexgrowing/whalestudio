import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorCenterProperLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.CoeffPlaces

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem supp_neg_le' (D : CartierDiv Z) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le' (D : CartierDiv Z) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

variable [IsLocallyNoetherian Z]

theorem mult_zero'' (z : Z) : (0 : CartierDiv Z).mult z = 0 := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv Z) 0 z
  rw [add_zero] at h₀
  omega

theorem mult_nsmul''' (E : CartierDiv Z) (r : ℕ) (z : Z) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero => rw [zero_nsmul, mult_zero'']; simp
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem mult_sub'' (D E : CartierDiv Z) (z : Z) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  omega

theorem ord_nonneg_of_regAt' {f : Z.functionField} {z : Z} (hf : RegAt z f) (h0 : f ≠ 0) :
    0 ≤ Scheme.ord f z := by
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, rfl⟩ := hf
    have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
    rw [ord_algebraMap hz ha]
    exact Nat.cast_nonneg _
  · exact (Scheme.ord_eq_zero_of_coheight_neq_one hz _).ge

theorem regAt_functionFieldMap' {X : Scheme.{0}} [IsIntegral X] (q : Z ⟶ X) [IsDominant q] (y : Z)
    {f : X.functionField} (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

end GlobalTheory.Discrepancy.CoeffPlaces

open GlobalTheory.Discrepancy.CoeffPlaces in

theorem GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  intro X _ _ p n hproj _ η m g f Y _ _ s _ K B y σ hη hm hres hfB hfy hσ1 hσm hlt E hE
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hres.bir E
  obtain ⟨y', rfl, hE'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p s hres.bir inferInstance E' E hE'E _ hE
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  set F := pullCart s (CartierDiv.principal f) with hFdef
  set G := pullCart s (CartierDiv.principal g) with hGdef
  have hFsupp : F.supp ≤ B := fun v hv => hfB v ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y s _).1 v hv)
  have e : G - m • F - m • K = (G - m • K) + -(m • F) := by abel
  have hsupp : (G - m • F - m • K).supp ≤ B := by
    rw [e]
    exact (CartierDiv.supp_add_le _ _).trans
      (sup_le hres.supp ((supp_neg_le' _).trans ((supp_nsmul_le' _ _).trans hFsupp)))
  have hFm (w : Y) : F.mult w = Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal f (s w))).mult_eq
  have hEqn : (G - m • F).IsEqn y' (fnPull s g / fnPull s f ^ m) :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal g (s y'))).sub
      ((isEqn_pullCart s (CartierDiv.isEqn_principal f (s y'))).nsmul m)
  have hmul (w : Y) : (G - m • F - m • K).mult w = (G - m • K).mult w - m * F.mult w := by
    rw [mult_sub'', mult_sub'', mult_sub'', mult_nsmul''', mult_nsmul''']; ring
  have hlt' : ∀ w, w ⤳ y' → (G - m • F - m • K).mult w < m := by
    intro w hw
    rw [hmul, hFm]
    by_cases hwσ : w = σ
    · subst hwσ
      rw [hσm, hσ1]
      simp only [mul_one, sub_self]
      exact_mod_cast hm
    · have hsw : s w ⤳ s y' := hw.map s.continuous
      have h0 : 0 ≤ Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        ord_nonneg_of_regAt' (regAt_functionFieldMap' s w (regAt_of_specializes hsw hfy))
          (Units.ne_zero _)
      have h1 := hlt w hwσ hsw
      have h2 : (0 : ℤ) ≤ m * Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        mul_nonneg (Int.natCast_nonneg m) h0
      linarith
  have hcrit := (GlobalTheory.T.klt_of_snc_coefficients ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (G - m • F) m B hm
    hres.div hres.snc hsupp y' _ hEqn E' hE').1 hlt'
  have hd : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g / fnPull s f ^ m) =
      discrep E η m g + E.ord f := by
    simp only [discrep]
    rw [GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hres.bir E' E hE'E n η hη, div_eq_mul_inv (fnPull s g), E'.ord_mul, E'.ord_inv,
      E'.ord_pow, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E g,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E f]
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring
  rw [← hd]
  exact hcrit
