import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleRelativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrictStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PullbackCompositionCompatible
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorOfForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrictStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogResStep

open GlobalTheory.Cartier.CartierDiv in

theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (m : ℕ) : (m • D).supp ≤ D.supp := by
  induction m with
  | zero => simp [(CartierDiv.supp_eq_bot_iff (D := (0 : CartierDiv X))).2 rfl]
  | succ m ih => exact (succ_nsmul D m ▸ CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

theorem sup_ne_top {Y : Scheme.{0}} [IsIntegral Y] {Z W : Closeds Y} (hZ : Z ≠ ⊤) (hW : W ≠ ⊤) : Z ⊔ W ≠ ⊤ := by
  have key : ∀ C : Closeds Y, C ≠ ⊤ → genericPoint Y ∉ C := fun C hC h => hC <| by
    ext x; simp only [Closeds.coe_top, Set.mem_univ, iff_true]
    exact ((genericPoint_spec Y).mem_closed_set_iff C.isClosed).1 h (Set.mem_univ x)
  intro h
  have : genericPoint Y ∈ Z ⊔ W := by rw [h]; trivial
  rcases this with h' | h'
  · exact key Z hZ h'
  · exact key W hW h'

end GlobalTheory.LogResStep

open GlobalTheory.LogResStep in
theorem GlobalTheory.exists_logRes_ample : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ (Y₀ : Scheme.{0}) [IsIntegral Y₀] (s₀ : Y₀ ⟶ X) [IsDominant s₀], SmoothOfRelativeDimension n (s₀ ≫ p) → IsProjOver (s₀ ≫ p) → Function.Bijective (functionFieldMap s₀) → ∀ (Z : Closeds Y₀), Z ≠ ⊤ → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (t : Y ⟶ Y₀) (_ : IsDominant t) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G (t ≫ s₀) K B ∧ (∀ y, t y ∈ Z → y ∈ B) ∧ ∃ (c : ℕ) (E : CartierDiv Y) (A₁ : LB Y) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ B ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro hP k _ _ X _ p n η m G hη Y₀ _ s₀ _ hsm hproj hbij Z hZ A hA
  haveI : SmoothOfRelativeDimension n (s₀ ≫ p) := hsm
  haveI : Smooth (s₀ ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ p)

  set η₀ := EtaleKlt.ratPull p s₀ n η with hη₀def
  have hη₀ : η₀ ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y₀ p s₀ hbij n).1 (h.trans (map_zero _).symm))
  obtain ⟨K₀, hK₀⟩ := (GlobalTheory.T.canonical_divisor_of_form k Y₀ (s₀ ≫ p) n η₀ hη₀).1

  set D₀ : CartierDiv Y₀ := pullCart s₀ G - m • K₀ with hD₀
  set Z' : Closeds Y₀ := Z ⊔ D₀.supp with hZ'
  have hZ'top : Z' ≠ ⊤ := sup_ne_top hZ D₀.supp_ne_top
  set I : Y₀.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z' with hIdef
  have hIsupp : (I.support : Set Y₀) = Z' := Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
  have hI : I ≠ ⊥ := by
    intro h
    apply hZ'top
    ext x
    rw [← hIsupp, h]
    simp
  obtain ⟨Y, t, hYi, hsmY, hprojY, -, hiso, heff, hsnc⟩ := hP k n Y₀ (s₀ ≫ p) inferInstance hsm hproj I hI
  haveI := hYi
  have hne := Principalise.nonempty_compl_support hI
  haveI : IsDominant t := GlobalTheory.T.isDominant_of_isIso_restrict' Y₀ Y t I.support.compl hne hiso
  haveI : SmoothOfRelativeDimension n (t ≫ s₀ ≫ p) := hsmY
  haveI : SmoothOfRelativeDimension n ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hsmY
  haveI : Smooth (t ≫ s₀ ≫ p) := SmoothOfRelativeDimension.smooth n _
  have hsmY' : SmoothOfRelativeDimension n ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hsmY
  have hprojY' : IsProjOver ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hprojY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (t ≫ s₀ ≫ p)
  have hcomp := GlobalTheory.T.pullback_composition_compatible k X Y₀ Y p s₀ t
  have hbt := GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' Y₀ Y t I.support.compl hne hiso
  have hbij' : Function.Bijective (functionFieldMap (t ≫ s₀)) := by
    rw [hcomp.1, RingHom.coe_comp]; exact hbt.comp hbij
  have hη₁ : EtaleKlt.ratPull p (t ≫ s₀) n η ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p (t ≫ s₀) hbij' n).1 (h.trans (map_zero _).symm))
  obtain ⟨K, hK⟩ := (GlobalTheory.T.canonical_divisor_of_form k Y ((t ≫ s₀) ≫ p) n _ hη₁).1
  have hK' : IsDivOfForm K (EtaleKlt.ratPull (s₀ ≫ p) t n η₀) := ((hcomp.2.2 n η K).1 hK)

  have hB : ∀ y : Y, y ∈ (I.comap t).support ↔ t y ∈ Z' := fun y => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]
    change t y ∈ (I.support : Set Y₀) ↔ _
    rw [hIsupp]; rfl
  have hkiso := GlobalTheory.T.canonical_divisor_birational_compare k Y₀ Y (s₀ ≫ p) n t I.support.compl hne hiso η₀ hη₀ K₀ K hK₀ hK'
  have heq : pullCart (t ≫ s₀) G - m • K = pullCart t D₀ + m • (-(K - pullCart t K₀)) := by
    rw [hcomp.2.1 G, hD₀]
    change _ = pullCartHom t (pullCart s₀ G - m • K₀) + _
    rw [map_sub, map_nsmul]
    change _ = pullCart t (pullCart s₀ G) - m • pullCart t K₀ + _
    rw [smul_neg, nsmul_sub]; abel
  refine ⟨Y, hYi, t, inferInstance, K, (I.comap t).support,
    ⟨hsmY', hprojY', hbij', hK, hsnc, ?_⟩, ?_, ?_⟩
  · rw [heq]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ?_ ?_)
    · intro y hy
      rw [hB]
      exact Or.inr ((GlobalTheory.T.cartierDivisorPullback_support_and_effective Y₀ Y t D₀).1 y hy)
    · intro y hy
      have hy' := supp_neg_le _ (supp_nsmul_le _ m hy)
      rw [hB]
      by_contra hc
      refine hkiso y ?_ hy'
      intro hm
      have : t y ∈ (I.support : Set Y₀) := hm
      rw [hIsupp] at this; exact hc this
  · intro y hy; rw [hB]; exact Or.inl hy
  · exact GlobalTheory.T.blowup_ample_relative k Y₀ Y (s₀ ≫ p) n t hproj hprojY I hiso heff A hA
