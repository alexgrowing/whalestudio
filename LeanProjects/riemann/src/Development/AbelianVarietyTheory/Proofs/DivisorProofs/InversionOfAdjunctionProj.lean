import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessLemmaAtNormalPointLogResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResidueDominantCartierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyAddOrdGtNegOneLogResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderBirationalPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory

theorem inversion_of_adjunction_proj : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g f : X.functionFieldˣ) (y : X) (S : DivOver p), TrBasis (Cartier.constFn p) x → 0 < m → IsIntegrallyClosed (X.presheaf.stalk y) → RegAt y (f : X.functionField) → (placeEquiv p S).IsPrimeOf (locRing y) → S.ord f = 1 → discrep S (dForm (Cartier.constFn p) x) m g = -1 → (∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing y) → discrep E (dForm (Cartier.constFn p) x) m g ≤ 0) → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ E : DivOver p, E.Through y → -1 < discrep E (dForm (Cartier.constFn p) x) m g + E.ord f := by
  intro hP X _ _ p n hproj hdim x m g f y S hx hm hnorm hreg hS hSf hdisc hE hadj E hEy
  have hη : (dForm (Cartier.constFn p) x : RatForms p n) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_dForm_of_trBasis _ hx).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨Y, hYi, hYn, s, hsd, K, B, hres, hB, hconn⟩ :=
    GlobalTheory.T.connectedness_lemma_at_normal_point_logResolution hP X p n hproj hdim (dForm (Cartier.constFn p) x) m (CartierDiv.principal g)
      (CartierDiv.principal f).supp hη hm (CartierDiv.supp_ne_top _)
  haveI := hYi; haveI := hYn; haveI := hsd
  obtain ⟨z, hzy, hSz⟩ := (isPrimeOf_placeEquiv S y).1 hS
  have hbir := hres.bir
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  obtain ⟨S', hS'⟩ := DivOver.exists_over ℂ X Y p s hbir S
  obtain ⟨σ, hσz, hS'σ⟩ := DivOver.isAt_lift ℂ X Y p s hbir inferInstance S' S hS' z hSz
  haveI := hres.smooth
  have hη' : EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1
      (h0.trans (map_zero _).symm))
  have hd := discrep_isAt_eq_neg_mult ℂ Y (s ≫ p) n _ hη' K (pullCart s (CartierDiv.principal g)) m
    hm hres.div S' σ (fnPull s g) hS'σ
    (isEqn_pullCart s (hσz ▸ CartierDiv.isEqn_principal g z))
  have hdd : discrep S' (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x)) m (fnPull s g) =
      discrep S (dForm (Cartier.constFn p) x) m g := by
    simp only [discrep]
    rw [BirOrd.formOrd_ratPull_of_over ℂ X Y p s hbir S' S hS' n _ hη,
      DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbir S' S hS' g]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmult : (pullCart s (CartierDiv.principal g) - m • K).mult σ = m := by
    rw [hdd, hdisc] at hd
    have : ((pullCart s (CartierDiv.principal g) - m • K).mult σ : ℚ) = m := by
      field_simp at hd
      linarith
    exact_mod_cast this
  have hsσ : s σ ⤳ y := hσz ▸ hzy
  have heff : ∀ z', z' ⤳ y → ∀ E' : DivOver p, E'.IsAt z' → ∀ g',
      (CartierDiv.principal g).IsEqn z' g' →
      discrep E' (dForm (Cartier.constFn p) x) m g' ≤ 0 := by
    intro z' hz' E' hE' g' hg'
    have h1 := hE E' ((isPrimeOf_placeEquiv E' y).2 ⟨z', hz', hE'⟩)
    have h2 : E'.ord g' = E'.ord g := by
      rw [hE'.ord_eq, hE'.ord_eq, ← hg'.mult_eq, (CartierDiv.isEqn_principal g z').mult_eq]
    simp only [discrep] at h1 ⊢
    rw [h2]
    exact h1
  have hnb := GlobalTheory.T.log_residue_dominant_cartier X p n hproj hdim x m g Y s K B y σ S S' hx hm hres hS' hS'σ hmult hadj
  have hlt := hconn y σ hnorm heff hmult hsσ hnb
  have hordσ : Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 := by
    rw [← hS'σ.ord_eq, DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbir S' S hS' f, hSf]
  exact GlobalTheory.T.discrepancy_add_ord_gt_neg_one_log_resolution X p n hproj hdim _ m g f Y s K B y σ hη hm hres hB hreg hordσ hmult hlt E hEy

end GlobalTheory
