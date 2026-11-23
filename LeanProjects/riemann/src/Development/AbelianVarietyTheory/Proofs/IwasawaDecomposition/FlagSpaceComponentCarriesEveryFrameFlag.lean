import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgClosedTranscendentalSpecialisingEverywhStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFrameTranscendentalSpecialisingTwoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointLiftValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRingStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.FlagFibre

theorem sp_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (a : B →+* C') (b : A →+* B) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]; exact Spec.map_id _

theorem carries_every : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U), ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ i K _ _ χ x hx g g' p hp hc
  obtain ⟨L, _, _, ι, s, hs, hV⟩ := GlobalTheory.T.exists_algClosed_transcendental_specialising_everywhere K
  obtain ⟨gL, hgL⟩ := GlobalTheory.T.exists_genericFrame_transcendental_specialising_two E H Dw l Xo c O β Z K χ (x ≫ genι Z) g g' L ι s hs ((spMap ι ≫ x) ≫ genι Z)
    (Category.assoc _ _ _)
  have hxL : (spMap ι ≫ x) ≫ genStr Z = spMap (ι.comp χ) := by
    rw [Category.assoc, hx, sp_comp]
  obtain ⟨⟨j, pL⟩, ⟨hpL, hcL⟩, -⟩ := Φ.lifts L (ι.comp χ) (spMap ι ≫ x) hxL gL
  have spec : ∀ (a : K) (b : EigFrame Z χ (x ≫ genι Z)), (∀ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K)
      (sV : V), (algebraMap V L).comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V →
      algebraMap V L sV = s → r sV = a → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x ≫ genι Z))
        (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ),
        gV.Tri (algebraMap V L) gL tL ∧ gV.Tri r b tk) →
      ∃ p' : Sp K ⟶ (Φ.C j).Y.X, p' ≫ (Φ.C j).π = x ∧ (Φ.C j).Carries p' b := by
    intro a b hb
    obtain ⟨V, ιV, r, sV, h1, h2, h3, h4, h5⟩ := hV a
    obtain ⟨gV, tL, tk, hTL, hTk⟩ := hb V ιV r sV h1 h2 h3 h4 h5
    have hpL' : pL ≫ (Φ.C j).π = spMap (algebraMap V L) ≫ (spMap ιV ≫ x) := by
      rw [hpL, ← Category.assoc, ← sp_comp, h1]
    obtain ⟨q, hq1, hq2⟩ := GlobalTheory.T.exists_flagComponent_point_lift_valuationRing E H Dw l Xo c O β Z F e (Φ.C j) V L (spMap ιV ≫ x) pL hpL'
    have hc' : (Φ.C j).Carries (spMap (algebraMap V L) ≫ q) gL := by rw [hq2]; exact hcL
    have hxV : spMap ιV ≫ x ≫ genι Z = q ≫ (Φ.C j).π ≫ genι Z := by
      rw [← Category.assoc q, hq1, Category.assoc]
    refine ⟨spMap r ≫ q, ?_, GlobalTheory.T.carriedFrames_specialise_flagComponent_localRing E H Dw l Xo c O β Z F e (Φ.C j) V L (algebraMap V L)
      (IsFractionRing.injective V L) K r h3 q (ιV.comp χ) _ hxV gV (ι.comp χ) _ gL tL hTL hc' χ _ b tk hTk⟩
    rw [Category.assoc, hq1, ← Category.assoc, ← sp_comp, h2, sp_id, Category.id_comp]
  obtain ⟨p₀, hp₀, hc₀⟩ := spec 0 g fun V ιV r sV h1 h2 h3 h4 h5 => (hgL V _ ιV r sV h1 h2 h3 h4).1 h5
  obtain ⟨p₁, hp₁, hc₁⟩ := spec 1 g' fun V ιV r sV h1 h2 h3 h4 h5 => (hgL V _ ιV r sV h1 h2 h3 h4).2 h5
  obtain ⟨_, -, hu⟩ := Φ.lifts K χ x hx g
  have hij : i = j := congrArg Sigma.fst ((hu ⟨i, p⟩ ⟨hp, hc⟩).trans (hu ⟨j, p₀⟩ ⟨hp₀, hc₀⟩).symm)
  subst hij
  exact ⟨p₁, hp₁, hc₁⟩

end GlobalTheory.FlagFibre
