import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedPresentationEvalQuotientFractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfAgreeOnAffineOpenGeneratorsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem eq_of_secRatioEq_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k), w ∈ N ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ (thickObj R (maximalIdeal R) e G).left), a ≫ (thickObj R (maximalIdeal R) e G).hom = b ≫ (thickObj R (maximalIdeal R) e G).hom → (∀ x, a x ∈ N) → (∀ x, b x ∈ N) → (∀ l, SecRatioEq U.LG.L (a ≫ (fstG (maximalIdeal R) e G).left) (b ≫ (fstG (maximalIdeal R) e G).left) (σ l) s₀ (σ l) s₀) → a = b := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, H⟩ := GlobalTheory.T.exists_section_ratios_generate_mod_maximal R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨N, m, σ, r, hwN, hNaff, hNi, hgerm, hgen⟩ := H e k hk s₀ i w hw hu
  have hw' : (fstG (maximalIdeal R) e G).left ≫ G.hom = (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e :=
    (fstG (maximalIdeal R) e G).w
  have hz : ∀ x ∈ maximalIdeal R ^ (e + 1), (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) x = 0 := by
    intro x hx
    have h0 : (thick R (maximalIdeal R) e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = 0 := by
      have := congrArg (fun φ => φ.hom x)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      rw [← this, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, hw', Scheme.Hom.comp_appTop, CommRingCat.hom_comp, h0, map_zero]
  have hgen' := GlobalTheory.T.localized_presentation_eval_quotient_fraction R _ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) (e + 1) hz m r hgen
  refine ⟨N, m, σ, hwN, fun W a b hab ha hb hrat => ?_⟩
  have ha' : ⊤ ≤ a ⁻¹ᵁ N := fun x _ => ha x
  have hb' : ⊤ ≤ b ⁻¹ᵁ N := fun x _ => hb x
  have hst : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (f : Γ((thickObj R (maximalIdeal R) e G).left, N)), c x ∈ N →
      (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) = gs c x N f := by
    intro c x f h
    have e1 : gs (c ≫ 𝟙 _) x N f = (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) := by
      rw [gs_eq (𝟙 _) (c x) _ h, ← gs_pull c (𝟙 _) x _ h, gs_eq c x _ (show c x ∈ (𝟙 (thickObj R (maximalIdeal R) e G).left : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) ⁻¹ᵁ N from h)]
      exact (Scheme.Hom.germ_stalkMap_apply c _ x h _).symm
    rw [← e1, Category.comp_id]
  have hsg : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (s : H0 U.LG.L k), c x ∈ N →
      secGerm (c ≫ (fstG (maximalIdeal R) e G).left) x s i = (c.stalkMap x).hom (secGerm (fstG (maximalIdeal R) e G).left (c x) s i) :=
    fun c x s h => secGerm_comp c _ x s (hNi h)
  refine GlobalTheory.T.eq_of_agree_on_affineOpen_generators R _ W ((fstG (maximalIdeal R) e G).left ≫ G.hom) N hNaff m r hgen' a b ?_ ha' hb' ?_
  · rw [hw', ← Category.assoc, hab, Category.assoc]
  · intro l
    apply fn_ext
    intro x _
    rw [gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_pull (𝟙 W) a x N (ha x), gs_pull (𝟙 W) b x N (hb x), Category.id_comp, Category.id_comp]
    have key := secRatioEq_iff_germ.1 (hrat l) x i i (hNi (ha x)) (hNi (hb x))
    rw [hsg a x _ (ha x), hsg a x _ (ha x), hsg b x _ (hb x), hsg b x _ (hb x),
      (hgerm _ (ha x)).2 l, (hgerm _ (hb x)).2 l, map_mul, map_mul, hst a x _ (ha x), hst b x _ (hb x)] at key
    have hA := ((hgerm _ (ha x)).1).map (a.stalkMap x).hom
    have hB := ((hgerm _ (hb x)).1).map (b.stalkMap x).hom
    refine (hA.mul hB).mul_left_inj.1 ?_
    linear_combination key

end GlobalTheory.Mum
