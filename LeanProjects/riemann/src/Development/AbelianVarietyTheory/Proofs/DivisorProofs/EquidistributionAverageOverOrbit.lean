import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAverageOverLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem mean_listed_eq_cover : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (w : V.G), IsClosed ({w} : Set V.G) → ∀ (d : ℕ) (z : ∀ a, Fin (d + 1) → M.X a), I.Lists (V.π w) z → ∀ g : M.Fun, (M.κ * ∑ a, (∑ i, g a (z a i)) / ((d : ℝ) + 1)) * Nat.card (V.X.residueField (V.j w) →+* ℂ) = ∑ᶠ σ, ∑ᶠ x ∈ {x : CxPts V.p σ | x.1 (IsLocalRing.closedPoint ℂ) = V.j w}, M.pull ε π g σ x := by
  intro F _ _ Y V e M I ε π hD w hw d z hL g
  have := CoverHt.isPreimmersion_j V
  have hx : IsClosed ({V.π w} : Set Y.X) := by
    have := V.π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  let g₁ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ :=
    Equiv.piCongrLeft (fun σ => Pts Y σ → ℝ) I.ε (fun a y => g a ((I.pt a).symm y))
  have hg₁ (a) (x : M.X a) : g₁ (I.ε a) (I.pt a x) = g a x := by
    simp only [g₁, Equiv.piCongrLeft_apply_apply, Homeomorph.symm_apply_apply]
  have hg₂ : ∀ (τ σ : F →+* ℂ) (_ : τ = σ) (p : Pts Y τ) (q : Pts Y σ), p.1 = q.1 → g₁ τ p = g₁ σ q := by
    rintro τ σ rfl p q h
    rw [Subtype.ext h]
  have hmean := mean_listed_eq F Y e M I (V.π w) d z g₁ hx hL
  simp only [hg₁] at hmean
  have inner (σ : F →+* ℂ) :
      ∑ᶠ x ∈ {x : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)) | x.1 (IsLocalRing.closedPoint ℂ) = V.j w},
          M.pull ε π g (σ.comp (algebraMap (𝓞 F) F)) x =
        (V.π.residueDegree w : ℝ) * ∑ᶠ (y : Pts Y σ) (_ : under y = V.π w), g₁ σ y := by
    have hs : spMap (σ.comp (algebraMap (𝓞 F) F)) = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
      rw [← Spec.map_comp]
      rfl
    obtain ⟨hε, hπ⟩ := hD (σ.comp (algebraMap (𝓞 F) F))
    have hτ : I.ε (ε (σ.comp (algebraMap (𝓞 F) F))) = σ := (HtModel.bijective_comp F).1 hε
    let Φ : {z : {z : Sp ℂ ⟶ V.G // z ≫ V.π ≫ Y.str = spMap σ} // below z.1 = w} →
        ↥{x : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)) | x.1 (IsLocalRing.closedPoint ℂ) = V.j w} := fun z =>
      ⟨⟨z.1.1 ≫ V.j, by rw [Category.assoc, V.pb.w, ← Category.assoc, z.1.2, hs]⟩,
        (Scheme.Hom.comp_apply _ _ _).trans (congrArg V.j z.2)⟩
    have hΦ : Function.Bijective Φ := by
      refine ⟨fun a b h => ?_, ?_⟩
      · have h' : a.1.1 ≫ V.j = b.1.1 ≫ V.j := congrArg (fun t => t.1.1) h
        exact Subtype.ext (Subtype.ext (V.pb.hom_ext h' (a.1.2.trans b.1.2.symm)))
      · rintro ⟨x, hx'⟩
        have e1 : x.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := x.2.trans hs
        refine ⟨⟨⟨V.pb.lift x.1 (spMap σ) e1, V.pb.lift_snd _ _ _⟩, ?_⟩, ?_⟩
        · apply V.j.isEmbedding.injective
          exact (Scheme.Hom.comp_apply _ _ _).symm.trans
            ((congrArg (fun t : Sp ℂ ⟶ V.X => t (IsLocalRing.closedPoint ℂ)) (V.pb.lift_fst _ _ e1)).trans hx')
        · exact Subtype.ext (Subtype.ext (V.pb.lift_fst _ _ _))
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_eq_of_bijective Φ hΦ (f := fun z => g₁ σ ⟨z.1.1 ≫ V.π, (Category.assoc _ _ _).trans z.1.2⟩) fun z => ?_]
    · rw [CoverHt.finsum_lifts σ V.π Y.str w hw (g₁ σ)]
      congr 1
      exact finsum_subtype_eq_finsum_cond (fun y : Pts Y σ => under y = V.π w)
    · obtain ⟨w', h1, h2⟩ := hπ (Φ z).1
      show g₁ σ _ = g _ _
      rw [← hg₁]
      refine (hg₂ _ _ hτ _ _ ?_).symm
      rw [← h2]
      congr 1
      refine V.pb.hom_ext h1 ?_
      rw [← Category.assoc, h2, (I.pt _ _).2, z.1.2, hτ]
  rw [hmean, CoverHt.card_emb V w hw, ← finsum_eq_of_bijective _ (HtModel.bijective_comp F) fun σ => (inner σ).symm,
    finsum_eq_sum_of_fintype, ← Finset.mul_sum]
  obtain ⟨_, _⟩ := ExtConj.pts Y _ hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = V.π w} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  field_simp

end GlobalTheory.Mean4O
