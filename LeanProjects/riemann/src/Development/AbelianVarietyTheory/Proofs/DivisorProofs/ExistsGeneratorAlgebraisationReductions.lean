import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorSchemeLineBundleAffineFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem res_compat_of_gm {Z B : Scheme.{0}} {N : LB B} (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z i i', b z ∈ N.U i → b z ∈ N.U i' → gm (𝟙 _) z _ (s i) = gm b z _ (N.g i i') * gm (𝟙 _) z _ (s i'))
    (i i' : N.ι) :
    res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) =
      pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i') := by
  apply unit_ext
  intro z hz
  have hz' : b z ∈ N.U i ⊓ N.U i' := hz
  rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 _) b z _ hz', Category.id_comp]
  exact h z i i' hz'.1 hz'.2

theorem appLE_eq_of_gm {Y Y' B : Scheme.{0}} {N : LB B} (β : Y ⟶ Y') (b : Y ⟶ B) (b' : Y' ⟶ B) (hβ : β ≫ b' = b)
    (i : N.ι) (s : Γ(Y, b ⁻¹ᵁ N.U i)ˣ) (s' : Γ(Y', b' ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z, b z ∈ N.U i → gm β z _ s' = gm (𝟙 _) z _ s) :
    (β.appLE (b' ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hβ]; exact le_rfl)).hom s'.val = s.val := by
  apply TopCat.Presheaf.section_ext Y.sheaf
  intro z hz
  have := congrArg Units.val (h z hz)
  have hz2 : β z ∈ b' ⁻¹ᵁ N.U i := by rw [← hβ] at hz; exact hz
  rw [gm_val β z _ hz2, gm_val (𝟙 Y) z _ hz] at this
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  exact this

theorem exists_isGen_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : LB X.left), N.IsLB → ∀ s : ∀ e (i : N.ι), Γ((Y e).left, b e ⁻¹ᵁ N.U i)ˣ, (∀ e z i i', b e z ∈ N.U i → b e z ∈ N.U i' → gm (𝟙 _) z _ (s e i) = gm (b e) z _ (N.g i i') * gm (𝟙 _) z _ (s e i')) → (∀ e z i, b e z ∈ N.U i → gm (β e) z _ (s (e + 1) i) = gm (𝟙 _) z _ (s e i)) → ∃ t : LB.Gen N, t.IsGen := by
  intro R _ _ I hI X hX Y β b hb hβ N hN s hs hsβ
  obtain ⟨G, q, u, hqa, hql, hu, hU⟩ := GlobalTheory.T.generatorScheme_lineBundle_affine_finiteType X.left N hN
  have hex := fun e => hU (Y e).left (b e) (s e) (res_compat_of_gm (b e) (s e) (fun z i i' => hs e z i i'))
  choose f hfq hfu using fun e => (hex e).exists
  have hfβ : ∀ e, β e ≫ f (e + 1) = f e := fun e =>
    (hex e).unique ⟨by rw [Category.assoc, hfq, hβ], fun i => by
        rw [← Scheme.Hom.appLE_comp_appLE (β e) (f (e + 1)) (q ⁻¹ᵁ N.U i) (b (e + 1) ⁻¹ᵁ N.U i) (b e ⁻¹ᵁ N.U i)
          (by rw [← hfq (e + 1)]; exact le_rfl) (by rw [← hβ e]; exact le_rfl),
          CommRingCat.comp_apply, hfu (e + 1) i]
        exact appLE_eq_of_gm (β e) (b e) (b (e + 1)) (hβ e) i (s e i) (s (e + 1) i) (hsβ e · i)⟩
      ⟨hfq e, hfu e⟩
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ X.hom)
  have H := GlobalTheory.T.formalAlgebraisation_morphisms'
  obtain ⟨g, hg, -⟩ := H R I hI X Z hX (inferInstanceAs (IsSeparated (q ≫ X.hom)))
    (inferInstanceAs (LocallyOfFiniteType (q ≫ X.hom))) (inferInstanceAs (QuasiCompact (q ≫ X.hom)))
    Y β b hb hβ f (fun e => by
      show f e ≫ q ≫ X.hom = _
      rw [← Category.assoc, hfq, (hb e).w]) hfβ
  have hgq : g.left ≫ q = 𝟙 X.left := by
    have hH := H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b (fun e => (hb e).w) hβ
    have h1 := hH.unique (y₁ := Over.homMk (g.left ≫ q) (by rw [Category.assoc]; exact Over.w g))
      (y₂ := 𝟙 X) (fun e => by
        show b e ≫ (g.left ≫ q) = b e
        rw [← Category.assoc, hg e, hfq e])
      (fun e => by rw [Over.id_left, Category.comp_id])
    exact congrArg CommaMorphism.left h1
  have hpt : ∀ x, q (g.left x) = x := fun x => by rw [← Scheme.Hom.comp_apply, hgq]; rfl
  have hle : ∀ i, N.U i ≤ g.left ⁻¹ᵁ (q ⁻¹ᵁ N.U i) := fun i x hx => by
    show q (g.left x) ∈ N.U i
    rw [hpt]; exact hx
  refine ⟨⟨fun i => res (hle i) (pullU g.left _ (u i))⟩, fun i j => ?_⟩
  apply unit_ext
  intro x hx
  have hx' : q (g.left x) ∈ N.U i ⊓ N.U j := by rw [hpt]; exact hx
  have key := congrArg (gm g.left x (q ⁻¹ᵁ (N.U i ⊓ N.U j))) (hu i j)
  rw [map_mul, gm_res _ x _ hx', gm_res _ x _ hx', gm_pull g.left q x _ hx', hgq] at key
  show gm (𝟙 _) x _ (res _ (res (hle i) (pullU g.left _ (u i)))) =
    gm (𝟙 _) x _ (N.g i j * res _ (res (hle j) (pullU g.left _ (u j))))
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx.1, gm_res _ x _ hx, gm_res _ x _ hx.2,
    gm_pull (𝟙 _) g.left x _ (hle i hx.1), gm_pull (𝟙 _) g.left x _ (hle j hx.2),
    Category.id_comp]
  exact key

end GlobalTheory.FormalAlg
