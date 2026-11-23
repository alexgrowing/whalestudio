import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingMulImageEqOfFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreFieldPointsInjectiveProjectiveMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem Near.closed_product_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  intro R _ _ _ M G' _ E N fU l hl1 hl2 hsurj Ω _ κ s s' a b c c' x y x' y' hs hs' ha hb hc ha' hb' hc'
  obtain ⟨Ω₁, _, io₁, ca, cb, hca, hcb, hcc⟩ := GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s a b c x y hs ha hb hc
  obtain ⟨Ω₂, _, io₂, ca', cb', hca', hcb', hcc'⟩ :=
    GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s' a b c' x' y' hs' ha' hb' hc'
  obtain ⟨Ω₃, _, j₁, j₂, hj⟩ := GlobalTheory.T.exists_common_field_extension' Ω Ω₁ Ω₂ io₁ io₂
  have : Mono E.j := by haveI := E.imm; infer_instance

  let g₁ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₁.comp κ)) :=
    Over.homMk (spMap j₁) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom])
  let g₂ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₂.comp κ)) :=
    Over.homMk (spMap j₂) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom, hj])
  have hg₁ : g₁.left = spMap j₁ := rfl
  have hg₂ : g₂.left = spMap j₂ := rfl
  have e₁ : spMap j₁ ≫ spMap io₁ = spMap (j₁.comp io₁) := specMap_contravariant_comp_ringHom _ _
  have e₂ : spMap j₂ ≫ spMap io₂ = spMap (j₁.comp io₁) := by rw [specMap_contravariant_comp_ringHom, hj]
  have hA : g₁ ≫ ca = g₂ ≫ ca' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hca, hca']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hB : g₁ ≫ cb = g₂ ≫ cb' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcb, hcb']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hC : g₁ ≫ (ca * cb) = g₂ ≫ (ca' * cb') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, hA, hB]
  have hfU : spMap (j₁.comp io₁) ≫ c ≫ fU = spMap (j₁.comp io₁) ≫ c' ≫ fU := by
    have := congrArg (fun g => g.left ≫ E.j) hC
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcc, hcc'] at this
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂] at this
    exact this

  have hlies : ∀ (t : Sp Ω ⟶ M.S) (d : Sp Ω ⟶ N.U.left) (z : Sp Ω ⟶ G'.left), t ≫ M.π = spMap (κ.comp (residue R)) →
      N.Pt t d z → d ≫ N.U.hom = spMap (κ.comp (residue R)) := by
    rintro t d z ht ⟨x₀, h₁, h₂, -⟩
    rw [← h₁, Category.assoc, pullback.condition, ← Category.assoc, h₂, ht]
  have hco : ∀ d : Sp Ω ⟶ N.U.left, d ≫ N.U.hom = spMap (κ.comp (residue R)) →
      (spMap (j₁.comp io₁) ≫ d) ≫ N.U.hom = spMap (((j₁.comp io₁).comp κ).comp (residue R)) := by
    intro d hd
    rw [Category.assoc, hd, specMap_contravariant_comp_ringHom]
  have key := GlobalTheory.T.closedFibre_fieldPoints_injective_projective_map R M G' E N fU l hl1 hl2 hsurj Ω₃ ((j₁.comp io₁).comp κ) (spMap (j₁.comp io₁) ≫ c)
    (spMap (j₁.comp io₁) ≫ c') (hco c (hlies s c _ hs hc)) (hco c' (hlies s' c' _ hs' hc'))
    (by simpa only [Category.assoc] using hfU)
  exact GlobalTheory.T.spMap_field_ext_cancel Ω Ω₃ (j₁.comp io₁) N.U.left c c' key

end GlobalTheory.Mum
