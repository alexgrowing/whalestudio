import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem transl_toTerm_eq {S : Scheme.{0}} {X : Over S} (f g : X ⟶ Over.mk (𝟙 S)) : f = g := by
  ext
  have hf := Over.w f
  have hg := Over.w g
  simp only [Over.mk_hom] at hf hg
  exact (Category.comp_id f.left).symm.trans (hf.trans (hg.symm.trans (Category.comp_id g.left)))

theorem transl_comp {S : Scheme.{0}} {G : Over S} [GrpObj G] (y z : Over.mk (𝟙 S) ⟶ G) :
    transl y ≫ transl z = transl (y * z) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc,
    transl_toTerm_eq (_ ≫ Over.homMk G.hom (by simp)) (Over.homMk G.hom (by simp)), _root_.mul_assoc, ← comp_mul]

theorem transl_one {S : Scheme.{0}} {G : Over S} [GrpObj G] : transl (1 : Over.mk (𝟙 S) ⟶ G) = 𝟙 G := by
  unfold transl
  rw [comp_one, _root_.mul_one]

instance transl_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y) :=
  ⟨⟨transl y⁻¹, by rw [transl_comp, _root_.mul_inv_cancel, transl_one], by rw [transl_comp, _root_.inv_mul_cancel, transl_one]⟩⟩

instance transl_left_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y).left :=
  inferInstanceAs (IsIso ((Over.forget S).map (transl y)))

theorem Near.chart_isOpenImmersion_over {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)) :
    IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  have := N.isOpen
  cases j with
  | none => exact ⟨N.isOpen, N.u_over⟩
  | some k =>
    refine ⟨?_, ?_⟩
    · rw [Near.chart_some]; infer_instance
    · rw [Near.chart_some, Category.assoc, Over.w, N.u_over]

end GlobalTheory.Mum
