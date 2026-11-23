import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Topology ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

theorem hodge_gram_conjPt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), ¬ Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ y : CxPts (genStr s.T.Z) σ, ∃ y' : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ), (LiesIn y' (genBd s.T.Z) ↔ LiesIn y (genBd s.T.Z)) ∧ x.r _ y' = x.r σ y ∧ ∀ g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), ∃ g' : EigFrame s.T.Z ((starRingEnd ℂ).comp σ) (y'.1 ≫ genι s.T.Z), ∀ τ : D.host.E →+* ℂ, x.gram y' g' τ = (x.gram y g τ).map (starRingEnd ℂ) ∧ (x.hodge _).gram y' g' τ = ((x.hodge σ).gram y g τ).map (starRingEnd ℂ) := by
  intro D A N j S κ s x σ _ y
  have hc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext Complex.conj_conj))
  let y' : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ y.1, by rw [Category.assoc, y.2, ← Spec.map_comp]; rfl⟩
  have hL : LiesIn y' (genBd s.T.Z) ↔ LiesIn y (genBd s.T.Z) := liesIn_iff_of_comp rfl _
  let jm : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ) → CxPts (genStr s.T.Z) σ := fun z =>
    ⟨spMap (starRingEnd ℂ) ≫ z.1, by
      rw [Category.assoc, z.2, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => Complex.conj_conj (σ a)))⟩
  have hj : IsConjMap jm := fun _ => rfl
  have hjy : jm y' = y := Subtype.ext (by
    show spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ y.1 = y.1
    rw [← Category.assoc, hc, Category.id_comp])
  refine ⟨y', hL, ?_, fun g => ?_⟩
  · simp only [OddPrimesWithRootsOfUnity.r, x.nrm_conj σ _ jm hj, hjy]
  have hx : y'.1 ≫ genι s.T.Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι s.T.Z := Category.assoc _ _ _
  obtain ⟨g', hg⟩ := g.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ) rfl hx
  have hgram : ∀ τ, x.gram y' g' τ = (x.gram y g τ).map (starRingEnd ℂ) := fun τ =>
    x.gram_conj rfl g g' τ (hg τ)
  refine ⟨g', fun τ => ⟨hgram τ, ?_⟩⟩
  by_cases hy : LiesIn y (genBd s.T.Z)
  · rw [x.hodge_gram_of_liesIn hy, x.hodge_gram_of_liesIn (hL.2 hy), hgram]
  · obtain ⟨f, hf⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hy
    obtain ⟨f', hf'⟩ := f.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ) rfl hx
    have hH : IsHodgeFrame s.U y' f' := hf.conj (RingHom.ext fun a => (Complex.conj_conj (σ a)).symm)
      (by show y.1 = spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ y.1; rw [← Category.assoc, hc, Category.id_comp])
      (fun τ i => by
        rw [hf' τ i, GlobalTheory.GradedPieces.dual_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
          RingHom.ext Complex.conj_conj, spMap_dualMap_id, Category.id_comp])
    rw [x.hodge_gram hH, x.hodge_gram hf, hf'.co τ hg hx]
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
      smul_eq_mul, RCLike.star_def, Complex.conj_conj, Complex.conj_ofReal]

end GlobalTheory.ShFam
