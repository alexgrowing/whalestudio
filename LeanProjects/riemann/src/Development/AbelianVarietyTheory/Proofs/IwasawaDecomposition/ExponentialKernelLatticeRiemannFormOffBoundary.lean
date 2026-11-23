import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExpStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingFormStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_eq_comp_linearEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : Sp ℂ ⟶ X) (g g' : ℕ) (ex : (Fin g → ℂ) → (Over.mk p ⟶ t.G)) (e' : (Fin g' → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p ex → IsHolTo Set.univ (fun w => (ex w).left) → IsExpAt t p e' → IsHolTo Set.univ (fun w => (e' w).left) → ∃ L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e' z = ex (L z) := by
  intro E _ _ _ H X t p g g' ex e' hex hhol he' hhol'
  have one : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), (∀ z w, f (z + w) = f z * f w) → f 0 = 1 := by
    intro m f hf
    have h := hf 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have der : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p f →
      ∀ v : epsPt p ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (f 0).left →
        ∃! w, IsDerivAt0 (fun z => (f z).left) w v.left := by
    intro m f hf v hv
    refine hf.2.2 v.left ⟨Over.w v, ?_⟩
    rw [hv, one f hf.1]
  have H3 := (GlobalTheory.holomorphic_hom_determined X t.G).2.2.1 p
  obtain ⟨h, hh, -⟩ := H3 (Fin g' → ℂ) g e' ex he'.1 hex.1 hhol' hhol (der ex hex)
  obtain ⟨h', hh', -⟩ := H3 (Fin g → ℂ) g' ex e' hex.1 he'.1 hhol hhol' (der e' he')
  obtain ⟨k, -, hk⟩ := H3 (Fin g' → ℂ) g' e' e' he'.1 he'.1 hhol' hhol' (der e' he')
  obtain ⟨k', -, hk'⟩ := H3 (Fin g → ℂ) g ex ex hex.1 hex.1 hhol hhol (der ex hex)
  have c1 : h' ∘ₗ h = LinearMap.id :=
    (hk _ fun z => by rw [LinearMap.comp_apply, ← hh', ← hh]).trans (hk _ fun z => rfl).symm
  have c2 : h ∘ₗ h' = LinearMap.id :=
    (hk' _ fun z => by rw [LinearMap.comp_apply, ← hh, ← hh']).trans (hk' _ fun z => rfl).symm
  exact ⟨LinearEquiv.ofLinear h h' c2 c1, hh⟩

theorem exists_hermForm_transport : ∀ (g g' : ℕ) (L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Hm₀ : Matrix (Fin g') (Fin g') ℂ), Hm₀.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (hermForm Hm₀ z z).re) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ v w, hermForm Hm (L v) (L w) = hermForm Hm₀ v w := by
  intro g g' L Hm₀ hH hpos
  let A : Matrix (Fin g') (Fin g) ℂ := LinearMap.toMatrix' L.symm.toLinearMap
  have hA : ∀ v, A.mulVec v = L.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have key : ∀ v w, hermForm (Aᵀ * Hm₀ * A.map star) v w = hermForm Hm₀ (L.symm v) (L.symm w) := by
    intro v w
    simp only [hermForm, ← hA]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
    congr 1
    ext j
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, mul_comm]
  refine ⟨Aᵀ * Hm₀ * A.map star, ?_, fun z hz => ?_, fun v w => ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    congr 1
    · ext a b
      simp [Matrix.conjTranspose_apply]
  · rw [key]
    exact hpos _ (by simpa using hz)
  · rw [key, L.symm_apply_apply, L.symm_apply_apply]

theorem exists_pushed_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X), IsPeriod (Fu.Di i) ty P → Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) → y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p → ∃ e' : (Fin g → ℂ) → (Over.mk p ⟶ Z.t.G), IsExpAt Z.t p e' ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ (∀ z, e' z = 1 ↔ z ∈ P.range) ∧ ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (e' ((k : ℂ)⁻¹ • P a)) (e' ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hP hu hp
  exact ⟨pushEx Z Fu y i P p hu hp, GlobalTheory.T.isExponential_modelFiber_of_uniformisationExp E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.isHolomorphic_uniformisationExp_modelFiber E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.expModelFiber_eq_one_iff_mem_periodLattice E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP⟩

theorem kernel_lattice_of_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (x : CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g x ex hσ hpq hx hex hhol
  obtain ⟨y, hy⟩ := hx.exists_lift
  let e₀ : Fin (Fintype.card (Letter Dw)) ≃ Letter Dw := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c σ (e₀ j).1) hpq hσ hty
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact x.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  obtain ⟨e', he', hhol', hker, hweil⟩ := exists_pushed_exp E H Dw l Xo c O β Z _ _ _ Fu y i P (x.1 ≫ genι Z) hP hu
    (by rw [← hy, Category.assoc])
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g _ ex e' hex hhol he' hhol'
  obtain ⟨Hm₀, hH₀, hpos₀, hEF⟩ := hP.2.2.2.2
  obtain ⟨Hm, hH, hpos, hform⟩ := exists_hermForm_transport _ _ L Hm₀ hH₀ hpos₀
  have hkerex : ∀ w, ex w = 1 ↔ ∃ a, w = L (P a) := by
    intro w
    constructor
    · intro h
      have h' : e' (L.symm w) = 1 := by rw [hL, L.apply_symm_apply, h]
      obtain ⟨a, ha⟩ := (hker _).1 h'
      exact ⟨a, by rw [ha, L.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [← hL]
      exact (hker _).2 ⟨a, rfl⟩
  refine ⟨Hm, hH, hpos, ?_, ?_, ?_⟩
  · have hset : {w | ex w = 1} = (L.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      ext w
      simp only [Set.mem_setOf_eq, hkerex, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨P a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, Submodule.span_image, hP.2.2.2.1, Submodule.map_top, LinearMap.range_eq_top]
    exact L.surjective
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    exact ⟨(Fu.Di i).EF a b, by rw [hform, hEF]⟩
  · intro k v w ζ hk hv hw hζ
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    rw [← L.map_smul, ← L.map_smul, ← hL, ← hL]
    refine hweil k a b ζ hk ?_
    rw [hζ, hform, hEF, Complex.ofReal_intCast]

end GlobalTheory.ShFam.Hor.LogCh
