import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CompRat.SplitSum

theorem finrank_prod_int {E : Type} [Field E] [NumberField E] (M N : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N] :
    Module.finrank (𝓞 E) (M × N) = Module.finrank (𝓞 E) M + Module.finrank (𝓞 E) N := by
  have h1 := (TensorProduct.isBaseChange (𝓞 E) (M × N) E).finrank_eq
  have h2 := (TensorProduct.isBaseChange (𝓞 E) M E).finrank_eq
  have h2' := (TensorProduct.isBaseChange (𝓞 E) N E).finrank_eq
  have h3 := (TensorProduct.prodRight (𝓞 E) E E M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

def prodSubEquiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Submodule R M) (B : Submodule R N) : (A.prod B) ≃ₗ[R] A × B where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_prod_sub {E : Type} [Field E] [NumberField E] {M N : Type} [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N]
    (A : Submodule (𝓞 E) M) (B : Submodule (𝓞 E) N) :
    Module.finrank (𝓞 E) (A.prod B) = Module.finrank (𝓞 E) A + Module.finrank (𝓞 E) B := by
  rw [(prodSubEquiv A B).finrank_eq, finrank_prod_int]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem splitLat_sum {D D' : Datum H} (h : SplitLat D) (h' : SplitLat D') : SplitLat (DatumSum.sumDatum D D') := by
  obtain ⟨Lp, Lm, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨Lp', Lm', h1', h2', h3', h4', h5', h6'⟩ := h'
  have := D.fin
  have := D'.fin
  have hE : ∀ x y : D.La × D'.La, (DatumSum.sumDatum D D').EF x y = D.EF x.1 y.1 + D'.EF x.2 y.2 :=
    fun x y => DatumSum.sumForm_apply D.EF D'.EF x y
  have hR : ∀ x : D.La × D'.La, (DatumSum.sumDatum D D').EF (H.rt • x) x =
      D.EF (H.rt • x.1) x.1 + D'.EF (H.rt • x.2) x.2 := fun x => hE _ _
  refine ⟨Lp.prod Lp', Lm.prod Lm', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : Lp.prod Lp' ⊔ Lm.prod Lm' = ⊤ := by
      rw [Submodule.prod_sup_prod, h1, h1', Submodule.prod_top]
    exact this
  · intro a ha b hb
    refine (hE a b).trans ?_
    rw [h2 _ ha.1 _ hb.1, h2' _ ha.2 _ hb.2, add_zero]
  · exact (finrank_prod_sub Lp Lp').trans (by rw [h3, h3']; rfl)
  · exact (finrank_prod_sub Lm Lm').trans (by rw [h4, h4']; rfl)
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h5' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h5 _ ha.1 h0
      · exact add_pos (h5 _ ha.1 h0) (h5' _ ha.2 h0')
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h6' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h6 _ ha.1 h0
      · exact add_neg (h6 _ ha.1 h0) (h6' _ ha.2 h0')

end GlobalTheory.CompRat.SplitSum

namespace GlobalTheory.CompRat

theorem exists_splitLat_of_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → ∃ D₀ : Datum H, D₀.p = p ∧ D₀.q = q ∧ SplitLat D₀ := by
  intro E _ _ _ H p q ⟨D, hp, hq⟩
  refine ⟨DatumSum.sumDatum (powDatum D p) (powDatum (CM.ConjDatum.conj D) q), ?_, ?_, ?_⟩
  · change p * D.p + q * D.q = p
    simp [hp, hq]
  · change p * D.q + q * D.p = q
    simp [hp, hq]
  · refine SplitSum.splitLat_sum (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inr ?_)) (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inl ?_))
    · change p * D.q = 0
      simp [hq]
    · change q * D.q = 0
      simp [hq]

end GlobalTheory.CompRat
