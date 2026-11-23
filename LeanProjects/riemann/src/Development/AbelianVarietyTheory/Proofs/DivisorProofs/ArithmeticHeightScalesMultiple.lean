import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HermLB GlobalTheory.ArInt

namespace GlobalTheory.PtHtComb

theorem height_comb_mul : GlobalTheory.Published.CycleHeights → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (m : ℕ) (h h' : X → ℝ),
    (comb L n).IsArithHeight h → (comb L (fun i => (m : ℤ) * n i)).IsArithHeight h' →
    ∀ x : X, ArInt.IsAlgPt x → h' x = m * h x := by
  intro HC k _ X p D hX ι _ L n m h h' H H' x hx
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hr : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    (RingHom.charZero_iff (i.residueFieldMap (genericPoint Z)).hom.injective).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  obtain ⟨⟨Φ, hΦ, -⟩, -⟩ := (HC.arExists k Z (i ≫ p) 0 hZ).2 ι fun j => (L j).pull i rfl
  have key (n' : ι → ℤ) (g : X → ℝ) (G : (comb L n').IsArithHeight g) :
      g (i (genericPoint Z)) = Φ (lin fun j => (n' j : ℝ)) := by
    have e := (isometric_comb_pull L n' i rfl).isSelfInter hZ (hΦ n')
    rw [zero_add, pow_one] at e
    exact (G.isSelfInter_restrict hX i rfl).unique hZ e
  rw [key _ _ H, key _ _ H', ← smul_eq_mul, ← map_smul]
  congr 1
  simp only [lin, Finset.smul_sum, Int.cast_mul, Int.cast_natCast, MvPolynomial.smul_eq_C_mul, map_mul, mul_assoc]

end GlobalTheory.PtHtComb
