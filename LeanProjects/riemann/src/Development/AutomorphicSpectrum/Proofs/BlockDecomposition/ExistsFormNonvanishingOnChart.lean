import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatioStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem exists_form_of_mem_open : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (U : X.Opens), genericPoint X ∈ U → ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧
      j ∉ ptIdeal (i (genericPoint X)) ∧ ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
        GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ U := by
  intro m n X _ i _ U hU
  classical
  have hx : i (genericPoint X) ∈ mchart (ptChart (i (genericPoint X))) :=
    Set.mem_iInter.2 fun k => mem_ptChart _ k
  have hcl : IsClosed (i '' (U : Set X)ᶜ) :=
    i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl
  let V : (MP ℤ m n).Opens := ⟨(i '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hV : i (genericPoint X) ∈ V := by
    rintro ⟨x, hxU, hxe⟩
    exact hxU (i.isClosedEmbedding.injective hxe ▸ hU)
  obtain ⟨g, hgV, hgx⟩ := (SmoothRep.gen m n (ptChart (i (genericPoint X)))).1.exists_basicOpen_le ⟨_, hV⟩ hx
  obtain ⟨F0, rfl⟩ := ExRat.dehomog_surjective _ g
  obtain ⟨a, F, hF, e⟩ := ExRat.exists_homog (ptChart (i (genericPoint X))) F0
  rw [← e] at hgV hgx
  have hm := homog_mul hF (ExRat.isMultiHomog_mono (ptChart (i (genericPoint X))) 1)
  refine ⟨F * ExRat.mono (ptChart (i (genericPoint X))) 1, _, hm, ?_, ?_⟩
  · rw [mem_ptIdeal_iff_aeval_ptCoord m n _ _ _ hm, FnForm.aeval_ptCoord_eq_mul _ _ hx hm]
    simp only [ptCoord_ptChart, one_pow, Finset.prod_const_one, one_mul, map_mul, ExRat.dehomog_mono, mul_one]
    exact (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ hx _).2 hgx
  · intro y z hyz hne
    have hz : ∀ k, z ⟨k, ptChart (i (genericPoint X)) k⟩ ≠ 0 := by
      intro k h0
      apply hne
      have : eval z (map (Int.castRingHom ℂ) (ExRat.mono (ptChart (i (genericPoint X))) 1)) = 0 := by
        simp only [ExRat.mono, Pi.one_apply, pow_one, map_prod, map_X]
        exact Finset.prod_eq_zero (Finset.mem_univ k) ((eval_X _).trans h0)
      rw [map_mul, map_mul, this, mul_zero]
    have hF0 : eval z (map (Int.castRingHom ℂ) F) ≠ 0 := by
      intro h0
      apply hne
      rw [map_mul, map_mul, h0, zero_mul]
    have hw : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart (ptChart (i (genericPoint X)))) :=
      mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptsIn.1 ((hyz k _).1.2 (hz k)))
    have hev : ev (mpStr ℤ m n) σ₀ _ (dehomog (ptChart (i (genericPoint X))) F) (PtsOver.map i rfl _ y) ≠ 0 := by
      rw [GlobalTheory.T.dehomogenized_eval_eq_ratio m n _ F a hF _ z hyz hw]
      exact div_ne_zero hF0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k))
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hw _).2 hev)
    have hp := hgV hb
    rw [mem_ptsIn]
    by_contra h
    exact hp ⟨_, h, rfl⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq
