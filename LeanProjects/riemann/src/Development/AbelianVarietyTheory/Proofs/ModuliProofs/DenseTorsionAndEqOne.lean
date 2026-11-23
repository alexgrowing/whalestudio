import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsMemNonzeroLocus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.PrimePowerTorsion

theorem dense_torsion (hA : Out.AmpleSt) (hK : Out.KerPowSt) (hI : Out.IrredSt) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (l : ℕ) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) := by
  have := P.isAb.comm
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (x := x) (U := ⟨U, hU⟩) hx
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ Out.nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA K P N hN
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, ham⟩ : ∃ m : ℕ, 4 ≤ m ∧ a + m = l ^ (a + 4) := by
    have := Nat.lt_pow_self (n := a + 4) (show 1 < l by omega)
    exact ⟨l ^ (a + 4) - a, by omega, by omega⟩
  obtain ⟨t, ht⟩ := gen m hm x
  let p : (Out.baseOver (Sp K)).left := IsLocalRing.closedPoint K
  obtain ⟨t', ht'⟩ := gen (a + m) (by omega) ((1 : Out.baseOver (Sp K) ⟶ P.A).left p)
  have e := nonzeroLocus_secMul s t
  obtain ⟨b, hb, q, hq⟩ := TorsionDense.exists_mem_nonzeroLocus P hI hK (a + m) (by omega)
    (by rw [ham, Nat.cast_pow]; exact pow_ne_zero _ hlK)
    {x | ∃ j : ℕ, x ^ l ^ j = 1} (fun w hw b ⟨j, hb⟩ => ⟨a + 4 + j, by
      rw [mul_pow, pow_add, pow_mul w, ← ham, hw, one_pow, mul_comm _ (l ^ j), pow_mul, hb, one_pow,
        _root_.one_mul]⟩)
    (secMul s t) t' x (e.ge ⟨hs, ht⟩) 1 ⟨0, one_pow _⟩ p ht'
  exact ⟨b.left q, hle (e.le hq).1, Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

theorem dense_torsion_and_eq_one :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℕ), l.Prime → (l : K) ≠ 0 → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) ∧ ∀ f : P.A ⟶ P.A, (∀ (j : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), x ^ l ^ j = 1 → x ≫ f = 1) → f = 1 := by
  intro h1 _ K _ _ P l hl hlK
  have hD := dense_torsion h1.ample h1.kerPow h1.irred K P l hl.two_le hlK
  refine ⟨hD, fun f hf => Over.OverMorphism.ext ?_⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P.isAb.proper
  let g : P.A ⟶ P.A := 1
  suffices IsDominant (equalizer.ι f.left g.left) from
    ext_of_isDominant_of_isSeparated P.A.hom ((Over.w f).trans (Over.w g).symm) (equalizer.ι f.left g.left)
      (equalizer.condition _ _)
  refine ⟨Dense.mono (fun y hy => ?_) hD⟩
  obtain ⟨x, ⟨j, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hy
  have hxy : x.left ≫ f.left = x.left ≫ g.left :=
    congrArg CommaMorphism.left ((hf j x hx).trans (MonObj.comp_one x).symm)
  refine ⟨equalizer.lift x.left hxy q, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]

end GlobalTheory.PrimePowerTorsion
