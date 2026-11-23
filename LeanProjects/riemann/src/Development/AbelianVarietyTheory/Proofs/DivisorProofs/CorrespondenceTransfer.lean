import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.CorrespondenceTransfer

theorem corr_smul' {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (r : R) : m.Corr (r • x) (σ r • x') := fun c ↦ by
  simp only [LinearMap.smul_apply, smul_eq_mul, hx c, map_mul]

theorem transfer : ∀ (R : Subring ℂ) (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp ℂ)) [GrpObj A'] (p : A'.left ⟶ A.left)
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 ℂ) (𝟙 _) A' (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC →
    ∀ (n : ℕ) (eH : HdR A ≃ₗ[R] (Fin n → R)) (x y : Fin n → R) (k : FractionRing R),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) x = k • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) y →
    ∀ X Y, m.Corr (eH.symm x) X → m.Corr (eH.symm y) Y → X = j k • Y := by
  intro R j hj A _ A' _ p m hm n eH x y k hk X Y hX hY
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hs (Subtype.ext (by simpa using h0))
  have hsK : algebraMap R (FractionRing R) s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs

  have hlin : s • x = r • y := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (s • x - r • y) = 0 := by
      rw [map_sub, map_smul, map_smul, hk, ← algebraMap_smul (FractionRing R) s,
        ← algebraMap_smul (FractionRing R) r, smul_smul,
        show algebraMap R (FractionRing R) s * (algebraMap R (FractionRing R) r / algebraMap R (FractionRing R) s)
          = algebraMap R (FractionRing R) r by field_simp, sub_self]
    by_contra hne
    exact GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero (K := FractionRing R) inferInstance (sub_ne_zero.2 hne) h1
  have e1 : m.Corr (eH.symm (s • x)) (algebraMap R ℂ s • X) := by
    rw [map_smul]; exact corr_smul' hX s
  have e2 : m.Corr (eH.symm (s • x)) (algebraMap R ℂ r • Y) := by
    rw [hlin, map_smul]; exact corr_smul' hY r
  have heq := hm.unique e1 e2
  have hjk : j (algebraMap R (FractionRing R) r / algebraMap R (FractionRing R) s) = (r : ℂ) / s := by
    rw [map_div₀, hj, hj]
  rw [hjk]
  have hs' : algebraMap R ℂ s = (s : ℂ) := rfl
  have hr' : algebraMap R ℂ r = (r : ℂ) := rfl
  rw [hs', hr'] at heq
  rw [div_eq_inv_mul, mul_smul, ← heq, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end GlobalTheory.Div.CorrespondenceTransfer
