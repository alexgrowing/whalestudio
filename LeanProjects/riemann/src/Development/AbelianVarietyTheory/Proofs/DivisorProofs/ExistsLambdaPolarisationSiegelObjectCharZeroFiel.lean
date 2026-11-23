import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqOf_of_dim (hL : Out.Laws) (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R]
    [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c₀ : SiegPre h k ζ (spMap β))
    (hd : SmoothOfRelativeDimension h c₀.A.hom) (hc₀ : c₀.Principal) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c₀.A.left),
      (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧
        SqOf P c₀ (spMap (algebraMap R R₁)) φ := by
  have h2 : IsUnit ((2 : ℕ) : R) := by
    have := (IsUnit.mk0 ((2 : ℕ) : ℚ) (by norm_num)).map (algebraMap ℚ R)
    rwa [map_natCast] at this
  obtain ⟨R', _, _, ⟨f₁, e₁, l₁⟩, H₁⟩ := GlobalTheory.T.exists_finiteEtale_cover_constant_torsion R c₀.A h 2 c₀.ab hd h2
  obtain ⟨c', m', hc'⟩ := pull_sieg (spMap ((algebraMap R R').comp β)) (spMap (algebraMap R R'))
    (SiegelRingChange.spMap_comp' _ _).symm c₀ hc₀
  have m'' := m'
  obtain ⟨φ', -, g', -⟩ := m''
  obtain ⟨i₀, hi₀⟩ := H₁ c'.A φ' g'
  letI : Algebra ℚ R' := ((algebraMap R R').comp (algebraMap ℚ R)).toAlgebra
  haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  obtain ⟨R₁, _, _, ⟨f₂, e₂, l₂⟩, H₂⟩ := GlobalTheory.T.exists_symmetric_linearisation_square_diagonalBundle hL h k o ζ R' _ c' h i₀ hc'
  obtain ⟨c₁, m₁, hc₁⟩ := pull_sieg (spMap ((algebraMap R' R₁).comp ((algebraMap R R').comp β)))
    (spMap (algebraMap R' R₁)) (SiegelRingChange.spMap_comp' _ _).symm c' hc'
  have m₁' := m₁
  obtain ⟨φ₁, φ₂, g₁, sq₁, w₁, -⟩ := m₁'
  obtain ⟨i, hi, li⟩ := exists_pull_labels g₁ 2 i₀ hi₀
  letI : Algebra ℚ R₁ := ((algebraMap R' R₁).comp (algebraMap ℚ R')).toAlgebra
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R' R₁
  obtain ⟨u, j, huj⟩ := H₂ c₁.A φ₁ i _ g₁ hi rfl
  obtain ⟨p₁, p₂, p₃, p₄⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ c₁.A 2 c₁.ab (isUnit_two_sections R₁)
  have hψ : ∀ {T : Over (Sp R₁)} (x : T ⟶ c₁.A), x ≫ ((𝟙 c₁.A) ^ 2 : c₁.A ⟶ c₁.A) = x ^ 2 := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  have two : ∀ a : Multiplicative (Fin (2 * h) → ZMod 2), a ^ 2 = 1 := fun a => by
    apply Multiplicative.toAdd.injective
    funext x
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize (Multiplicative.toAdd a x) = y
    revert y; decide
  have hD : (c'.diag.pull φ₁).IsLB := pull_isLB (diag_isLB c') _
  obtain ⟨M, hM, iM, sM⟩ := GlobalTheory.T.exists_descent_symmetric_linearised_bundle _ c₁.A c₁.A ((𝟙 c₁.A) ^ 2) _ i (lbPow (c'.diag.pull φ₁) 2)
    (GlobalTheory.isLB_lbPow hD 2) p₁ p₂ p₃ p₄ (fun a => by rw [hψ, ← map_pow, two, map_one])
    (fun K _ _ t => ⟨fun x => by rw [hψ]; exact (li K t).1 x, (li K t).2⟩) u j huj
  have iM' := (GlobalTheory.lbIso_lbPow (diag_iso sq₁ w₁) 2).trans (GlobalTheory.isLB_lbPow (diag_isLB c₁) 2) (GlobalTheory.isLB_lbPow hD 2)
    (pull_isLB hM _) iM
  have hd₁ : SmoothOfRelativeDimension h c₁.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (g₁.comp g').1 hd
  obtain ⟨P, φ, hP⟩ := GlobalTheory.T.exists_principalPolarization_symmetric_squareRoot hL h k o ζ R₁ _ c₁ M hc₁ hd₁ hM
    (GlobalTheory.T.lam_iso_of_doubling_pullback_eq_diagonal_sq hL h k o ζ R₁ _ c₁ M hc₁ hM iM') sM
  obtain ⟨ψ, hψ'⟩ := sqOf_of_pb hP (pb_comp m' m₁)
  letI : Algebra R R₁ := ((algebraMap R' R₁).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' R₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨R₁, inferInstance, inferInstance, P, ψ,
    ⟨Module.Finite.trans R' R₁, Algebra.Etale.comp R R' R₁, Module.FaithfullyFlat.trans R R' R₁⟩, ?_⟩
  have e : spMap (algebraMap R R₁) = 𝟙 _ ≫ spMap (algebraMap R' R₁) ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, ← SiegelRingChange.spMap_comp']
  rw [e]; exact hψ'

end GlobalTheory.SiegelSqrtField
end

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqrt_field : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s), c.Principal →
    ∀ (K : Type) [Field K] [CharZero K] (f : Sp K ⟶ S), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra K R₁),
      Module.Finite K R₁ ∧ Nontrivial R₁ ∧ ∃ (P : PolAV (Sp R₁)) (α : P.A.left ⟶ c.A.left) (α₂ : (G2 P.A).left ⟶ (G2 c.A).left),
        IsGrpPullback P.A c.A (spMap (algebraMap K R₁) ≫ f) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ P.A P.L) (c.P.pull α₂) := by
  intro h k o _ ζ S s c hc K _ _ f
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, f ≫ s = spMap β :=
    ⟨(Spec.preimage (f ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨c₀, m₀, hc₀⟩ := pull_sieg (spMap β) f hβ c hc
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K c₀.A c₀.ab
  let c₁ : SiegPre g 2 (0 : K) (spMap (RingHom.id K)) :=
    { A := c₀.A, ab := c₀.ab, P := c₀.P, isLB := c₀.isLB, rig₁ := c₀.rig₁, rig₂ := c₀.rig₂, symm := c₀.symm,
      lev := fun _ => 1, lev_add := fun _ _ => (mul_one 1).symm, lev_tors := fun _ => one_pow _,
      geom := fun k _ _ x β' z _ hz => absurd (hz.trans (map_zero β')) z.ne_zero }
  have hc₁ : c₁.Principal := hc₀
  obtain ⟨R₁, _, _, P, φ, ⟨hfin, -, hff⟩, hP⟩ :=
    exists_sqOf_of_dim GlobalTheory.allSixLaws.1 g 2 K 0 K (RingHom.id K) c₁ hg hc₁
  obtain ⟨χ, χ₂, hχ, hs, hw, -⟩ := m₀
  obtain ⟨hφ, -, φ₂, hs', hw'⟩ := hP
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  refine ⟨R₁, inferInstance, inferInstance, hfin, ?_, P, φ ≫ χ, φ₂ ≫ χ₂, hφ.comp hχ, ⟨?_, ?_⟩, ?_⟩
  · haveI := Module.FaithfullyFlat.lTensor_nontrivial K R₁ K
    exact (TensorProduct.lid K R₁).injective.nontrivial
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans lam (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull φ₂ hw)).trans
      lam (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB χ₂ φ₂)

end GlobalTheory.SiegelSqrtField
