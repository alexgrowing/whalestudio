import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory
namespace NormLeFrob

theorem valuation_algebraMap_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) :
    A.valuation (algebraMap E Ω (x : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (algebraMap E Ω (x : E)) := (x.2).map (IsScalarTower.toAlgHom ℤ E Ω)
  have h2 : IsIntegral A (algebraMap E Ω (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact A.valuation_le_one y

noncomputable def toResidue {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) : 𝓞 E →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp (valuation_algebraMap_le_one A x)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }

theorem toResidue_eq_zero_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A w) (x : 𝓞 E) :
    toResidue A x = 0 ↔ x ∈ w.asIdeal := by
  rw [← hw x]
  simp only [toResidue, RingHom.coe_comp, Function.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem toResidue_isRoot {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (q : ℕ) (σ : G E Ω) (hσ : IsFrob A q σ) (x : 𝓞 E) :
    (X ^ q - X : (IsLocalRing.ResidueField A)[X]).IsRoot (toResidue A x) := by
  have hx := valuation_algebraMap_le_one A x
  have h := hσ.2 _ hx
  rw [AlgEquiv.commutes] at h
  have hmem : (⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ : A) ^ q
      - ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [← Valuation.map_neg]
    convert h using 2
    simp
  rw [← IsLocalRing.residue_eq_zero_iff] at hmem
  simp only [IsRoot, eval_sub, eval_pow, eval_X]
  have e : toResidue A x = IsLocalRing.residue A
      ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ := rfl
  rw [e, ← map_pow, ← map_sub]
  exact hmem

theorem normV_le_of_isFrob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ q : ℕ, 1 < q → ∀ σ : G E Ω, IsFrob A q σ → normV w ≤ q := by
  intro E Ω _ _ _ _ A w hw q hq σ hσ
  classical
  set k := IsLocalRing.ResidueField A
  set P : k[X] := X ^ q - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq
  let f : 𝓞 E ⧸ w.asIdeal →+* k :=
    Ideal.Quotient.lift w.asIdeal (toResidue A) (fun x hx => (toResidue_eq_zero_iff A w hw x).mpr hx)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (toResidue_eq_zero_iff A w hw x).mp ha
  let g : 𝓞 E ⧸ w.asIdeal → {y : k // y ∈ P.roots.toFinset} := fun a =>
    ⟨f a, by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Multiset.mem_toFinset, mem_roots hP0]
      exact toResidue_isRoot A q σ hσ x⟩
  have hg : Function.Injective g := fun a b h => hf (congrArg Subtype.val h)
  calc normV w = Nat.card (𝓞 E ⧸ w.asIdeal) := rfl
    _ ≤ Nat.card {y : k // y ∈ P.roots.toFinset} := Nat.card_le_card_of_injective g hg
    _ = P.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq k hq

end NormLeFrob
end GlobalTheory
