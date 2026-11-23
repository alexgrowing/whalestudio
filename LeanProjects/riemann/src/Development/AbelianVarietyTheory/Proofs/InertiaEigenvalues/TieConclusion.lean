import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SelmerSumLargePrime

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.Proof.QuotientLengthInfimum

open GlobalTheory.IndefiniteRowSideFullHecke

theorem length_quot_eq_iInf {O : Type} [CommRing O] [IsPrincipalIdealRing O] (I : Ideal O) :
    Module.length O (O ⧸ I) = ⨅ x ∈ I, Module.length O (O ⧸ Ideal.span {x}) := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem _).2 hx
    exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
      Ideal.span_singleton_generator I
    refine iInf₂_le_of_le (Submodule.IsPrincipal.generator I)
      (Submodule.IsPrincipal.generator_mem I) ?_
    rw [hg]

theorem mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X) (y : O) :
    y ∈ ccAt T Z π ↔ ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = y := by
  have hs : Function.Surjective ((Pi.evalRingHom (fun _ : X => O) π).comp T.val.toRingHom) :=
    fun a => ⟨algebraMap O T a, by simp⟩
  unfold ccAt
  rw [Ideal.mem_map_iff_of_surjective _ hs]
  rfl

theorem div_le_iff_lengths (e c s h v q : ℕ∞) (he0 : e ≠ 0) (he : e ≠ ⊤) :
    ((c : ℝ≥0∞) / (e : ℝ≥0∞) ≤ (s : ℝ≥0∞) / (e : ℝ≥0∞) + (h : ℝ≥0∞) + (v : ℝ≥0∞) + (q : ℝ≥0∞) / (e : ℝ≥0∞)) ↔
      c ≤ s + e * h + e * v + q := by
  have he0' : (e : ℝ≥0∞) ≠ 0 := by simpa using he0
  have he' : (e : ℝ≥0∞) ≠ ⊤ := by simpa using he
  rw [← ENat.toENNReal_le, ← ENNReal.mul_le_mul_iff_right he0' he']
  simp only [mul_add, ENNReal.mul_div_cancel he0' he', ENat.toENNReal_add, ENat.toENNReal_mul]

theorem toENNReal_sum {ι : Type} (s : Finset ι) (f : ι → ℕ∞) :
    ((∑ a ∈ s, f a : ℕ∞) : ℝ≥0∞) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ENat.toENNRealRingHom f s

section Hyp

end Hyp

section Terms

variable (D : D7) (i : D.nd.Loc)

theorem ramLen_ne : SelmerSumLargePrime.ramLen D i ≠ 0 ∧ SelmerSumLargePrime.ramLen D i ≠ ⊤ := by
  have h := BaseSizes.vO_l D i
  unfold BaseSizes.vO BaseSizes.nlen at h
  change ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) / ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) = 1 at h
  constructor
  · intro h0; rw [h0] at h; simp at h
  · intro h0; rw [h0] at h; simp at h

theorem vCC_eq (π : D.nd.X i) :
    BaseSizes.vCC D i π = (SelmerSumLargePrime.ccLen D i π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.vCC BaseSizes.vO BaseSizes.nlen SelmerSumLargePrime.ccLen
  change ⨅ f ∈ D.nd.cc i, _ / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) = _
  apply le_antisymm
  · set I := ccAt (D.nd.T i) (D.nd.Z i) π with hI
    have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I := Ideal.span_singleton_generator I
    obtain ⟨f, hf, hfx⟩ := (mem_ccAt _ _ π _).1 (Submodule.IsPrincipal.generator_mem I)
    refine iInf₂_le_of_le f hf ?_
    rw [hfx, hg]
  · refine le_iInf₂ fun f hf => ?_
    refine ENNReal.div_le_div_right ?_ _
    rw [ENat.toENNReal_le, length_quot_eq_iInf]
    exact iInf₂_le _ ((mem_ccAt _ _ π _).2 ⟨f, hf, rfl⟩)

theorem sPi_eq (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    BaseSizes.sPi D i π ρ = (SelmerSumLargePrime.selLen D i ρ π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := rfl

theorem shaSum_eq : BaseSizes.shaSum D i = (SelmerSumLargePrime.shaSum D i : ℝ≥0∞) := by
  unfold BaseSizes.shaSum SelmerSumLargePrime.shaSum
  rw [toENNReal_sum]

theorem vClass_eq :
    BaseSizes.vClass D i = (((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) : ℝ≥0∞) := by
  unfold BaseSizes.vClass hE
  simp

theorem zetaP_eq (P : HeightOneSpectrum (𝓞 D.host.E)) : BaseSizes.zetaP D i P = SelmerSumLargePrime.zetaP D i P := rfl

theorem epsQ_eq : BaseSizes.epsQ D i = (SelmerSumLargePrime.twistLen D i : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.epsQ SelmerSumLargePrime.twistLen BaseSizes.vO BaseSizes.nlen
  rw [ENat.toENNReal_mul, toENNReal_sum, mul_div_assoc, div_eq_mul_inv (∑ _ ∈ _, _), Finset.sum_mul]
  rfl

theorem conclusion_iff (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    (BaseSizes.vCC D i π ≤ BaseSizes.sPi D i π ρ + BaseSizes.shaSum D i + BaseSizes.vClass D i + BaseSizes.epsQ D i) ↔
      SelmerSumLargePrime.ccLen D i π ≤ SelmerSumLargePrime.selLen D i ρ π + SelmerSumLargePrime.ramLen D i * SelmerSumLargePrime.shaSum D i +
        SelmerSumLargePrime.ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + SelmerSumLargePrime.twistLen D i := by
  rw [vCC_eq, sPi_eq, shaSum_eq, vClass_eq, epsQ_eq]
  exact div_le_iff_lengths _ _ _ _ _ _ (ramLen_ne D i).1 (ramLen_ne D i).2

end Terms

def LengthBoundLoc (D : D7) (L : SizeData₂ D) (i : D.nd.Loc) : Prop :=
  LevelStarExponents.lStar L < (D.nd.l i : ℝ) → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    D.nd.l i ∉ SelmerSumLargePrime.excPrimes L →
    HG D.nd D.naut i →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i), SelmerSumLargePrime.IsBlockSplit D i (r π) ρ →
      SelmerSumLargePrime.ccLen D i π ≤ SelmerSumLargePrime.selLen D i ρ π + SelmerSumLargePrime.ramLen D i * SelmerSumLargePrime.shaSum D i +
        SelmerSumLargePrime.ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + SelmerSumLargePrime.twistLen D i

def TiedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (a : Fm.Ix x) (i : (Fm.D x a).nd.Loc), BaseSizes.WeightTie (Fm.D x a) i

end GlobalTheory.Proof.QuotientLengthInfimum

end
