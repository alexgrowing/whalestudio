import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpFunctionalSymm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.IdxRat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.IdxNorm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SgnEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SgnLam
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.TestEx

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem ab_mul_idx {F : Type} [Field F] [NumberField F] (a b : (A F)ˣ) : ab (a * b) = ab a * ab b := by
  unfold ab
  rw [map_mul]
  rfl

private theorem ab_one {F : Type} [Field F] [NumberField F] : ab (1 : (A F)ˣ) = 1 := by
  unfold ab
  rw [map_one]
  rfl

private theorem ab_diag {F : Type} [Field F] [NumberField F] (k : Fˣ) : ab (IdeleGroup.diagonal F k) = 1 := by
  unfold ab
  rw [IdeleGroup.ideleModule_diagonal]
  rfl

private theorem idx_unique {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {δ : F} (hδ : δ ≠ 0)
    {b : (A F)ˣ} {c c' : ℂ} (h : IsIdx δ (b : A F) c) (h' : IsIdx δ (b : A F) c') : c = c' :=
  (idxEx F δ hδ b).unique h h'

private theorem idx_sgn {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {δ : F} (hδ : δ ≠ 0)
    (hneg : ∀ φ : F →+* ℝ, φ δ < 0) {a : (A F)ˣ} (ha : IsSgn a) (b : (A F)ˣ) {c : ℂ}
    (h : IsIdx δ (b : A F) c) : IsIdx δ ((a * b : (A F)ˣ) : A F) (-c) := by
  obtain ⟨c', hc', -⟩ := idxEx F δ hδ (a * b)
  obtain ⟨g, hg, hne, -⟩ := testEx F
  have h1 := hc' ⟨_, hg⟩
  have h2 := h ⟨_, hg⟩
  have h3 := sgnLam F δ hneg a b ha g
  simp only at h1 h2
  rw [h1, h2] at h3
  have : c' = -c := by
    apply mul_right_cancel₀ hne
    rw [h3]
    ring
  rwa [this] at hc'

private theorem idx_ker {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (D : Dat F E) (hδ : D.δ ≠ 0) {b : (A F)ˣ} {t : F} {z : (A E)ˣ} (ht : t ≠ 0)
    (hb : (b : A F) = rt t * (ideleNorm F E z : (A F)ˣ)) :
    IsIdx D.δ (b : A F) (((ab b)⁻¹ ^ 2 : ℝ) : ℂ) := by
  have h := idxNorm F E D (rt t) 1 z (idxRat F D.δ hδ t ht)
  have hd : b = IdeleGroup.diagonal F (Units.mk0 t ht) * ideleNorm F E z := by
    ext1
    rw [hb, Units.val_mul]
    rfl
  have hab : ab b = ab (ideleNorm F E z) := by
    rw [hd, ab_mul_idx, ab_diag, one_mul]
  rw [hb, hab]
  simpa using h

theorem UpperTheory.ConvolutionTheory.R2.C.idxEta :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] (D : Dat F E) (η : (A F)ˣ →* ℂˣ), (∀ a, η a ^ 2 = 1) →
    (∀ a, η a = 1 → ∃ (t : F) (z : (A E)ˣ), t ≠ 0 ∧ (a : A F) = rt t * (ideleNorm F E z : (A F)ˣ)) →
    ∀ b : (A F)ˣ, IsIdx D.δ (b : A F) (((η b : ℂˣ) : ℂ) * (((ab b)⁻¹ ^ 2 : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ _ D η hsq hker b
  have hδ : D.δ ≠ 0 := by
    intro h0
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  have step1 : ∀ b : (A F)ˣ, η b = 1 → IsIdx D.δ (b : A F) (((ab b)⁻¹ ^ 2 : ℝ) : ℂ) := by
    intro b hb
    obtain ⟨t, z, ht, hz⟩ := hker b hb
    exact idx_ker D hδ ht hz
  obtain ⟨a, hsgn, haa, hab⟩ := sgnEx F
  have step2 : ∀ (b : (A F)ˣ) (c : ℂ), IsIdx D.δ (b : A F) c → IsIdx D.δ ((a * b : (A F)ˣ) : A F) (-c) :=
    fun b c h => idx_sgn hδ D.neg hsgn b h
  have hηa : η a ≠ 1 := by
    intro h1
    have i1 := step1 a h1
    have i2 := step2 1 _ (step1 1 (map_one η))
    rw [mul_one] at i2
    have := idx_unique hδ i1 i2
    rw [hab, ab_one] at this
    norm_num at this
  have neg_of_ne : ∀ x : ℂˣ, x ^ 2 = 1 → x ≠ 1 → x = -1 := by
    intro x hx hne
    have hx' : (x : ℂ) * x = 1 := by
      rw [← Units.val_mul, ← sq, hx, Units.val_one]
    rcases mul_self_eq_one_iff.1 hx' with h | h
    · exact absurd (Units.ext h) hne
    · exact Units.ext (by simpa using h)
  by_cases hb : η b = 1
  · rw [hb]
    simpa using step1 b hb
  · have hb' := neg_of_ne _ (hsq b) hb
    have ha' := neg_of_ne _ (hsq a) hηa
    have h1 : η (a * b) = 1 := by
      rw [map_mul, hb', ha']
      simp
    have i := step2 _ _ (step1 (a * b) h1)
    have e : a * (a * b) = b := by
      rw [← mul_assoc, haa, one_mul]
    rw [e, ab_mul_idx, hab, one_mul] at i
    rw [hb']
    simpa using i
