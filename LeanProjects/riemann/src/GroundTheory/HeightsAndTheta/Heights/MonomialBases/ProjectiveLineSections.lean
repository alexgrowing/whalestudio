import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry NumberField TensorProduct GroundTheory.Arith.SchemeCoh Matrix
open ProjScheme SectionsLatticeFS

noncomputable section

namespace ProjectiveLineSections

def expo (n k : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (n - k)

@[simp] lemma expo_zero (n k : ℕ) : expo n k 0 = k := by simp [expo]

@[simp] lemma expo_one (n k : ℕ) : expo n k 1 = n - k := by simp [expo]

lemma degree_fin_two (a : Fin 2 →₀ ℕ) : a.degree = a 0 + a 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

lemma degree_expo {n k : ℕ} (hk : k ≤ n) : (expo n k).degree = n := by
  rw [degree_fin_two, expo_zero, expo_one]; omega

def expoEquiv (n : ℕ) : Fin (n + 1) ≃ {a : Fin 2 →₀ ℕ // a.degree = n} where
  toFun k := ⟨expo n k, degree_expo (Nat.lt_succ_iff.mp k.2)⟩
  invFun a := ⟨a.1 0, by have := degree_fin_two a.1; omega⟩
  left_inv k := Fin.ext (expo_zero n k)
  right_inv a := by
    have h := degree_fin_two a.1
    refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
    fin_cases i
    · simp
    · simp; omega

def monoSection (n : ℕ) (k : Fin (n + 1)) : (self (𝓞 ℚ) 1).H0 (twistN (𝓞 ℚ) 1 n) :=
  polySection (monomial_mem_grading (A := 𝓞 ℚ) (expo n k) (degree_expo (Nat.lt_succ_iff.mp k.2)))

def monoBasis (hb : MonomialBasis.Statement.{0}) (n : ℕ) :
    Module.Basis (Fin (n + 1)) (𝓞 ℚ) ((self (𝓞 ℚ) 1).H0 (twistN (𝓞 ℚ) 1 n)) :=
  (hb (𝓞 ℚ) 1 n).choose.reindex (expoEquiv n).symm

theorem monoBasis_apply (hb : MonomialBasis.Statement.{0}) (n : ℕ) (k : Fin (n + 1)) :
    monoBasis hb n k = monoSection n k := by
  simp only [monoBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  exact (hb (𝓞 ℚ) 1 n).choose_spec (expoEquiv n k)

theorem finrank_sections_projectiveLine (hb : MonomialBasis.Statement.{0}) (n : ℕ) :
    Module.finrank (𝓞 ℚ) ((self (𝓞 ℚ) 1).H0 (twistN (𝓞 ℚ) 1 n)) = n + 1 := by
  rw [Module.finrank_eq_card_basis (monoBasis hb n), Fintype.card_fin]

variable (hfin : SectionsLattice.Finite.Statement) (hl2 : SectionsLattice.L2.Statement)
  (hflat : PNFlat.Statement.{0}) (hred : PNReduced.Statement.{0})
  (hf : FSContinuousFrame.Statement.{0}) (hc : FSNormConj.Statement.{0})
  (hs : FSFullSupport.Statement) (hci : FSConjInvariant.Statement)

abbrev bundle (n : ℕ) : HermitianBundle ℚ :=
  fsSectionsHermitian (K := ℚ) (N := 1) hfin hl2 hflat hred hf hc hs hci n

theorem inner_eq (n : ℕ) (σ : ℚ →+* ℂ) (t u : Fibre σ ((self (𝓞 ℚ) 1).H0 (twistN (𝓞 ℚ) 1 n))) :
    ((bundle hfin hl2 hflat hred hf hc hs hci n).metric.form σ).inner t u =
      fubiniStudyL2Inner ℚ n (CP.fsMeasure 1) σ t u := by
  have := (hfin ℚ 1 (self (𝓞 ℚ) 1) (hflat (𝓞 ℚ) 1) (fsBundle hf hc n).L (fsBundle hf hc n).invertible).1
  have := (hfin ℚ 1 (self (𝓞 ℚ) 1) (hflat (𝓞 ℚ) 1) (fsBundle hf hc n).L (fsBundle hf hc n).invertible).2
  rw [← l2Inner_fubiniStudyBundle hf hc n (CP.fsMeasure 1) σ t u]
  exact Classical.choose_spec (hl2 ℚ 1 (self (𝓞 ℚ) 1) (hflat (𝓞 ℚ) 1) (hred (𝓞 ℚ) 1)
    (fsBundle hf hc n) (fsPointMeasures ℚ 1 hs hci)) σ t u

lemma fubiniStudy_inner_monomial (hm : L2MonomialOrthogonality.Statement) (n : ℕ) (σ : ℚ →+* ℂ) (a b : Fin 2 →₀ ℕ)
    (ha : a.degree = n) (hb : b.degree = n) :
    fubiniStudyL2Inner ℚ n (CP.fsMeasure 1) σ
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] polySection (monomial_mem_grading (A := 𝓞 ℚ) a ha))
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] polySection (monomial_mem_grading (A := 𝓞 ℚ) b hb)) =
      if a = b then
        (((∏ i, ((a i).factorial : ℝ)) * (Nat.factorial 1) / (n + 1).factorial : ℝ) : ℂ)
      else 0 := by
  subst ha
  exact hm ℚ 1 σ a b hb

theorem inner_mono (hm : L2MonomialOrthogonality.Statement) (n : ℕ) (σ : ℚ →+* ℂ) (k l : Fin (n + 1)) :
    ((bundle hfin hl2 hflat hred hf hc hs hci n).metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] monoSection n k) ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] monoSection n l) =
      if k = l then
        ((((k : ℕ).factorial * (n - k).factorial : ℕ) / (n + 1).factorial : ℝ) : ℂ)
      else 0 := by
  refine ((inner_eq hfin hl2 hflat hred hf hc hs hci n σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] monoSection n k)
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] monoSection n l)).trans
    (fubiniStudy_inner_monomial hm n σ (expo n k) (expo n l) (degree_expo (Nat.lt_succ_iff.mp k.2))
      (degree_expo (Nat.lt_succ_iff.mp l.2)))).trans ?_
  have hinj : expo n k = expo n l ↔ k = l := by
    refine ⟨fun h ↦ Fin.ext ?_, fun h ↦ h ▸ rfl⟩
    simpa using congrArg (fun a ↦ a 0) h
  by_cases hkl : k = l
  · simp [hkl, Fin.prod_univ_two]
  · simp [hinj, hkl]

def Degree.Statement : Prop :=
  ∀ (hfin : SectionsLattice.Finite.Statement) (hl2 : SectionsLattice.L2.Statement)
    (hflat : PNFlat.Statement.{0}) (hred : PNReduced.Statement.{0})
    (hf : FSContinuousFrame.Statement.{0}) (hc : FSNormConj.Statement.{0})
    (hs : FSFullSupport.Statement) (hci : FSConjInvariant.Statement) (n : ℕ),
    (bundle hfin hl2 hflat hred hf hc hs hci n).arithDegree =
      (1 / 2) * Real.log (((n + 1).factorial : ℝ) ^ (n + 1) /
        ∏ k ∈ Finset.range (n + 1), ((k.factorial * (n - k).factorial : ℕ) : ℝ))

theorem Degree.proof (hb : MonomialBasis.Statement.{0}) (hm : L2MonomialOrthogonality.Statement) :
    Degree.Statement := by
  intro hfin hl2 hflat hred hf hc hs hci n
  set B := bundle hfin hl2 hflat hred hf hc hs hci n
  let s : Fin (n + 1) → B.carrier := fun k ↦ monoSection n k
  have hs' : s = ⇑(monoBasis hb n) := funext fun k ↦ (monoBasis_apply hb n k).symm
  have hli : LinearIndependent (𝓞 ℚ) s := hs' ▸ (monoBasis hb n).linearIndependent
  have hcard : Fintype.card (Fin (n + 1)) = Module.finrank (𝓞 ℚ) B.carrier := by
    rw [Fintype.card_fin]; exact (finrank_sections_projectiveLine hb n).symm
  have hspan : Submodule.span (𝓞 ℚ) (Set.range s) = ⊤ := hs' ▸ (monoBasis hb n).span_eq
  set c : ℕ → ℝ := fun k ↦ ((k.factorial * (n - k).factorial : ℕ) : ℝ)
  set F : ℝ := ((n + 1).factorial : ℝ)
  have hgram : ∀ σ : ℚ →+* ℂ, gramDet B.metric σ s = ∏ k : Fin (n + 1), (c k / F) := by
    intro σ
    have : gram ℂ (fun k ↦ fibreVec B.metric σ (s k)) =
        diagonal fun k : Fin (n + 1) ↦ (((c k / F : ℝ)) : ℂ) := by
      ext k l
      rw [gram_apply, diagonal_apply]
      exact inner_mono hfin hl2 hflat hred hf hc hs hci hm n σ k l
    rw [gramDet, this, det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  have hP : ∏ k : Fin (n + 1), c k = ∏ k ∈ Finset.range (n + 1), c k :=
    Fin.prod_univ_eq_prod_range c (n + 1)
  have hPpos : 0 < ∏ k ∈ Finset.range (n + 1), c k :=
    Finset.prod_pos fun k _ ↦ by simp only [c]; positivity
  have hFpos : 0 < F := by simp only [F]; positivity
  rw [HermitianBundle.arithDegree, arithDegree_eq B.metric hli hcard, degreeWith, hspan,
    Nat.card_unique, Nat.cast_one, Real.log_one,
    Fintype.sum_subsingleton _ (Rat.castHom ℂ), hgram, Finset.prod_div_distrib, hP,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.log_div hPpos.ne' (pow_pos hFpos _).ne', Real.log_div (pow_pos hFpos _).ne' hPpos.ne',
    Real.log_pow]
  push_cast
  ring

theorem degree_zero (hb : MonomialBasis.Statement.{0}) (hm : L2MonomialOrthogonality.Statement) :
    (bundle hfin hl2 hflat hred hf hc hs hci 0).arithDegree = 0 := by
  rw [Degree.proof hb hm hfin hl2 hflat hred hf hc hs hci 0]
  norm_num

theorem degree_one (hb : MonomialBasis.Statement.{0}) (hm : L2MonomialOrthogonality.Statement) :
    (bundle hfin hl2 hflat hred hf hc hs hci 1).arithDegree = Real.log 2 := by
  rw [Degree.proof hb hm hfin hl2 hflat hred hf hc hs hci 1]
  norm_num [Finset.prod_range_succ, Nat.factorial]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

end ProjectiveLineSections

end

end GroundTheory.Heights₂.Heights
