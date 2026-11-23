import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCliffordLowestVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordVectorSpinWeightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjointStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightModuleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sl2SquareKillsVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinTensorHighestWeightStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

noncomputable section

namespace GlobalTheory.CompanionTheory.SpinPRV

open ReciprocityTheory.ChartRestriction.DS.HW in

lemma tens_single {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (G : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) (z : Z) (i : ι) :
    tensAct A (matrixFamilyDual G) a b (WithLp.toLp 2 (Pi.single i z) : PiLp 2 (fun _ : ι => Z)) =
      (WithLp.toLp 2 (Pi.single i (A a b z)) : PiLp 2 (fun _ : ι => Z)) -
        ∑ j, G a b i j • (WithLp.toLp 2 (Pi.single j z) : PiLp 2 (fun _ : ι => Z)) := by
  ext k
  simp only [ReciprocityTheory.ChartRestriction.DS.HW.tensAct, ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual]
  by_cases hk : k = i
  · subst hk
    simp [Pi.single_apply, Finset.sum_apply, Matrix.neg_apply, Matrix.transpose_apply, sub_eq_add_neg]
  · simp [Pi.single_apply, hk, Finset.sum_apply, Matrix.neg_apply, Matrix.transpose_apply]

open ReciprocityTheory.ChartRestriction.DS.HW in
lemma tens_apply {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) (x : PiLp 2 (fun _ : ι => Z)) (i : ι) :
    tensAct A D a b x i = A a b (x i) + ∑ j, D a b i j • x j := by
  simp [ReciprocityTheory.ChartRestriction.DS.HW.tensAct]

lemma toLp_eq_sum_single {Z : Type} [NormedAddCommGroup Z] {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Z) :
    (WithLp.toLp 2 f : PiLp 2 (fun _ : ι => Z)) = ∑ i, (WithLp.toLp 2 (Pi.single i (f i)) : PiLp 2 (fun _ : ι => Z)) := by
  ext k
  simp [Pi.single_apply]

private theorem tensAct_tensAct_apply {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ) (a b c d : Fin n)
    (x : PiLp 2 (fun _ : ι => Z)) (i : ι) :
    ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D a b (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D c d x) i =
      A a b (A c d (x i)) + ∑ k, D c d i k • A a b (x k) + ∑ k, D a b i k • A c d (x k) +
        ∑ k, (D a b * D c d) i k • x k := by
  rw [tens_apply, tens_apply]
  simp only [tens_apply, map_add, map_sum, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun k j => (D a b i j * D c d j k) • x k)]
  abel

private theorem kRel_tensAct_of_glRel {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ)
    (hA : Formalism.REAL.GlRel A) (hD : Formalism.REAL.GlRel D) :
    CompanionTheory.D.DSIC.KRel (fun _ => true) (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D) := by
  intro a b c d _ _
  apply LinearMap.ext
  intro x
  ext i
  have e1 : A a b (A c d (x i)) - A c d (A a b (x i)) =
      ((if b = c then A a d else 0) - (if d = a then A c b else 0)) (x i) := by
    have := LinearMap.congr_fun (hA a b c d) (x i)
    simpa [Module.End.mul_apply] using this
  have e2 : ∑ k, (D a b * D c d) i k • x k - ∑ k, (D c d * D a b) i k • x k =
      ∑ k, ((if b = c then D a d else 0) - (if d = a then D c b else 0)) i k • x k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← sub_smul, ← Matrix.sub_apply, hD a b c d]
  have hl : (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D a b * ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D c d -
      ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D c d * ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D a b) x i =
      (A a b (A c d (x i)) - A c d (A a b (x i))) +
        (∑ k, (D a b * D c d) i k • x k - ∑ k, (D c d * D a b) i k • x k) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, tensAct_tensAct_apply]
    abel
  rw [hl, e1, e2]
  split_ifs <;> simp [tens_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib] <;> abel

private theorem kUnit_tensAct_of_adjoint {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ)
    (hA : ∀ a b (x y : Z), inner ℂ (A a b x) y = inner ℂ x (A b a y))
    (hD : ∀ a b i j, star (D a b i j) = D b a j i) :
    CompanionTheory.D.DSIC.KUnit (fun _ => true) (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D) := by
  intro a b _ x y
  simp only [PiLp.inner_apply, tens_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_add_distrib, hA, starRingEnd_apply, hD]
  congr 1
  exact Finset.sum_comm

private theorem glRel_ext1Dual {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Fin n → Fin n → Matrix ι ι ℂ) (hG : Formalism.REAL.GlRel G) :
    Formalism.REAL.GlRel (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual G) := by
  intro a b c d
  simp only [ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual, neg_mul_neg, ← Matrix.transpose_mul]
  rw [← Matrix.transpose_sub,
    show G c d * G a b - G a b * G c d = -(G a b * G c d - G c d * G a b) by abel, hG a b c d]
  split_ifs <;> simp [Matrix.transpose_sub] <;> abel

open ReciprocityTheory.ChartRestriction.DS.HW in
theorem assemble {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) (hc : IsCliff c)
    (q : ι → ℂ) (hq0 : q ≠ 0) (hq1 : ∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q)
    (hq2 : ∀ a b, a < b → spinM c b a *ᵥ q = 0)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
    (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V) (hK : Formalism.REAL.GlRel Kf)
    (hKu : ∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) (hfd : FiniteDimensional ℂ S)
    (hst : ∀ a b, ∀ w ∈ S, Kf a b w ∈ S) (hvS : v ∈ S) (hv0 : v ≠ 0)
    (hv : Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v) :
    ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  classical
  have hdom : Antitone (wtR ν) :=
    GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable V Kf S (wtR ν) v hK hfd hst hvS hv0 hv
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (σ a) - rhoV n (σ a)) := by
    refine ⟨Tuple.sort (fun a => -(wtR ν a - rhoV n a)), ?_⟩
    intro x y hxy
    have := Tuple.monotone_sort (fun a => -(wtR ν a - rhoV n a)) hxy
    simp only [Function.comp] at this
    linarith
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨Z, iZ1, iZ2, iZ3, E, u, a0, hEgl, hEu, hu0, hu, hirr, ha0, haw, hah⟩ :=
    GlobalTheory.T.exists_highest_weight_module (fun a => wtR ν (σ a) - rhoV n (σ a)) hσ (-(((n : ℝ) - 1) / 2))
      (fun a => ⟨ν (σ a) + ((σ a : ℕ) : ℤ), by simp only [wtR, rhoV]; push_cast; ring⟩) σ
  have hay : ∀ y, E y y a0 = ((wtR ν y - rhoV n y : ℝ) : ℂ) • a0 := by
    intro y
    have := haw (σ.symm y)
    simpa using this
  have hadj : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → (E i j ^ 2) a0 = 0 := by
    intro i j hij
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hne : i ≠ j := ne_of_lt hlt
    refine GlobalTheory.T.sl2_square_kills_vector E hEgl hEu hne ha0 (hay i) (hay j) ⟨ν i - ν j - 1, ?_⟩ ?_ ?_
    · simp only [wtR, rhoV]; rw [hij]; push_cast; ring
    · have := hdom hlt.le
      simp only [wtR, rhoV] at this ⊢
      rw [hij]; push_cast; linarith
    · rcases lt_or_gt_of_ne (σ.symm.injective.ne hne) with h | h
      · left; simpa using hah _ _ h
      · right; simpa using hah _ _ h
  obtain ⟨φ, hφq, hφup, hφdiag⟩ := GlobalTheory.T.spin_tensor_highest_weight c hc q hq0 hq1 hq2 E hEgl (wtR ν) a0 hay hadj
  have hφsum : ∀ f : ι → ℂ, φ f = ∑ j, f j • φ (Pi.single j 1) := by
    intro f
    conv_lhs => rw [show f = ∑ j, f j • (Pi.single j 1 : ι → ℂ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, map_smul]
  have hcol : ∀ (M : Matrix ι ι ℂ) (i : ι), ∑ j, M j i • φ (Pi.single j 1) = φ (M *ᵥ Pi.single i 1) := by
    intro M i
    rw [hφsum (M *ᵥ Pi.single i 1)]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  let t : PiLp 2 (fun _ : ι => Z) := WithLp.toLp 2 (fun i => φ (Pi.single i 1))
  have hETt : ∀ a b i, ReciprocityTheory.ChartRestriction.DS.HW.tensAct E (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c)) a b t i =
      E a b (φ (Pi.single i 1)) - φ (spinM c a b *ᵥ Pi.single i 1) := by
    intro a b i
    rw [tens_apply, ← hcol]
    simp [ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual, t, sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]
  have hthigh : Formalism.REAL.KHighest (fun _ => true)
      (ReciprocityTheory.ChartRestriction.DS.HW.tensAct E (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c))) (wtR ν) t := by
    refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · ext i
      rw [hETt, hφdiag]
      simp [t]
    · ext i
      rw [hETt, hφup a b hab]
      simp
  have ht0 : t ≠ 0 := by
    intro h
    apply ha0
    rw [← hφq, hφsum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have : t j = 0 := by rw [h]; simp
    simp only [t, PiLp.toLp_apply] at this
    simp [this]
  have hDstar : ∀ a b i j, star (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c) a b i j) =
      ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c) b a j i := by
    intro a b i j
    have := congrFun (congrFun ((GlobalTheory.T.spin_gl_relations_adjoint c hc).2 a b) i) j
    simp only [ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual, Matrix.neg_apply, Matrix.transpose_apply, star_neg,
      Matrix.conjTranspose_apply] at this ⊢
    rw [this]
  obtain ⟨ψ, hψt, hψeq⟩ := CompanionTheory.D.DSIC.hHWMap n (fun _ => true) (PiLp 2 (fun _ : ι => Z)) V
    (ReciprocityTheory.ChartRestriction.DS.HW.tensAct E (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c))) Kf (wtR ν) t v S
    (kRel_tensAct_of_glRel E _ hEgl (glRel_ext1Dual _ (GlobalTheory.T.spin_gl_relations_adjoint c hc).1))
    (kUnit_tensAct_of_adjoint E _ hEu hDstar) (fun a b c d _ _ => hK a b c d) (fun a b _ x y => hKu a b x y)
    ht0 hthigh hv hfd (fun a b _ w hw => hst a b w hw) hvS
  have hkey : ∀ a b (z : Z) (i : ι), ψ (WithLp.toLp 2 (Pi.single i (E a b z))) =
      Kf a b (ψ (WithLp.toLp 2 (Pi.single i z))) + ∑ j, spinM c a b i j • ψ (WithLp.toLp 2 (Pi.single j z)) := by
    intro a b z i
    have h1 := hψeq a b rfl (WithLp.toLp 2 (Pi.single i z))
    rw [tens_single, map_sub, map_sum] at h1
    simp only [map_smul] at h1
    rw [← h1]
    abel
  have hsm : ∀ (r : ℂ) (z : Z) (i : ι), ψ (WithLp.toLp 2 (Pi.single i (r • z))) =
      r • ψ (WithLp.toLp 2 (Pi.single i z)) := by
    intro r z i
    rw [show (Pi.single i (r • z) : ι → Z) = r • Pi.single i z by ext k; simp [Pi.single_apply]]
    rw [WithLp.toLp_smul, map_smul]
  refine ⟨fun i => ψ (WithLp.toLp 2 (Pi.single i u)), ?_, ?_⟩
  · intro hx
    have hall : ∀ i, ψ (WithLp.toLp 2 (Pi.single i u)) = 0 := fun i => congrFun hx i
    let W : Submodule ℂ Z :=
      { carrier := {z | ∀ i, ψ (WithLp.toLp 2 (Pi.single i z)) = 0}
        add_mem' := by
          intro z1 z2 h1 h2 i
          simp only [Set.mem_setOf_eq] at h1 h2 ⊢
          rw [Pi.single_add, WithLp.toLp_add, map_add, h1 i, h2 i, add_zero]
        zero_mem' := by
          intro i
          simp
        smul_mem' := by
          intro r z h i
          simp only [Set.mem_setOf_eq] at h ⊢
          rw [hsm, h i, smul_zero] }
    have hstabW : ∀ (a b : Fin n), ∀ z ∈ W, E a b z ∈ W := by
      intro a b z hz
      have hz' : ∀ j, ψ (WithLp.toLp 2 (Pi.single j z)) = 0 := hz
      show ∀ i, ψ (WithLp.toLp 2 (Pi.single i (E a b z))) = 0
      intro i
      rw [hkey]
      simp only [hz', map_zero, smul_zero, Finset.sum_const_zero, add_zero]
    have huW : u ∈ W := hall
    have hWtop : W = ⊤ := hirr W hstabW huW
    apply hv0
    rw [← hψt]
    show ψ (WithLp.toLp 2 (fun i => φ (Pi.single i 1))) = 0
    rw [toLp_eq_sum_single, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hmem : φ (Pi.single i 1) ∈ W := by rw [hWtop]; trivial
    exact hmem i
  · have hy : ∀ a b, yF Kf c a b (fun i => ψ (WithLp.toLp 2 (Pi.single i u))) =
        fun i => ψ (WithLp.toLp 2 (Pi.single i (E a b u))) := by
      intro a b
      funext i
      rw [hkey]
      rfl
    refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · rw [hy, hu.1 a]
      funext i
      rw [hsm]
      rfl
    · rw [hy, hu.2 a b hab rfl]
      funext i
      simp

theorem spin_parthasarathy_rao_varadarajan : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
      (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V), Formalism.REAL.GlRel Kf →
      (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) →
      v ∈ S → v ≠ 0 → Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v →
      ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  intro n
  obtain ⟨ι, hF, hD, c, hc, q, hq0, hq⟩ := GlobalTheory.T.exists_clifford_lowest_vector n
  letI := hF
  letI := hD
  obtain ⟨h1, h2⟩ := GlobalTheory.T.clifford_vector_spin_weight c hc q hq
  refine ⟨ι, hF, hD, c, hc, ?_⟩
  intro V _ _ Kf S ν v hK hKu hfd hst hvS hv0 hv
  exact assemble c hc q hq0 h1 h2 V Kf S ν v hK hKu hfd hst hvS hv0 hv

end GlobalTheory.CompanionTheory.SpinPRV
