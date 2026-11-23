import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsArchSmoothOfContDiffChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ContDiffChartOfIsArchSmooth

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Fb

attribute [local instance 100] LieRing.ofAssociativeRing

variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ)

theorem sm_eq : TR.Sm E a = archSmooth E a :=
  le_antisymm (fun φ h => UpperTheory.isArchSmooth_of_contDiff_chart E a φ h) fun φ h => UpperTheory.contDiff_chart_of_isArchSmooth E a φ h

def smEq : TR.Sm E a ≃ₗ[ℂ] archSmooth E a := LinearEquiv.ofEq _ _ (sm_eq E a)

def uTR : UEnv E a →ₐ[ℝ] Module.End ℂ (TR.Sm E a) :=
  ((smEq E a).symm.conjAlgEquiv ℝ).toAlgHom.comp uAction

variable {E a}

@[simp] theorem coe_smEq (φ : TR.Sm E a) : (smEq E a φ).1 = φ.1 := rfl

@[simp] theorem coe_smEq_symm (φ : archSmooth E a) : ((smEq E a).symm φ).1 = φ.1 := rfl

theorem smEq_uTR (u : UEnv E a) (φ : TR.Sm E a) : smEq E a (uTR E a u φ) = uAction u (smEq E a φ) := rfl

theorem uTR_ι (X : TR.Lie E a) : uTR E a (UniversalEnvelopingAlgebra.ι ℝ (lieEq E a X)) = TR.lie E a X := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun g => ?_)
  set h := isExpLieAlgebra E a
  set Y := h.ofLie (lieEq E a X)
  have h1 := h.hasDerivAt_rightDeriv ((smEq E a φ).2 g) Y 1
  let L : ArchMatrix E a →L[ℝ] TR.Lie E a :=
    LinearMap.toContinuousLinearMap ((matEq E a).symm.toLinearMap : ArchMatrix E a →ₗ[ℝ] TR.Lie E a)
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (Y : ArchMatrix E a))) (Y : ArchMatrix E a) 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (Y : ArchMatrix E a) 0
  have h4 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  have e : L Y = X := (matEq E a).symm_apply_apply (Matrix.of X)
  have h2 := TR.hasDerivAt_curve φ g (fun t => (grpEq E a).symm (h.expG (t • Y))) X
    (by rw [zero_smul, h.expG_zero, map_one]) (h4.congr_deriv e)
  refine (uAction_ι_apply (lieEq E a X) (smEq E a φ) g).trans (h1.unique ?_)
  simp only [← infEmb_grpEq, MulEquiv.apply_symm_apply] at h2
  simp only [one_mul]
  exact h2

theorem uAction_ι_smEq (X : TR.Lie E a) (φ : TR.Sm E a) :
    uAction (UniversalEnvelopingAlgebra.ι ℝ (lieEq E a X)) (smEq E a φ) = smEq E a (TR.lie E a X φ) := by
  rw [← smEq_uTR, uTR_ι]

open Classical in

def genU (v : InfinitePlace E) (i j : Fin a) : UEnv E a :=
  UniversalEnvelopingAlgebra.ι ℝ (lieEq E a (TR.toL (Matrix.single i j (Pi.single v 1))))

theorem uTR_genU (v : InfinitePlace E) (i j : Fin a) : uTR E a (genU v i j) = TR.Eop v i j := uTR_ι _

private theorem ι_comm (X Y : Matrix (Fin a) (Fin a) (TR.Rinf E)) :
    UniversalEnvelopingAlgebra.ι ℝ (lieEq E a (TR.toL X)) * UniversalEnvelopingAlgebra.ι ℝ (lieEq E a (TR.toL Y)) -
      UniversalEnvelopingAlgebra.ι ℝ (lieEq E a (TR.toL Y)) * UniversalEnvelopingAlgebra.ι ℝ (lieEq E a (TR.toL X)) =
      UniversalEnvelopingAlgebra.ι ℝ (lieEq E a (TR.toL (X * Y))) -
        UniversalEnvelopingAlgebra.ι ℝ (lieEq E a (TR.toL (Y * X))) := by
  rw [← map_sub, ← map_sub, ← Ring.lie_def, ← LieHom.map_lie, ← lieEq_lie]
  rfl

theorem glRel_genU (v : InfinitePlace E) : Formalism.REAL.GlRel (genU (a := a) v) := fun i j k l => by
  classical
  have h0 : TR.toL (0 : Matrix (Fin a) (Fin a) (TR.Rinf E)) = 0 := rfl
  unfold genU
  rw [ι_comm]
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, ← Pi.single_mul, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h), h0, map_zero, map_zero]
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, ← Pi.single_mul, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h), h0, map_zero, map_zero]

theorem commute_genU {v w : InfinitePlace E} (h : v ≠ w) (i j k l : Fin a) : Commute (genU v i j) (genU w k l) := by
  classical
  have key : ∀ {v w : InfinitePlace E}, v ≠ w → ∀ i j k l : Fin a,
      (Matrix.single i j (Pi.single v 1) * Matrix.single k l (Pi.single w 1) : Matrix (Fin a) (Fin a) (TR.Rinf E)) = 0 := by
    intro v w h i j k l
    by_cases e : j = k
    · subst e
      have : (Pi.single v 1 * Pi.single w 1 : TR.Rinf E) = 0 := by
        funext x
        by_cases hx : x = v
        · subst hx; simp [h]
        · simp [hx]
      rw [Matrix.single_mul_single_same, this, Matrix.single_zero]
    · exact Matrix.single_mul_single_of_ne (h := e) ..
  refine sub_eq_zero.1 ?_
  unfold genU
  rw [ι_comm, key h, key h.symm, sub_self]

theorem adjoin_genU : Algebra.adjoin ℝ {x : UEnv E a | ∃ v i j, x = genU v i j} = ⊤ := by
  classical
  refine eq_top_iff.2 fun u _ => ?_
  induction u using UEnv.induction with
  | halg r => exact Subalgebra.algebraMap_mem _ r
  | hι Y =>
    obtain ⟨X, rfl⟩ := (lieEq E a).surjective Y
    have e : X = ∑ i, ∑ j, ∑ v, X i j v • TR.toL (Matrix.single i j (Pi.single v 1)) := by
      funext k l w
      simp [Finset.sum_apply, Matrix.single_apply, Pi.single_apply, ite_and, ite_apply]
    rw [e]
    simp only [map_sum, map_smul]
    exact sum_mem fun i _ => sum_mem fun j _ => sum_mem fun v _ =>
      Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨v, i, j, rfl⟩)) _
  | hmul x y hx hy => exact mul_mem (hx trivial) (hy trivial)
  | hadd x y hx hy => exact add_mem (hx trivial) (hy trivial)

theorem uTR_mem_Zalg {z : UEnv E a} (hz : z ∈ (isExpLieAlgebra E a).centerU) : uTR E a z ∈ TR.Zalg E a := by
  have h1 : uTR E a z ∈ Algebra.adjoin ℂ {x | ∃ v i j, x = TR.Eop (a := a) v i j} := by
    have : Algebra.adjoin ℝ {x : UEnv E a | ∃ v i j, x = genU v i j} ≤
        ((Algebra.adjoin ℂ {x | ∃ v i j, x = TR.Eop (E := E) (a := a) v i j}).restrictScalars ℝ).comap (uTR E a) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨v, i, j, rfl⟩
      exact Algebra.subset_adjoin ⟨v, i, j, uTR_genU v i j⟩
    exact this (by rw [adjoin_genU]; exact Algebra.mem_top)
  have h2 := multiCentre (TR.Eop (E := E) (a := a))
    (fun v => by simpa only [uTR_genU] using glRel_map (uTR E a) (glRel_genU v))
    (fun v w h i j k l => by simpa only [uTR_genU] using (commute_genU h i j k l).map (uTR E a)) h1
    fun v i j => by rw [← uTR_genU, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  refine Algebra.adjoin_mono ?_ h2
  rintro _ ⟨v, u, rfl⟩
  exact ⟨v, u - ((a : ℂ) - 1) / 2, by rw [TR.cap, sub_add_cancel]⟩

theorem Zalg_eq_span : Subalgebra.toSubmodule (TR.Zalg E a) =
    Submodule.span ℂ (uTR E a '' ((isExpLieAlgebra E a).centerU : Set (UEnv E a))) := by
  refine le_antisymm (fun z hz => ?_) (Submodule.span_le.2 ?_)
  · induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨v, u, rfl⟩ := hx
      have := qdet_mem_span_center genU glRel_genU (fun _ _ h => commute_genU h) adjoin_genU
        (uTR E a) v (u + ((a : ℂ) - 1) / 2)
      simp only [uTR_genU] at this
      exact this
    | algebraMap c =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨1, one_mem _, map_one _⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨p * q, mul_mem hp hq, map_mul _ p q⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact uTR_mem_Zalg hz

theorem zfin_iff (φ : TR.Sm E a) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm E a) => z φ) '' TR.Zalg E a)) ↔
      IsZFinite (smEq E a φ) := by
  have e : (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm E a) => z φ) '' TR.Zalg E a)).map (smEq E a).toLinearMap =
      Submodule.span ℂ ((fun z => uAction z (smEq E a φ)) '' ((isExpLieAlgebra E a).centerU : Set (UEnv E a))) := by
    have h1 : (fun z : Module.End ℂ (TR.Sm E a) => z φ) '' TR.Zalg E a =
        (Subalgebra.toSubmodule (TR.Zalg E a)).map (LinearMap.applyₗ φ) := rfl
    rw [h1, Submodule.span_eq, Zalg_eq_span, Submodule.map_span, Submodule.map_span, Set.image_image, Set.image_image]
    rfl
  rw [IsZFinite, ← e]
  exact ⟨fun _ => inferInstance, fun h => Module.Finite.equiv ((smEq E a).submoduleMap _).symm⟩

end UpperTheory.V.Fb
