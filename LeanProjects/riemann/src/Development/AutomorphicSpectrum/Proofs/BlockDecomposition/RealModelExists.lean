import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHomStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativePreservesEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionParabolicEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionDerivativeAtOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaParabolicUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnitaryGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightDerivativeEqZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContainingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantEvalLowestStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommuteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValuePermInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfCharStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemConeStatement

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem kF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {F1 F2 : Fin n → Fin n → Module.End ℂ V}
    (g1 : Formalism.REAL.GlRel F1) (g2 : Formalism.REAL.GlRel F2) (cm : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) :
    Formalism.REAL.GlRel (kF F1 F2) := by
  intro a b c d
  have e : kF F1 F2 a b * kF F1 F2 c d - kF F1 F2 c d * kF F1 F2 a b =
      (F1 a b * F1 c d - F1 c d * F1 a b) + (F2 a b * F2 c d - F2 c d * F2 a b) +
        (F1 a b * F2 c d - F2 c d * F1 a b) - (F1 c d * F2 a b - F2 a b * F1 c d) := by
    simp only [kF]
    noncomm_ring
  rw [e, g1 a b c d, g2 a b c d, cm a b c d, cm c d a b]
  simp only [kF, sub_self, add_zero, sub_zero]
  split_ifs <;> first | abel | (simp; done) | (simp; abel)

theorem barF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {F2 : Fin n → Fin n → Module.End ℂ V}
    (g2 : Formalism.REAL.GlRel F2) : Formalism.REAL.GlRel (barF F2) := by
  intro a b c d
  have h := g2 b a d c
  simp only [barF, neg_mul_neg]
  rw [h]
  simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
  split_ifs <;> first | abel | (simp; done) | (simp; abel)

theorem muZ_cast (lam : Fin n → ℤ) (lev : Fin n → ℕ) (a : Fin n) : ((muZ lam lev a : ℤ) : ℝ) = muQ lam lev a := by
  simp only [muZ, muQ, rhoU]
  push_cast
  ring

theorem model_of_ops (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hlev : IsLev lam lev)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V) (f : V)
    (ev : V →ₗ[ℂ] ℂ) (gl1 : Formalism.REAL.GlRel F1) (gl2 : Formalism.REAL.GlRel F2)
    (cm : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b)
    (unitK : ∀ a b (x y : V), ⟪kF F1 F2 a b x, y⟫_ℂ = ⟪x, kF F1 F2 b a y⟫_ℂ)
    (gen : ∀ x : V, ∃ T ∈ alg F1 F2, T f = x) (S₀ : Submodule ℂ V) (fd : FiniteDimensional ℂ S₀) (hf : f ∈ S₀)
    (st : ∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) (hw : f ∈ hwSp F1 F2 (muQ lam lev)) (hev : ev f ≠ 0)
    (e1l : ∀ a b v, lev b ≤ lev a → a ≠ b → ev (F1 a b v) = 0) (e1d : ∀ a v, ev (F1 a a v) = (lam a : ℂ) * ev v)
    (e2l : ∀ a b v, lev b ≤ lev a → a ≠ b → ev (barF F2 a b v) = 0)
    (e2d : ∀ a v, ev (barF F2 a a v) = (yZ lam lev a : ℂ) * ev v)
    (sep : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) →
      ∀ w ∈ S, w = 0) : Nonempty (Model lam lev) := by
  have gK := kF_gl gl1 gl2 cm
  have gB := barF_gl gl2
  have lf := GlobalTheory.T.exists_k_finite_submodule_containing n V F1 F2 gl1 gl2 cm f gen S₀ fd hf st
  have hlow : ∀ a b : Fin n, b < a → lev b ≤ lev a ∧ a ≠ b := fun a b h => ⟨hlev.1 h.le, h.ne'⟩
  refine ⟨{ W := V, F1 := F1, F2 := F2, f := f, gl1 := gl1, gl2 := gl2, comm := cm, unitK := unitK, locFin := lf,
            hw := hw, ne := fun h => hev (by rw [h, map_zero]), ch1 := ?_, ch2 := ?_, cone := ?_ }⟩
  · intro m x
    refine GlobalTheory.T.center_acts_by_scalar_on_cyclic n V F1 F2 lf (gelA F1 m) (fun a b => ⟨GlobalTheory.T.gelfand_invariant_commute_generator n V F1 gl1 m a b, GlobalTheory.T.gelfand_invariant_commute_of_commute n V F1 (F2 a b)
      (fun c d => (cm c d a b).symm) m⟩) ev _ (fun v => ?_) sep x
    have h := GlobalTheory.T.gelfand_invariant_eval_lowest n V F1 gl1 ev (fun a => (lam a : ℂ)) (fun a b hba v => e1l a b v (hlow a b hba).1 (hlow a b hba).2)
      e1d m v
    rw [h]
    congr 2
    funext a
    simp [infOf]
  · intro m x
    refine GlobalTheory.T.center_acts_by_scalar_on_cyclic n V F1 F2 lf (gelA (barF F2) m) (fun a b => ⟨?_, ?_⟩) ev _ (fun v => ?_) sep x
    · refine GlobalTheory.T.gelfand_invariant_commute_of_commute n V (barF F2) (F1 a b) (fun c d => ?_) m
      simp only [barF, mul_neg, neg_mul, cm a b d c]
    · have h := GlobalTheory.T.gelfand_invariant_commute_generator n V (barF F2) gB m b a
      simp only [barF, mul_neg, neg_mul, neg_inj] at h
      simpa [barF] using h
    · have h := GlobalTheory.T.gelfand_invariant_eval_lowest n V (barF F2) gB ev (fun a => (yZ lam lev a : ℂ))
        (fun a b hba v => e2l a b v (hlow a b hba).1 (hlow a b hba).2) e2d m v
      rw [h]
      obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char n lam lev hlev
      have : (fun a : Fin n => (yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) =
          fun a => infOf lam false (σ a) := funext hσ
      rw [this, GlobalTheory.T.gelfand_value_perm_invariant n (infOf lam false) σ m]
  · intro ν x hx hx0
    set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
    refine GlobalTheory.T.highest_weight_mem_cone n V (kF F1 F2) gK lev hlev.1 ev (muQ lam lev) ν x hx (fun a b v hl hne => ?_) (fun a v => ?_) ?_
    · have h1 := e1l a b v hl.ge hne
      have h2 := e2l b a v hl.le hne.symm
      simp only [barF, LinearMap.neg_apply, map_neg, neg_eq_zero] at h2
      simp [kF, h1, h2]
    · have h1 := e1d a v
      have h2 := e2d a v
      simp only [barF, LinearMap.neg_apply, map_neg] at h2
      have hm : (muQ lam lev a : ℂ) = (lam a : ℂ) - (yZ lam lev a : ℂ) := by
        rw [← muZ_cast]
        simp [yZ]
      simp only [kF, LinearMap.add_apply, map_add, h1, hm]
      linear_combination -h2
    · by_contra hcon
      push_neg at hcon
      obtain ⟨S₁, fd₁, hx₁, st₁⟩ := lf x
      have hstab : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
        intro T hT
        induction hT using Algebra.adjoin_induction with
        | mem T hT => obtain ⟨a, b, rfl⟩ := hT; exact st₁ a b
        | algebraMap r => intro w hw; simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
        | add T T' _ _ h h' => intro w hw; exact S₁.add_mem (h w hw) (h' w hw)
        | mul T T' _ _ h h' => intro w hw; exact h _ (h' w hw)
      let S : Submodule ℂ V := A.toSubmodule.map (LinearMap.applyₗ x)
      have hS : ∀ w, w ∈ S ↔ ∃ T ∈ A, T x = w := by
        intro w
        simp [S, Submodule.mem_map]
      have hle : S ≤ S₁ := by
        intro w hw
        obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact hstab T hT x hx₁
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
      have h0 := sep S inferInstance (fun a b w hw => ?_) (fun w hw => ?_) x ((hS x).2 ⟨1, A.one_mem, rfl⟩)
      · exact hx0 h0
      · obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact (hS _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
      · obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact hcon T hT

theorem res_gl {M : Type} [AddCommGroup M] [Module ℂ M] (V : Submodule ℂ M) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : ∀ a b, ∀ v ∈ V, E a b v ∈ V) (h : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (fun a b => (E a b).restrict (hE a b)) := by
  intro a b c d
  ext v
  have := congrArg (fun F => F (v : M)) (h a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, LinearMap.restrict_apply]
  rw [this]
  split_ifs <;> simp

theorem first_raising_mem_equivariant (lev : Fin n → ℕ) (φ : Mat n → ℂ) (a b : Fin n) {h : SmF n} (hh : h ∈ Eqv lev φ) :
    e1 DR a b h ∈ Eqv lev φ := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)
    (Submodule.smul_mem _ _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)))

theorem first_lowering_mem_equivariant (lev : Fin n → ℕ) (φ : Mat n → ℂ) (a b : Fin n) {h : SmF n} (hh : h ∈ Eqv lev φ) :
    f1 DR a b h ∈ Eqv lev φ := by
  simp only [f1, LinearMap.smul_apply, LinearMap.add_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)
    (Submodule.smul_mem _ _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)))

theorem evaluation_raising_lowering (lev : Fin n → ℕ) (f h : SmF n) (hf : f ∈ Eqv lev f.1) (h1 : f.1 1 = 1) (hh : h ∈ Eqv lev f.1)
    (a b : Fin n) (hab : lev b ≤ lev a) :
    (e1 DR a b h).1 1 = (e1 DR a b f).1 1 * h.1 1 ∧ (f1 DR a b h).1 1 = (f1 DR a b f).1 1 * h.1 1 := by
  have hX : ∀ c : ℂ, ∀ a' b', lev a' < lev b' → (Matrix.single a b c : Mat n) a' b' = 0 := by
    intro c a' b' hlt
    rw [Matrix.single_apply_of_ne]
    rintro ⟨rfl, rfl⟩
    exact absurd hlt (not_lt.2 hab)
  have d1 := GlobalTheory.T.right_derivative_lower_block_at_one n lev f h hf h1 hh _ (hX 1)
  have d2 := GlobalTheory.T.right_derivative_lower_block_at_one n lev f h hf h1 hh _ (hX Complex.I)
  constructor
  · simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
      Pi.sub_apply, d1, d2, smul_eq_mul]
    ring
  · simp only [f1, LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, Pi.smul_apply,
      Pi.add_apply, d1, d2, smul_eq_mul]
    ring

theorem modelEx_main : ModelEx := by
  intro n lam hlam lev hlev
  classical
  letI : MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _
  haveI : BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := GlobalTheory.T.exists_haar_unitary_group n
  have hmem := GlobalTheory.T.inducedFunction_smooth n lam hlam lev hlev
  let F : SmF n := ⟨fRaw lam lev, hmem⟩
  have hF : F.1 = fRaw lam lev := rfl
  have hFe : F ∈ Eqv lev F.1 := fun p hp g hg => GlobalTheory.T.inducedFunction_parabolic_equivariant n lam hlam lev hlev p hp g hg
  have hF1 : F.1 1 = 1 := GlobalTheory.T.inducedFunction_at_one n lam lev
  let A := Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}
  have hcyc : ∀ w, w ∈ cyc F ↔ ∃ T ∈ A, T F = w := by
    intro w
    simp [cyc, A, Submodule.mem_map]
  have hEq : ∀ T ∈ A, ∀ h ∈ Eqv lev F.1, T h ∈ Eqv lev F.1 := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl | rfl⟩ := hT
      · exact fun h hh => first_raising_mem_equivariant lev _ a b hh
      · intro h hh
        simp only [e2, LinearMap.neg_apply]
        exact Submodule.neg_mem _ (first_lowering_mem_equivariant lev _ b a hh)
    | algebraMap r => intro w hw; simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hw
    | add T T' _ _ h h' => intro w hw; exact Submodule.add_mem _ (h w hw) (h' w hw)
    | mul T T' _ _ h h' => intro w hw; exact h _ (h' w hw)
  have hWE : ∀ w ∈ cyc F, w ∈ Eqv lev F.1 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact hEq T hT F hFe
  have st1 : ∀ a b, ∀ w ∈ cyc F, e1 DR a b w ∈ cyc F := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact (hcyc _).2 ⟨e1 DR a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩) hT, rfl⟩
  have st2 : ∀ a b, ∀ w ∈ cyc F, e2 DR a b w ∈ cyc F := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact (hcyc _).2 ⟨e2 DR a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩) hT, rfl⟩
  obtain ⟨hsym, hnn, hadd, hsm, hdef⟩ := GlobalTheory.T.l2_inner_product_hermitian_form n κ
  have hzero : ∀ w ∈ cyc F, (∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0) → w = 0 := by
    intro w hw hk
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · obtain ⟨p, hp, k, rfl⟩ := GlobalTheory.T.iwasawa_parabolic_unitary n lev hlev.1 g hg
      have := hWE w hw p hp k.1 (GlobalTheory.CompanionTheory.ModelS.unit_mem k)
      simp [this, hk k]
    · exact w.2.2 g hg
  let core : InnerProductSpace.Core ℂ (cyc F) :=
    { inner := fun x y => ipK κ x.1 y.1
      conj_inner_symm := fun x y => hsym x.1 y.1
      re_inner_nonneg := fun x => hnn x.1
      add_left := fun x y z => hadd x.1 y.1 z.1
      smul_left := fun x y c => hsm c x.1 y.1
      definite := fun x hx => Subtype.ext (hzero x.1 x.2 (hdef x.1 hx)) }
  letI : NormedAddCommGroup (cyc F) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ core
  letI : InnerProductSpace ℂ (cyc F) := InnerProductSpace.ofCore core.toCore
  obtain ⟨g1, g2, cm⟩ := GlobalTheory.CompanionTheory.GLK.Pair.gl_pair n (SmF n) DR (GlobalTheory.T.right_derivative_real_lie_hom n).1 (GlobalTheory.T.right_derivative_real_lie_hom n).2.1 (GlobalTheory.T.right_derivative_real_lie_hom n).2.2
  let F1 : Fin n → Fin n → Module.End ℂ (cyc F) := fun a b => (e1 DR a b).restrict (st1 a b)
  let F2 : Fin n → Fin n → Module.End ℂ (cyc F) := fun a b => (e2 DR a b).restrict (st2 a b)
  have hKc : ∀ a b (x : cyc F), ((kF F1 F2 a b x : cyc F) : SmF n) = Kf a b x.1 := fun _ _ _ => rfl
  let f : cyc F := ⟨F, (hcyc F).2 ⟨1, A.one_mem, rfl⟩⟩
  let ev : cyc F →ₗ[ℂ] ℂ := ev1.comp (cyc F).subtype
  obtain ⟨S₁, fd₁, hf₁, st₁⟩ := GlobalTheory.T.inducedFunction_k_finite n lam hlam lev hlev F hF
  obtain ⟨hh1, hh2⟩ := GlobalTheory.T.inducedFunction_k_highest_weight n lam hlam lev hlev F hF
  have hder := GlobalTheory.T.inducedFunction_derivative_at_one n lam hlam lev hlev F hF
  refine model_of_ops lam lev hlev F1 F2 f ev (res_gl _ _ st1 g1) (res_gl _ _ st2 g2) ?_ ?_ ?_
    (S₁.comap (cyc F).subtype) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b c d
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact congrArg (fun T => T w.1) (cm a b c d)
  · intro a b x y
    exact GlobalTheory.T.k_action_skew_adjoint_l2 n κ (GlobalTheory.T.integral_right_derivative_eq_zero n κ) a b x.1 y.1
  · intro x
    have key : ∀ T ∈ A, ∃ T' ∈ alg F1 F2, ∀ w : cyc F, ((T' w : cyc F) : SmF n) = T w.1 := by
      intro T hT
      induction hT using Algebra.adjoin_induction with
      | mem T hT =>
        obtain ⟨a, b, rfl | rfl⟩ := hT
        · exact ⟨F1 a b, Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩, fun _ => rfl⟩
        · exact ⟨F2 a b, Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩, fun _ => rfl⟩
      | algebraMap r =>
        exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun w => by simp [Module.algebraMap_end_apply]⟩
      | add T T' _ _ h h' =>
        obtain ⟨P, hP, hP'⟩ := h
        obtain ⟨Q, hQ, hQ'⟩ := h'
        exact ⟨P + Q, Subalgebra.add_mem _ hP hQ, fun w => by simp [hP', hQ']⟩
      | mul T T' _ _ h h' =>
        obtain ⟨P, hP, hP'⟩ := h
        obtain ⟨Q, hQ, hQ'⟩ := h'
        exact ⟨P * Q, Subalgebra.mul_mem _ hP hQ, fun w => by simp [hP', hQ']⟩
    obtain ⟨T, hT, hTx⟩ := (hcyc x.1).1 x.2
    obtain ⟨T', hT', hc⟩ := key T hT
    exact ⟨T', hT', Subtype.ext (by rw [hc f]; exact hTx)⟩
  · let φ : ↥(S₁.comap (cyc F).subtype) →ₗ[ℂ] S₁ :=
      ((cyc F).subtype ∘ₗ (S₁.comap (cyc F).subtype).subtype).codRestrict S₁ (fun x => x.2)
    exact Module.Finite.of_injective φ (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : ↥S₁ => (t : SmF n)) h)))
  · exact hf₁
  · intro a b w hw
    exact st₁ a b w.1 hw
  · refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · apply Subtype.ext
      rw [hKc]
      have := hh2 a
      rw [← muZ_cast]
      simpa [f] using this
    · apply Subtype.ext
      rw [hKc]
      exact hh1 a b hab
  · show F.1 1 ≠ 0
    rw [hF1]
    exact one_ne_zero
  · intro a b v hl hne
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a b hl).1
    have h0 := (hder a b hl).1
    show (e1 DR a b v.1).1 1 = 0
    rw [this, h0, if_neg hne, zero_mul]
  · intro a v
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a a le_rfl).1
    have h0 := (hder a a le_rfl).1
    show (e1 DR a a v.1).1 1 = _ * v.1.1 1
    rw [this, h0, if_pos rfl]
  · intro a b v hl hne
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a b hl).2
    have h0 := (hder a b hl).2
    show (-(e2 DR b a v.1)).1 1 = 0
    simp only [e2, neg_neg, LinearMap.neg_apply]
    rw [this, h0, if_neg hne, zero_mul]
  · intro a v
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a a le_rfl).2
    have h0 := (hder a a le_rfl).2
    show (-(e2 DR a a v.1)).1 1 = _ * v.1.1 1
    simp only [e2, neg_neg, LinearMap.neg_apply]
    rw [this, h0, if_pos rfl]
  · intro S fdS stS ev0 w hw
    haveI := fdS
    have hS := GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one n (S.map (cyc F).subtype) inferInstance (by
        intro a b u hu
        obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
        exact Submodule.mem_map.2 ⟨kF F1 F2 a b v, stS a b v hv, rfl⟩) (by
        intro u hu
        obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
        exact ev0 v hv) w.1 (Submodule.mem_map.2 ⟨w, hw, rfl⟩)
    exact Subtype.ext (hzero w.1 w.2 hS)

end GlobalTheory.CompanionTheory.ModelS
