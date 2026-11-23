import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open NumberField GlobalTheory.CuspRep UpperTheory.V

noncomputable section

namespace UpperTheory.V.Af.CuspFin

theorem casMem : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ S : Subalgebra ℂ A, (∀ u, Formalism.REAL.qdet E u ∈ S) → Formalism.REAL.Cas E ∈ S := by
  intro A _ _ n E hE S h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hE : ∀ i j, E i j ∈ S := by
      intro i j
      obtain rfl : n = 1 := by have := i.2; omega
      have := GlobalTheory.CuspRep.Central.trace_mem E (Subalgebra.toSubmodule S) (one_mem S) h
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simpa using this
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (hE _ _) (hE _ _)
  have ht : ∑ i, E i i ∈ S := GlobalTheory.CuspRep.Central.trace_mem E (Subalgebra.toSubmodule S) (one_mem S) h
  by_contra hc
  obtain ⟨φ, hφ, hS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule S) hc inferInstance
  have h0 : ∀ x ∈ S, φ x = 0 := fun x hx => (Submodule.eq_bot_iff _).1 hS _ ⟨x, hx, rfl⟩
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders A n E
  have core := GlobalTheory.CapelliCasimir.scalar_core n hn (fun l => -((l : ℕ) : ℂ)) 0 (fun i => φ (E i i))
    (fun i j => φ (E i i * E j j - E j i * E i j)) (fun d => φ (Rm d)) (φ 1) 0 (fun Y => by
      have h2 := congrArg φ (hR Y).symm
      rw [h0 _ (h Y)] at h2
      simp only [map_add, map_sum, map_smul, smul_eq_mul, sub_eq_add_neg (a := Y)] at h2
      simp only [add_zero]
      rw [h2, h0 1 (one_mem S), mul_zero])
  have h2 := core.2
  have h3 := congrArg φ (GlobalTheory.CapelliCasimir.sq_sub_cas E hE)
  have h4 := h0 _ ht
  rw [map_sub, h0 _ (mul_mem ht ht)] at h3
  simp only [h0 1 (one_mem S), mul_zero, zero_add, Finset.sum_erase_eq_sub (Finset.mem_univ _)] at h2
  simp only [map_sub φ, map_sum, map_smul, smul_eq_mul] at h3 h2 h4
  apply hφ
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h4, mul_assoc, neg_mul, one_mul, Finset.sum_neg_distrib] at h2 h3
  linear_combination -h3 - h2

theorem skewCurve : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (X : TR.Lie F a), (∀ i j, X j i = -X i j) → ∃ c : ℝ → TR.Kinf F a, c 0 = 1 ∧ HasDerivAt (fun t => TR.toL (Unitary.toUnits (c t)).val) X 0 := by
  intro F _ _ _ a X hX
  classical
  have hs : ∀ t : ℝ, t • Matrix.of X ∈ skewAdjoint (Matrix (Fin a) (Fin a) (TR.Rinf F)) := fun t => by
    rw [skewAdjoint.mem_iff]
    ext i j v
    simp [Matrix.star_apply, hX i j]
  have hcs : ContinuousStar (Matrix (Fin a) (Fin a) (TR.Rinf F)) := inferInstance
  letI : NormedRing (Matrix (Fin a) (Fin a) (TR.Rinf F)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (TR.Rinf F)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (TR.Rinf F)) := Matrix.linftyOpNormedAlgebra
  refine ⟨fun t => ⟨NormedSpace.exp (t • Matrix.of X), by
    have := @NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (Matrix (Fin a) (Fin a) (TR.Rinf F)) _ _ _ _ hcs
    exact this (hs t)⟩, ?_, ?_⟩
  · exact Subtype.ext (by simp)
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) 0
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h

theorem sliceOp : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (X : TR.Lie F a), (∀ i j, X j i = -X i j) → (∃ D : Module.End ℂ (TR.Kinf F a → ℂ), ∀ (φ : TR.Sm F a) (g : GA F a), D (fun k => (TR.cptRep F a k φ).1 g) = fun k => (TR.cptRep F a k (TR.lie F a X φ)).1 g) ∧ ∀ (V : Submodule ℂ (TR.Kinf F a → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, ∀ k' : TR.Kinf F a, (fun k => f (k * k')) ∈ V) → ∀ (φ : TR.Sm F a) (g : GA F a), (fun k => (TR.cptRep F a k φ).1 g) ∈ V → (fun k => (TR.cptRep F a k (TR.lie F a X φ)).1 g) ∈ V := by
  intro F _ _ _ a X hX
  obtain ⟨c, h0, hc⟩ := skewCurve F a X hX
  have key : ∀ (φ : TR.Sm F a) (g : GA F a) (k : TR.Kinf F a),
      HasDerivAt (fun t => (TR.cptRep F a (k * c t) φ).1 g) ((TR.cptRep F a k (TR.lie F a X φ)).1 g) 0 := by
    intro φ g k
    have h := TR.hasDerivAt_curve φ (g * TR.infGL F a (Unitary.toUnits k)) (fun t => Unitary.toUnits (c t)) X
      (by rw [h0, map_one]) hc
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    change φ.1 (g * TR.infGL F a (Unitary.toUnits (k * c t))) = _
    rw [map_mul, map_mul, ← mul_assoc]
  constructor
  · let U : Submodule ℂ (TR.Kinf F a → ℂ) :=
      { carrier := {f | ∀ k, DifferentiableAt ℝ (fun t => f (k * c t)) 0}
        add_mem' := fun h1 h2 k => (h1 k).add (h2 k)
        zero_mem' := fun k => differentiableAt_const _
        smul_mem' := fun r f h k => (h k).const_smul r }
    let D0 : U →ₗ[ℂ] (TR.Kinf F a → ℂ) :=
      { toFun := fun f k => deriv (fun t => f.1 (k * c t)) 0
        map_add' := fun f f' => funext fun k => deriv_add (f.2 k) (f'.2 k)
        map_smul' := fun r f => funext fun k => deriv_const_smul r (f.2 k) }
    obtain ⟨D, hD⟩ := LinearMap.exists_extend D0
    refine ⟨D, fun φ g => ?_⟩
    have hm : (fun k => (TR.cptRep F a k φ).1 g) ∈ U := fun k => (key φ g k).differentiableAt
    refine (LinearMap.congr_fun hD ⟨_, hm⟩).trans (funext fun k => (key φ g k).deriv)
  · intro V hV hst φ g hφ
    have hcl : IsClosed (V : Set (TR.Kinf F a → ℂ)) := V.closed_of_finiteDimensional
    refine hcl.mem_of_tendsto (b := nhdsWithin (0 : ℝ) {0}ᶜ)
      (f := fun t k => slope (fun t => (TR.cptRep F a (k * c t) φ).1 g) 0 t)
      (tendsto_pi_nhds.2 fun k => hasDerivAt_iff_tendsto_slope.1 (key φ g k)) (Filter.Eventually.of_forall fun t => ?_)
    exact V.smul_of_tower_mem ((t - 0)⁻¹ : ℝ) (V.sub_mem (hst _ hφ (c t)) (hst _ hφ (c 0)))

theorem polySlices : ∀ (T M ι : Type) [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ T) (D : Module.End ℂ M) (s : ι → T →ₗ[ℂ] M), (∀ i x, D (s i x) = s i (C x)) → ∀ (V : Submodule ℂ M), FiniteDimensional ℂ V → ∀ N : Submodule ℂ T, (∀ x ∈ N, C x ∈ N) → (∀ i, ∀ x ∈ N, s i x ∈ V) → ∃ q : Polynomial ℂ, q.Monic ∧ 0 < q.natDegree ∧ ∀ i, ∀ x ∈ N, s i (Polynomial.aeval C q x) = 0 := by
  intro T M ι _ _ _ _ C D s hs V hV N hN hNV
  let U : Submodule ℂ M := Submodule.span ℂ {y | ∃ i, ∃ x ∈ N, y = s i x}
  have hU : U ≤ V := Submodule.span_le.2 (by rintro _ ⟨i, x, hx, rfl⟩; exact hNV i x hx)
  have : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hU
  have hD : ∀ y ∈ U, D y ∈ U := by
    have : U ≤ U.comap D := Submodule.span_le.2 (by
      rintro _ ⟨i, x, hx, rfl⟩
      exact Submodule.subset_span ⟨i, C x, hN x hx, hs i x⟩)
    exact fun y hy => this hy
  have hpow : ∀ i (n : ℕ) x, s i ((C ^ n) x) = (D ^ n) (s i x) := by
    intro i n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hs]
  have hev : ∀ i (q : Polynomial ℂ) x, s i (Polynomial.aeval C q x) = Polynomial.aeval D q (s i x) := by
    intro i q x
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hpow]
  have hpow2 : ∀ (n : ℕ) (y : U), (((D.restrict hD ^ n) y : U) : M) = (D ^ n) y := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl
  have hev2 : ∀ (q : Polynomial ℂ) (y : U), ((Polynomial.aeval (D.restrict hD) q y : U) : M) = Polynomial.aeval D q y := by
    intro q y
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, hpow2]
  have hm := LinearMap.charpoly_monic (D.restrict hD)
  refine ⟨Polynomial.X * (D.restrict hD).charpoly, Polynomial.monic_X.mul hm, ?_, fun i x hx => ?_⟩
  · rw [Polynomial.monic_X.natDegree_mul hm, Polynomial.natDegree_X]; omega
  · rw [hev]
    refine (hev2 _ ⟨s i x, Submodule.subset_span ⟨i, x, hx, rfl⟩⟩).symm.trans ?_
    rw [map_mul, LinearMap.aeval_self_charpoly, mul_zero]
    rfl

theorem typePoly : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (TR.Kinf F a) W) (ι : Type) [Fintype ι] (X : ι → TR.Lie F a), (∀ l i j, X l j i = -X l i j) → ∀ r : ℂ, ∃ q : Polynomial ℂ, q.Monic ∧ 0 < q.natDegree ∧ ∀ φ : TR.Sm F a, (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → Polynomial.aeval (r • ∑ l, TR.lie F a (X l) * TR.lie F a (X l)) q φ = 0 := by
  intro F _ _ _ a W _ _ _ ρ ι _ X hX r
  choose D hD using fun l => (sliceOp F a (X l) (hX l)).1
  have hV : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
    let m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (TR.Kinf F a → ℂ) :=
      LinearMap.mk₂ ℂ (fun ℓ w k => ℓ (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift m)) (Submodule.span_le.2 ?_)
    rintro _ ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ⊗ₜ w, rfl⟩
  have hst : ∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∀ k' : TR.Kinf F a, (fun k => f (k * k')) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
    intro f hf k'
    have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ fun k => k * k') :=
      Submodule.span_le.2 (by
        rintro _ ⟨ℓ, w, rfl⟩
        exact Submodule.subset_span ⟨ℓ, ρ k' w, funext fun k => by simp [LinearMap.funLeft_apply]⟩)
    exact this hf
  let s : GA F a → TR.Sm F a →ₗ[ℂ] (TR.Kinf F a → ℂ) := fun g =>
    { toFun := fun φ k => (TR.cptRep F a k φ).1 g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hD' : ∀ l g φ, D l (s g φ) = s g (TR.lie F a (X l) φ) := fun l g φ => hD l φ g
  let N : Submodule ℂ (TR.Sm F a) := ⨅ g, (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (s g)
  have hN : ∀ φ, φ ∈ N ↔ ∀ g, s g φ ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := fun φ => by
    simp only [N, Submodule.mem_iInf, Submodule.mem_comap]
  have hNl : ∀ l, ∀ φ ∈ N, TR.lie F a (X l) φ ∈ N := fun l φ hφ =>
    (hN _).2 fun g => (sliceOp F a (X l) (hX l)).2 _ hV hst φ g ((hN φ).1 hφ g)
  obtain ⟨q, hm, hd, hq⟩ := polySlices _ _ _ (r • ∑ l, TR.lie F a (X l) * TR.lie F a (X l)) (r • ∑ l, D l * D l) s
    (fun g φ => by simp only [LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_smul, map_sum, hD'])
    _ hV N (fun φ hφ => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
      exact N.smul_mem _ (N.sum_mem fun l _ => hNl l _ (hNl l _ hφ))) (fun g φ hφ => (hN φ).1 hφ g)
  refine ⟨q, hm, hd, fun φ hφ => Subtype.ext (funext fun g => ?_)⟩
  have h := congrFun (hq g φ ((hN φ).2 hφ)) 1
  change (TR.cptRep F a 1 _).1 g = 0 at h
  rw [map_one] at h
  exact h

end UpperTheory.V.Af.CuspFin
