import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOfLi
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem exists_of_li {Q ι : Type} [AddCommGroup Q] [Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ)
    (h : LinearIndependent ℂ f) (v : ι → ℂ) : ∃ q, ∀ i, f i q = v i :=
  _root_.UpperTheory.Reformulated.B.Qe54.exists_of_li f h v

private theorem chineseRemainder_finiteCover {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (hc : IsFinCover ℂ K x) :
    Finite (fib ℂ K x) ∧ ∀ v : fib ℂ K x → ℂ, ∃ h : rB ℂ K x {0}, ∀ e, e.1 h = v e := by
  classical
  let I : Ideal (rB ℂ K x {0}) :=
    Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0}))
  let mk : rB ℂ K x {0} →ₐ[ℂ] (rB ℂ K x {0} ⧸ I) := Ideal.Quotient.mkₐ ℂ I
  have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F K d x hc {0} (Finset.singleton_nonempty 0)).1
  have hmem : ∀ y (hy : y ∈ rA ℂ x {0}), algebraMap F K y ∈ rB ℂ K x {0} := fun y hy =>
    (integralClosure (rA ℂ x {0}) K).algebraMap_mem ⟨y, hy⟩
  have hA : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ,
      mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c := by
    intro y hy
    refine Algebra.adjoin_induction (p := fun y hy => ∃ c : ℂ,
      mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, j, rfl⟩
      obtain rfl : i = 0 := Finset.mem_singleton.1 hi
      induction j using Fin.cases with
      | zero =>
        refine ⟨1, ?_⟩
        rw [map_one, ← map_one mk]
        congr 1
        ext
        simp [div_self (hc.pd.ne 0)]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    · intro r
      refine ⟨r, ?_⟩
      rw [← mk.commutes r]
      congr 1
      ext
      simp [← IsScalarTower.algebraMap_apply]
    · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
      refine ⟨c + c', ?_⟩
      have e : (⟨algebraMap F K (a + b), hmem _ (add_mem ha hb)⟩ : rB ℂ K x {0}) =
          ⟨_, hmem a ha⟩ + ⟨_, hmem b hb⟩ := Subtype.ext (map_add _ _ _)
      exact (congrArg mk e).trans (by rw [map_add, hc1, hc2, map_add])
    · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
      refine ⟨c * c', ?_⟩
      have e : (⟨algebraMap F K (a * b), hmem _ (mul_mem ha hb)⟩ : rB ℂ K x {0}) =
          ⟨_, hmem a ha⟩ * ⟨_, hmem b hb⟩ := Subtype.ext (map_mul _ _ _)
      exact (congrArg mk e).trans (by rw [map_mul, hc1, hc2, map_mul])
  have hQ : Module.Finite ℂ (rB ℂ K x {0} ⧸ I) := by
    obtain ⟨s, hs⟩ := hfin.fg_top
    let g : integralClosure (rA ℂ x {0}) K → (rB ℂ K x {0} ⧸ I) := fun y => mk ⟨y.1, y.2⟩
    have key : ∀ y, y ∈ Submodule.span (rA ℂ x {0}) (s : Set (integralClosure (rA ℂ x {0}) K)) →
        g y ∈ Submodule.span ℂ (g '' (s : Set (integralClosure (rA ℂ x {0}) K))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero =>
        have h0 : g 0 = 0 := map_zero mk
        rw [h0]
        exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : g (a + b) = g a + g b := by
          simp only [g, ← map_add]
          rfl
        rw [this]
        exact Submodule.add_mem _ ha hb
      | smul a y _ hy =>
        obtain ⟨c, hc1⟩ := hA a.1 a.2
        have e : (⟨(a • y).1, (a • y).2⟩ : rB ℂ K x {0}) = ⟨_, hmem a.1 a.2⟩ * ⟨y.1, y.2⟩ :=
          Subtype.ext (Algebra.smul_def a y.1)
        have : g (a • y) = c • g y :=
          (congrArg mk e).trans (by rw [map_mul, hc1, Algebra.smul_def])
        rw [this]
        exact Submodule.smul_mem _ _ hy
    refine ⟨⟨(s.image g), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    have := key ⟨b.1, b.2⟩ (hs ▸ Submodule.mem_top)
    rw [Finset.coe_image]
    exact this
  have hker : ∀ e : fib ℂ K x, ∀ a ∈ I, e.1 a = 0 := by
    intro e a ha
    have : I ≤ RingHom.ker (e.1 : rB ℂ K x {0} →+* ℂ) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      exact e.2 j
    exact this ha
  let L : fib ℂ K x → ((rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ) := fun e => Ideal.Quotient.liftₐ I e.1 (hker e)
  have hL : ∀ e b, L e (mk b) = e.1 b := fun e b => by
    first | rfl | exact Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective L := by
    intro e e' h
    refine Subtype.ext (AlgHom.ext fun b => ?_)
    rw [← hL, ← hL, h]
  have li : LinearIndependent ℂ (fun e => (L e).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap' ℂ (rB ℂ K x {0} ⧸ I) ℂ).comp L hinj
  have hF : Finite (fib ℂ K x) := li.finite
  refine ⟨hF, fun v => ?_⟩
  obtain ⟨q, hq⟩ := exists_of_li _ li v
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨b, fun e => ?_⟩
  rw [← hq e, ← hL]
  rfl

theorem UpperTheory.Gal.productCup_of_system.cRT_of :
    CRT := by
  intro F K _ _ _ _ _ _ d x hc
  exact chineseRemainder_finiteCover (xv x) hc
