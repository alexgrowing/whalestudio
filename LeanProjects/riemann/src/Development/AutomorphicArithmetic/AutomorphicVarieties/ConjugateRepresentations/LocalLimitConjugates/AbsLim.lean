import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem tendsto_zero_on_closure_of_lipschitz_family {H : Type} [NormedAddCommGroup H] (Q : ℕ → H → H)
    (hQ : ∀ k x y, ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖) (S : Set H)
    (hS : ∀ x ∈ S, Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0)) (x : H)
    (hx : x ∈ closure S) :
    Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hS y hyS) (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [dist_zero_right] at h1 ⊢
  rw [dist_eq_norm] at hxy
  calc ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖ := hQ k x y
    _ < ε / 2 + ε / 2 := add_lt_add h1 hxy
    _ = ε := by ring

theorem UpperTheory.V.Cj.H.absLim :
    UpperTheory.V.Cj.H.AbsLim := by
  intro H _ _ _ D A hA s hs hplus hminus T hT hTb P hP hPr w
  have hc : ∀ k, ‖(Complex.I * (s k : ℂ))‖ = |s k| := by
    intro k
    simp
  have hadj : ∀ k (v' : D), ContinuousLinearMap.adjoint (T k)
      ((A v' : H) - (Complex.I * (s k : ℂ)) • (v' : H)) = (v' : H) := by
    intro k v'
    apply sub_eq_zero.mp
    apply hplus k
    intro v
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hT k v]
    rw [inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right, hA v' v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hPfix : ∀ k, (Complex.I * (s k : ℂ)) • T k (P w) = P w := by
    intro k
    apply sub_eq_zero.mp
    apply hminus k
    intro v
    have h1 : inner ℂ (T k (P w)) ((A v : H) - (Complex.I * (s k : ℂ)) • (v : H))
        = inner ℂ (P w) (v : H) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hadj k v]
    rw [inner_sub_left, inner_smul_left, h1, inner_sub_right, inner_smul_right, hP w v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hr : Filter.Tendsto (fun k => (Complex.I * (s k : ℂ)) • T k (w - P w)) Filter.atTop
      (nhds 0) := by
    refine tendsto_zero_on_closure_of_lipschitz_family (fun k x => (Complex.I * (s k : ℂ)) • T k x) ?_
      (Set.range fun v : D => (A v : H)) ?_ (w - P w) ?_
    · intro k x y
      have e : (Complex.I * (s k : ℂ)) • T k x = (Complex.I * (s k : ℂ)) • T k y
          + (Complex.I * (s k : ℂ)) • T k (x - y) := by
        rw [map_sub, smul_sub]
        abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, hc]
      exact hTb k (x - y)
    · rintro _ ⟨v, rfl⟩
      have e : ∀ k, (Complex.I * (s k : ℂ)) • T k (A v : H) = (Complex.I * (s k : ℂ)) • (v : H)
          - (Complex.I * (s k : ℂ)) • ((Complex.I * (s k : ℂ)) • T k (v : H)) := by
        intro k
        have h := hT k v
        rw [map_add, map_smul] at h
        rw [eq_sub_iff_add_eq, ← smul_add, h]
      apply squeeze_zero_norm (a := fun k => 2 * |s k| * ‖(v : H)‖)
      · intro k
        rw [e k]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, norm_smul, hc]
        have h2 := mul_le_mul_of_nonneg_left (hTb k (v : H)) (abs_nonneg (s k))
        linarith
      · have h3 : Filter.Tendsto (fun k => |s k|) Filter.atTop (nhds 0) := by
          simpa using hs.abs
        have h4 := (h3.const_mul 2).mul_const ‖(v : H)‖
        rwa [mul_zero, zero_mul] at h4
    · have h := hPr w
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at h
      exact h
  have hsum : ∀ k, (Complex.I * (s k : ℂ)) • T k w
      = P w + (Complex.I * (s k : ℂ)) • T k (w - P w) := by
    intro k
    rw [map_sub, smul_sub, hPfix k]
    abel
  have h5 := (tendsto_const_nhds (x := P w) (f := Filter.atTop)).add hr
  rw [add_zero] at h5
  exact h5.congr (fun k => (hsum k).symm)
