import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import GroundTheory.GlobalFields.KummerTheory.Splitting

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section Group

variable {G : Type} [Group G] [MeasurableSpace G]

private theorem cv_unit (μ : Measure G) (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (h1 : μ (K : Set G) = 1) :
    cv μ ((K : Set G).indicator 1) ((K : Set G).indicator 1) = (K : Set G).indicator (1 : G → ℂ) := by
  funext x
  by_cases hx : x ∈ K
  · have e : (fun y => (K : Set G).indicator (1 : G → ℂ) y * (K : Set G).indicator (1 : G → ℂ) (y⁻¹ * x)) =
        (K : Set G).indicator (fun _ => (1 : ℂ)) := by
      funext y
      by_cases hy : y ∈ K
      · have hyx : y⁻¹ * x ∈ K := K.mul_mem (K.inv_mem hy) hx
        simp [Set.indicator_of_mem, SetLike.mem_coe, hy, hyx]
      · simp [Set.indicator_of_notMem, SetLike.mem_coe, hy]
    simp only [cv]
    rw [e, integral_indicator hK]
    simp [Measure.real, h1, SetLike.mem_coe, hx]
  · have e : (fun y => (K : Set G).indicator (1 : G → ℂ) y * (K : Set G).indicator (1 : G → ℂ) (y⁻¹ * x)) =
        fun _ => 0 := by
      funext y
      by_cases hy : y ∈ K
      · have hyx : y⁻¹ * x ∉ K := fun h => hx (by simpa using K.mul_mem hy h)
        simp [SetLike.mem_coe, hyx]
      · simp [SetLike.mem_coe, hy]
    simp only [cv]
    rw [e]
    simp [SetLike.mem_coe, hx]

private theorem cvAll_unit (μ : Measure G) (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (h1 : μ (K : Set G) = 1) (m : ℕ) (φ : Fin (m + 1) → G → ℂ)
    (hφ : ∀ i, φ i = (K : Set G).indicator 1) : cvAll μ m φ = (K : Set G).indicator 1 := by
  induction m with
  | zero => exact hφ 0
  | succ m ih =>
    simp only [cvAll]
    rw [ih (Fin.tail φ) (fun i => hφ _), hφ 0]
    exact cv_unit μ K hK h1

end Group

private theorem ind_props {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    Continuous ((K : Set G).indicator (1 : G → ℂ)) ∧ HasCompactSupport ((K : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (K : Set G) := K.isClosed_of_isOpen ho
  refine ⟨(IsClopen.continuous_indicator ⟨hcl, ho⟩ continuous_const), ?_⟩
  refine hc.of_isClosed_subset (isClosed_closure) ?_
  refine closure_minimal (fun x hx => ?_) hcl
  by_contra h
  exact hx (Set.indicator_of_notMem h _)

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.unitSplit :
    UpperTheory.ConvolutionTheory.L1.UnitSplit := by
  intro F E _ _ _ _ _ _ σ hσ n v hs
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E (v := v)
  obtain ⟨w, -, hw⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n v w₀ hs
  intro _ _ _ _ mE mF hE hF h1E h1F
  have hh : ∀ u : PlacesOver E v,
      Continuous ((GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ)) ∧
      HasCompactSupport ((GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ)) := fun u =>
    ind_props _ (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)
  have key := hw (fun u => (GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ))
    hh mF hF h1F mE mF hE hF h1E h1F
  have e1 : GM.prodFn (n := n) (fun u : PlacesOver E v => (GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ)) =
      (unitSet E n v).indicator 1 := by
    funext g
    rw [GM.prodFn, finprod_eq_prod_of_fintype]
    by_cases hg : g ∈ unitSet E n v
    · rw [Set.indicator_of_mem hg]
      refine Finset.prod_eq_one fun u _ => ?_
      exact Set.indicator_of_mem (hg u) _
    · rw [Set.indicator_of_notMem hg]
      obtain ⟨u, hu⟩ : ∃ u : PlacesOver E v, GM.cmp u g ∉ GLnLocal.integralGL (u.1.adicCompletion E) n := by
        by_contra h
        push_neg at h
        exact hg h
      exact Finset.prod_eq_zero (Finset.mem_univ u) (Set.indicator_of_notMem hu _)
  have e2 : cvAll mF m (fun i g => (GLnLocal.integralGL ((w i).1.adicCompletion E) n : Set (GL (Fin n) ((w i).1.adicCompletion E))).indicator (1 : GL (Fin n) ((w i).1.adicCompletion E) → ℂ)
        (mapGL n (completionMap v (w i).1) g)) =
      (GLnLocal.integralGL (v.adicCompletion F) n : Set (GL (Fin n) (v.adicCompletion F))).indicator 1 := by
    refine cvAll_unit mF _ (GLnLocal.isOpen_integralGL _ n).measurableSet h1F m _ fun i => ?_
    funext g
    have hi := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v (w i) (hs (w i)) n).2.1 g
    by_cases hg : g ∈ GLnLocal.integralGL (v.adicCompletion F) n
    · rw [Set.indicator_of_mem (show g ∈ (_ : Set _) from hg), Set.indicator_of_mem (show _ ∈ (_ : Set _) from hi.2 hg)]
      rfl
    · rw [Set.indicator_of_notMem (show g ∉ (_ : Set _) from hg), Set.indicator_of_notMem (show _ ∉ (_ : Set _) from fun h => hg (hi.1 h))]
  rw [e1, e2] at key
  exact key
