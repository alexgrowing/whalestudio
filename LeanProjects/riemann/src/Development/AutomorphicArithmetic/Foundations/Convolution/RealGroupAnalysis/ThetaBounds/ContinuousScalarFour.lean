import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FiniteFamilyOfCompact
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAdeleInfHom

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {F : Type} [Field F] [NumberField F]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_mono'' {F : Type} [Field F] [NumberField F]
    {S S' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : S ⊆ S') (N : ℕ) (v : V4 F) :
    wt S N v ≤ wt S' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ S
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private noncomputable def sc4 {F : Type} [Field F] [NumberField F] : (A F)ˣ →* GL (Fin 4) (A F) :=
  Units.map (Matrix.scalar (Fin 4) : A F →+* Matrix (Fin 4) (Fin 4) (A F)).toMonoidHom

private theorem continuous_scalarFour {F : Type} [Field F] [NumberField F] :
    Continuous (sc4 (F := F)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun a : A F => Matrix.scalar (Fin 4) a
  simp only [Matrix.scalar_apply]
  exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)

private theorem scalarFour_mulVec {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (v : V4 F) :
    (sc4 a).val *ᵥ v = fun i => (a : A F) * v i := by
  funext i
  change (Matrix.scalar (Fin 4) (a : A F) *ᵥ v) i = _
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem UpperTheory.ConvolutionTheory.R2.Ff.omCpt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmCpt W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ C hC
  obtain ⟨-, hIw⟩ := iwa F
  obtain ⟨U, hUc, hU⟩ := hIw C hC
  obtain ⟨n, e, he⟩ := omFin F E D W φ hφ
  have hdom : ∀ i, Dom (Set.univ : Set Unit) fun _ => (e i).1 := fun i => (wtBound F (e i)).2
  choose Ki hKi hB using hdom
  have hK : IsCompact (⋃ i, Ki i) := isCompact_iUnion hKi
  obtain ⟨K', hK', hlin⟩ := wtLin F (sc4 '' U) (hUc.image continuous_scalarFour) _ hK
  obtain ⟨m, hm⟩ := (hUc.image (M.continuous_ab (F := F))).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hBl⟩ := hlin N
  choose Bi hBi using fun i => hB i N
  refine ⟨max m 0 ^ 2 * ((∑ i, |Bi i|) * |B|), fun g hg v => ?_⟩
  obtain ⟨b, a, ha, k, hk, rfl⟩ := hU g hg
  obtain ⟨c, hc, hsum⟩ := he k hk
  have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
    have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, W.η_sq a, Units.val_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by rw [← norm_pow, h2, norm_one])
  set w : V4 F := fun i => (a : A F) * v i with hw
  have hψ : ∀ x : A F, ‖ψ x‖ = 1 := fun x => Circle.norm_coe _
  have h1 : ‖(W.Om (nU b * mD a * k) φ).1 v‖ = ab a ^ 2 * ‖(W.Om k φ).1 w‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, W.Om_n, W.Om_m, norm_mul,
      hψ, one_mul, norm_mul, norm_mul, hη, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have h2 : (W.Om k φ).1 w = ∑ i, c i * (e i).1 w := by
    rw [hsum]
    simp [Finset.sum_apply]
  have hlinw : wt (⋃ i, Ki i) N w ≤ |B| * wt K' N v := by
    have := hBl (sc4 a) ⟨a, ha, rfl⟩ v
    rw [scalarFour_mulVec] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (wt_nonneg' _ _ _))
  have h3 : ‖(W.Om k φ).1 w‖ ≤ (∑ i, |Bi i|) * (|B| * wt K' N v) := by
    rw [h2, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    calc ‖c i‖ * ‖(e i).1 w‖ ≤ 1 * ‖(e i).1 w‖ :=
          mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
      _ = ‖(e i).1 w‖ := one_mul _
      _ ≤ Bi i * wt (Ki i) N w := hBi i () (Set.mem_univ _) w
      _ ≤ |Bi i| * wt (Ki i) N w :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ |Bi i| * wt (⋃ i, Ki i) N w :=
          mul_le_mul_of_nonneg_left (wt_mono'' (Set.subset_iUnion Ki i) N w) (abs_nonneg _)
      _ ≤ |Bi i| * (|B| * wt K' N v) := mul_le_mul_of_nonneg_left hlinw (abs_nonneg _)
  have h4 : ab a ^ 2 ≤ max m 0 ^ 2 :=
    pow_le_pow_left₀ (M.ab_pos a).le ((hm ⟨a, ha, rfl⟩).trans (le_max_left _ _)) 2
  rw [h1]
  calc ab a ^ 2 * ‖(W.Om k φ).1 w‖
      ≤ max m 0 ^ 2 * ((∑ i, |Bi i|) * (|B| * wt K' N v)) :=
        mul_le_mul h4 h3 (norm_nonneg _) (by positivity)
    _ = max m 0 ^ 2 * ((∑ i, |Bi i|) * |B|) * wt K' N v := by ring
