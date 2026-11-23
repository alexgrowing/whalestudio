import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in

theorem bor_eq_pi (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    Bor Ψ r = Set.univ.pi fun _ : Ψ => Set.univ.pi fun a : Fin r => Set.univ.pi fun c : Fin r =>
      if c < a then ({0} : Set ℂ) else if c = a then ({0}ᶜ : Set ℂ) else Set.univ := by
  ext b
  simp only [Bor, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun τ => ?_
  constructor
  · rintro ⟨hd, hu⟩ a c
    have hbt : (mat b τ).BlockTriangular id := fun i j h => hu i j h
    rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff] at hd
    split_ifs with h1 h2
    · exact hu a c h1
    · subst h2
      exact hd c (Finset.mem_univ _)
    · trivial
  · intro h
    have hu : ∀ a c : Fin r, c < a → b τ a c = 0 := by
      intro a c hc
      have := h a c
      rwa [if_pos hc] at this
    have hbt : (mat b τ).BlockTriangular id := fun i j h => hu i j h
    refine ⟨?_, hu⟩
    rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff]
    intro a _
    have := h a a
    rwa [if_neg (lt_irrefl a), if_pos rfl] at this

omit [NumberField E] [IsCMField E] in

theorem isPreconnected_bor (Ψ : Finset (E →+* ℂ)) (r : ℕ) : IsPreconnected (Bor Ψ r) := by
  rw [bor_eq_pi]
  refine isPreconnected_univ_pi fun _ => isPreconnected_univ_pi fun a =>
    isPreconnected_univ_pi fun c => ?_
  split_ifs
  · exact isPreconnected_singleton
  · refine (isConnected_compl_singleton_of_one_lt_rank ?_ (0 : ℂ)).isPreconnected
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  · exact isPreconnected_univ

omit [NumberField E] [IsCMField E] in

theorem continuous_rmul_pair (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    Continuous fun p : Frame Ψ r × Frame Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem frames_isConnected :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GGConnStatement (E := E) := by
  intro E _ _ _ r X
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  obtain ⟨Δ, zOf, bOf, -, hdense, -, -, hsplit, -⟩ := lu_holds r X (x0F X) ho
  have hn : Continuous (nmat X) := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    unfold nmat
    split_ifs <;> fun_prop
  have hc : Continuous (cpt X (x0F X)) :=
    (continuous_rmul_pair X.Ψ r).comp (continuous_const.prodMk hn)
  have hF : Continuous fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X (x0F X) p.1) p.2 :=
    (continuous_rmul_pair X.Ψ r).comp ((hc.comp continuous_fst).prodMk continuous_snd)
  have hcell := ((OmFConnStatement_holds r X (x0F X) ho).prod
    (isPreconnected_bor X.Ψ r)).image _ hF.continuousOn
  refine ⟨⟨_, OFC.radialRetraction_mem_chart X (x0F X) ho 0 0⟩, hcell.subset_closure ?_ ?_⟩
  · rintro _ ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    exact OntoS.dom_rmul X hz hb
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨ε0, hε0, hb⟩ := Metric.isOpen_iff.mp (FourierCoefficientDomain.isOpen_dom X) x hx
    obtain ⟨y, hy, hΔ⟩ := hdense x hx (min ε ε0) (lt_min hε hε0)
    obtain ⟨hz, hb', hye⟩ := hsplit y (hb (Metric.ball_subset_ball (min_le_right _ _) hy)) hΔ
    refine ⟨y, ⟨(zOf y, bOf y), ⟨hz, hb'⟩, hye.symm⟩, ?_⟩
    rw [dist_comm]
    exact lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)

end GlobalTheory
