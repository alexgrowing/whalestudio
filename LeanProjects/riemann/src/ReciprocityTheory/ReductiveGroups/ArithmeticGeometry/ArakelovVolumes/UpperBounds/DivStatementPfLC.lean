import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_zero' (τ : X.Ψ) : mat (nmat X (0 : V (nd X))) τ = 1 := by
  ext a b
  by_cases h : b < a
  · have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
    simp [mat, nmat, h, hab, Matrix.one_apply]
    rfl
  · by_cases hab : a = b
    · subst hab; simp [mat, nmat]
    · simp [mat, nmat, h, hab, Matrix.one_apply]

theorem cpt_zero' (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show mat x0 τ * mat (nmat X (0 : V (nd X))) τ = x0 τ
  rw [nmat_zero', mul_one]
  rfl

theorem nmat_zero_mem : nmat X (0 : V (nd X)) ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · rw [nmat_zero']; simp
  · simp [nmat, hca]
    rfl

theorem lact_one' (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp only [lact, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul]
  rfl

theorem s_xs_zero {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 := by
  have he : Fl.xs j = lact (1 : GL (Fin r) E) (rmul (Fl.xs j) (nmat X 0)) := by
    rw [lact_one']
    exact (cpt_zero' X (Fl.xs j)).symm
  exact (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).mpr ⟨j, 1, X.Γ.one_mem, nmat X 0, nmat_zero_mem X, he⟩ k

theorem anal_loc {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : AnalyticAt ℂ (fun z => P (cpt X x z)) 0 := by
  have hc := OntoB.cd_cpt X x
  have hU : IsOpen {z : V (nd X) | cpt X x z ∈ X.dom} :=
    (FourierCoefficientDomain.isOpen_dom X).preimage hc.continuous
  refine DivLA.analyticAt_of_diffOn hU ?_ (by simpa [cpt_zero'] using hx)
  exact hP.comp (hc.differentiable (by simp)).differentiableOn (fun z hz => hz)

theorem leadM_succ {n δ : ℕ} (s : Fin n → Frame X.Ψ r → ℂ) (w0 : Frame X.Ψ r → ℂ)
    (t : Fin δ → Frame X.Ψ r → ℂ) (T d : ℕ) (cc cc' cnew : (Fin n → ℕ) → Fin δ → ℂ)
    (h1 : ∀ α ∈ Finset.Nat.antidiagonalTuple n d, cc' α = cnew α)
    (h2 : ∀ α, α ∉ Finset.Nat.antidiagonalTuple n d → cc' α = cc α) (y : Frame X.Ψ r) :
    leadM X s w0 t T (d + 1) cc' y =
      leadM X s w0 t T d cc y + ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, cnew α k * monoM X s α y * w0 y ^ (T - d) * t k y := by
  have hU : ReciprocityTheory.ChartRestriction.G.AR.multiLt n (d + 1) =
      ReciprocityTheory.ChartRestriction.G.AR.multiLt n d ∪ Finset.Nat.antidiagonalTuple n d := by
    unfold ReciprocityTheory.ChartRestriction.G.AR.multiLt
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
  have hD : Disjoint (ReciprocityTheory.ChartRestriction.G.AR.multiLt n d) (Finset.Nat.antidiagonalTuple n d) := by
    rw [Finset.disjoint_left]
    intro α h1 h2
    simp only [ReciprocityTheory.ChartRestriction.G.AR.multiLt, Finset.mem_biUnion, Finset.mem_range,
      Finset.Nat.mem_antidiagonalTuple] at h1 h2
    obtain ⟨e, he, he'⟩ := h1
    omega
  unfold leadM
  rw [hU, Finset.sum_union hD]
  congr 1
  · apply Finset.sum_congr rfl
    intro α hα
    rw [h2 α (Finset.disjoint_left.mp hD hα)]
  · apply Finset.sum_congr rfl
    intro α hα
    rw [h1 α hα, Finset.Nat.mem_antidiagonalTuple.mp hα]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
