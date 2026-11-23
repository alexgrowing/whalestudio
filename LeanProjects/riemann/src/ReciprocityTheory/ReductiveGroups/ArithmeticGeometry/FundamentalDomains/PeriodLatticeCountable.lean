import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainTranslate

namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Lattice

variable (X : Data E r) (la : Wt X.Ψ r)

noncomputable def perB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (perL X la)) ℝ (X.Ψ → ℝ) :=
  (Module.Free.chooseBasis ℤ (perL X la)).ofZLatticeBasis ℝ (perL X la)

theorem perB_span : (Submodule.span ℤ (Set.range (perB X la))).toAddSubgroup = X.periods la := by
  rw [perB, Module.Basis.ofZLatticeBasis_span]
  rfl

instance periods_countable : Countable (X.periods la) := inferInstanceAs (Countable (perL X la))

theorem fd_exists : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧
    IsAddFundamentalDomain (X.periods la) D volume ∧ 0 < volume D ∧ volume D < ⊤ := by
  refine ⟨ZSpan.fundamentalDomain (perB X la), ZSpan.fundamentalDomain_measurableSet _, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain (perB X la) volume
    rw [← perB_span X la]
    exact h
  · exact pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero _)
  · exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top

theorem compact_reps : ∃ K : Set (X.Ψ → ℝ), IsCompact K ∧ ∀ s, ∃ p ∈ X.periods la, s - p ∈ K := by
  refine ⟨closure (ZSpan.fundamentalDomain (perB X la)),
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure, fun s => ?_⟩
  refine ⟨(ZSpan.floor (perB X la) s : X.Ψ → ℝ), ?_, subset_closure ?_⟩
  · rw [← perB_span X la]
    exact (ZSpan.floor (perB X la) s).prop
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _

end Lattice

section Glue

variable (X : Data E r) (u : Fin 2 → Fin r → E)

def e00 (s : X.Ψ → ℝ) : X.Ψ → Fin 2 → Fin 2 → ℂ := fun τ i k => if i = 0 ∧ k = 0 then (s τ : ℂ) else 0

theorem diag_unit_family_hermitian (s : X.Ψ → ℝ) : IsHermFam (e00 X s) := by
  intro τ i k
  unfold e00
  by_cases h : i = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬ (k = 0 ∧ i = 0) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [h, h']

theorem flow_eq_Zb (s : X.Ψ → ℝ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) y = X.Zb u (e00 X s) y := by
  funext τ
  simp only [Data.flow, Data.Zb]
  congr 1
  ext a j
  simp [Data.flowMat, Data.zmat, e00, Fin.sum_univ_two, Data.emb, cR]
  ring

theorem real_pairing_diag_unit (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (s : X.Ψ → ℝ) :
    X.pairR χ (e00 X s) = ∑ τ, (χ τ 0 0).re * s τ := by
  simp [Data.pairR, e00, Fin.sum_univ_two, Complex.re_sum]

theorem flow_Zb_comm (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) (s : X.Ψ → ℝ)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) (X.Zb u b y) = X.Zb u b (X.flow (u 0) (cR X s) y) := by
  funext τ
  obtain ⟨W, hW⟩ : ∃ W : Fin 2 → Fin r → ℂ,
      W = fun k j => ∑ l, τ.1 (X.Gm j l) * conj (τ.1 (u k l)) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Fin 2 → Fin r → ℂ, V = fun i a => τ.1 (u i a) := ⟨_, rfl⟩

  have hk : ∀ i k : Fin 2, ∑ j, W k j * V i j = 0 := by
    intro i k
    have h := congrArg τ.1 (hu i k)
    simp only [herm, map_sum, map_mul, emb_cc, map_zero] at h
    rw [← h, hW, hV]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  set α : ℂ := I * X.c τ * cR X s τ
  set γ : ℂ := I * X.c τ
  let A : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => α * V 0 a * W 0 j
  let B : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => γ * ∑ i, ∑ k, b τ i k * V i a * W k j
  have hF : X.flowMat (u 0) τ (cR X s τ) = 1 - A := by
    ext a j
    simp only [Data.flowMat, A, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, α]
  have hZ : X.zmat u b τ = 1 - B := by
    ext a j
    simp only [Data.zmat, B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, γ,
      Data.emb]
  have hAB : A * B = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, α * V 0 a * W 0 m * (γ * ∑ i, ∑ k, b τ i k * V i m * W k j)
        = ∑ i, ∑ k, (α * V 0 a * γ * b τ i k * W k j) * ∑ m, W 0 m * V i m := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have hBA : B * A = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, γ * (∑ i, ∑ k, b τ i k * V i a * W k m) * (α * V 0 m * W 0 j)
        = ∑ i, ∑ k, (γ * b τ i k * V i a * α * W 0 j) * ∑ m, W k m * V 0 m := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have key : X.flowMat (u 0) τ (cR X s τ) * X.zmat u b τ =
      X.zmat u b τ * X.flowMat (u 0) τ (cR X s τ) := by
    rw [hF, hZ]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hAB, hBA]
    abel
  show X.flowMat (u 0) τ (cR X s τ) * (X.zmat u b τ * mat y τ) =
    X.zmat u b τ * (X.flowMat (u 0) τ (cR X s τ) * mat y τ)
  rw [← Matrix.mul_assoc, key, Matrix.mul_assoc]

theorem Zb_cont (y : Frame X.Ψ r) : Continuous fun b : X.Ψ → Fin 2 → Fin 2 → ℂ => X.Zb u b y := by
  refine continuous_pi fun τ => ?_
  simp only [Data.Zb, Data.zmat]
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

end Glue

end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
