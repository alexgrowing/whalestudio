import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

namespace GlobalTheory.ReadingIndependence

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Theta Formalism.BasicNotions.TH

theorem jInjRd_of_laws {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : JInjRd T j a n := by
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  refine jInjRd_of_wt T hM hj a n (fun p y ψ => ?_)
    (GlobalTheory.Frames.algebraic_laws hS _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ _ _ _ (T.Q.Xo j) T.Q.c _ _ ψ y

theorem sum_toLp_ae {α : Type} [MeasurableSpace α] (μ : Measure α) {m : ℕ} (φ : Fin m → α → ℂ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (g : Fin m → ℂ) (s : Finset (Fin m)) :
    ((∑ i ∈ s, g i • (hφ i).toLp (φ i) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] ∑ i ∈ s, g i • φ i := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact Lp.coeFn_zero ℂ 2 μ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add ?_ ih)
    exact (Lp.coeFn_smul _ _).trans (((hφ i).coeFn_toLp).const_smul (g i))

section General

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ}
  {X : Comp → Data E r} (V : HSp D) (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
  (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)

theorem sum_ae {m : ℕ} (b : Fin m → C) (g : Fin m → ℂ) :
    ((∑ i, g i • uniformisationL2 V σ rd dict mu h (b i) : Lp ℂ 2 (muQ1 V)) : AutQ V → ℂ) =ᵐ[muQ1 V]
      onQ V (adel V dict mu (∑ i, g i • rd (b i))) := by
  have e : onQ V (adel V dict mu (∑ i, g i • rd (b i))) = ∑ i, g i • jFn V σ rd dict mu (b i) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul]
    rfl
  rw [e]
  exact sum_toLp_ae (muQ1 V) (fun i => jFn V σ rd dict mu (b i)) (fun i => h (b i)) g Finset.univ

theorem indepToC_of_jInj (hJ : JInj V σ rd dict mu h) : IndepToC rd := by
  intro m b hb
  have h1 := hJ m b hb
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro g hg
  refine h1 g (Lp.eq_zero_iff_ae_eq_zero.2 ?_)
  have := sum_ae V rd dict mu h b g
  rw [hg, map_zero, map_zero] at this
  exact this

end General

theorem jInjRd_of_jInjAt {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) (hJ : JInjAt h j hj a n hd) : JInjRd T j a n :=
  indepToC_of_jInj _ _ _ _ _ hJ

theorem jInjAt_of_aeDom {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n)
    (hae : AeDom (T.U j) T.σ₀ (T.V j T.σ₀) (T.dict j T.σ₀) (T.mu j T.σ₀)) : JInjAt h j hj a n hd := by
  intro m b hb
  have h1 := jInjRd_of_laws T h.toLawsCore.toLawsM hj a n m b hb
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro g hg
  refine h1 g ?_
  have hs := sum_ae (T.V j T.σ₀) (rdC (T.U j) T.σ₀ a n) (T.dict j T.σ₀) (T.mu j T.σ₀)
    (h.cuspidalL2Subspace j hj T.σ₀ T.good_σ₀ a n hd) b g
  rw [hg] at hs
  have hmem : (∑ i, g i • rdC (T.U j) T.σ₀ a n (b i)) ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) a n) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rdC_mem_holSub T.good_σ₀ a n (b i))
  have hz := hae _ _ hmem (hs.symm.trans (Lp.coeFn_zero ℂ 2 _))
  funext k x
  by_cases hx : x ∈ ((T.U j T.σ₀).X k).dom
  · exact hz k x hx
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : rdC (T.U j) T.σ₀ a n (b i) k x = 0 := by
      classical
      exact dif_neg hx
    rw [this, mul_zero]

theorem jInjAt_of_aut {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n)
    (hA : AdelAut (T.V j T.σ₀) (T.dict j T.σ₀) (T.mu j T.σ₀))
    (hP : ∃ p : Measure (GA D (T.V j T.σ₀)) × Set (GA D (T.V j T.σ₀)), IsVolPair D (T.V j T.σ₀) p.1 p.2) :
    JInjAt h j hj a n hd := by
  obtain ⟨th, hr, -, hdU⟩ := h.dictU j hj T.σ₀ T.good_σ₀
  exact jInjAt_of_aeDom h j hj a n hd
    (aeDom_of hA (h.finVol j hj T.σ₀ T.good_σ₀) hP (h.muUnit j hj T.σ₀ T.good_σ₀) hdU)

theorem not_jInjRd_of_const {D : D7} (T : Top D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (y : FrPt (T.Q.Xo j) T.Q.c (CAt T.σ₀)) (hy : ∀ k x, (T.U j T.σ₀).un k x = y)
    (b : Fin 2 → cusp (T.Q.Xo j) T.Q.c (T.U j) a n) (hb : LinearIndependent T.Q.c.F b) :
    ¬ JInjRd T j a n := by
  classical
  intro hJ
  have h1 := hJ 2 b hb
  rw [Fintype.linearIndependent_iff] at h1
  let v : Fin 2 → ℂ := fun i => toC (evR (T.Q.Xo j) T.Q.c (b i).1 y)
  have hv : ∀ i k x, rdC (T.U j) T.σ₀ a n (b i) k x =
      if x ∈ ((T.U j T.σ₀).X k).dom then v i else 0 := by
    intro i k x
    by_cases hx : x ∈ ((T.U j T.σ₀).X k).dom
    · rw [if_pos hx]
      have := rdU_apply_dom (T.U j T.σ₀) (b i).1 k ⟨x, hx⟩
      rw [hy] at this
      exact this
    · rw [if_neg hx]; exact dif_neg hx
  have rel : ∀ g : Fin 2 → ℂ, g 0 * v 0 + g 1 * v 1 = 0 → ∀ i, g i = 0 := by
    intro g hg
    refine h1 g ?_
    funext k x
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hv]
    split_ifs
    · exact hg
    · simp
  have e := rel ![v 1, -v 0] (by simp; ring)
  have e0 : v 0 = 0 := by simpa using e 1
  have := rel ![1, 0] (by simp [e0]) 0
  simp at this

end GlobalTheory.ReadingIndependence
