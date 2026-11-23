import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem analyticAt_entry_tail {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ) (p q : Fin 2) :
    AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => g (Fin.tail z') p q) z := by
  have hT : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => (Fin.tail z' : Fin d → ℂ)) z := by
    rw [analyticAt_pi_iff]
    intro i
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).analyticAt z
  have hA : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail z) :=
    ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
  exact hA.comp hT

theorem analyticAt_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ)
    (h : den (g (Fin.tail z)) (z 0) ≠ 0) : AnalyticAt ℂ (mob1 g) z := by
  have hc0 : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => z' 0) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt z
  have e := analyticAt_entry_tail g hg z
  have hnum : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ =>
      g (Fin.tail z') 1 0 + g (Fin.tail z') 1 1 * z' 0) z := (e 1 0).add ((e 1 1).mul hc0)
  have hden : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => den (g (Fin.tail z')) (z' 0)) z :=
    (e 0 0).add ((e 0 1).mul hc0)
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hnum.div hden h
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) j.succ).analyticAt z

theorem hasDerivAt_mob_shift (m : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den m a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob m (a + t)) (mobD m a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => m 1 0 + m 1 1 * (a + t)) (m 1 1 * 1) 0 :=
    (hl.const_mul (m 1 1)).const_add (m 1 0)
  have hd : HasDerivAt (fun t : ℂ => den m (a + t)) (m 0 1 * 1) 0 :=
    (hl.const_mul (m 0 1)).const_add (m 0 0)
  have h0 : den m (a + 0) ≠ 0 := by simpa using h
  have hq := hn.div hd h0
  have e1 : (m 1 1 * 1 * den m (a + 0) - (m 1 0 + m 1 1 * (a + 0)) * (m 0 1 * 1)) / den m (a + 0) ^ 2 =
      mobD m a := by
    simp only [add_zero, mobD, Matrix.det_fin_two]
    congr 1
    simp only [den]
    ring
  rw [e1] at hq
  exact hq

theorem det_jacobian_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a : ℂ)
    (h : den (g y) a ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob1 g) (Fin.cons a y : Fin (d + 1) → ℂ)).det = mobD (g y) a := by
  set z : Fin (d + 1) → ℂ := Fin.cons a y with hz
  have htail : (Fin.tail z : Fin d → ℂ) = y := Fin.tail_cons _ _
  have hz0 : z 0 = a := Fin.cons_zero _ _
  have hF : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z) z :=
    (analyticAt_mobius_first g hg z (by rwa [htail, hz0])).differentiableAt.hasFDerivAt

  have hrow : ∀ (i : Fin d) (v : Fin (d + 1) → ℂ), fderiv ℂ (mob1 g) z v i.succ = v i.succ := by
    intro i v
    have h1 := (hasFDerivAt_pi'.1 hF) i.succ
    have h2 : HasFDerivAt (fun z' : Fin (d + 1) → ℂ => mob1 g z' i.succ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ) z :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).hasFDerivAt
    exact DFunLike.congr_fun (h1.unique h2) v

  have hcorner : fderiv ℂ (mob1 g) z (Pi.single 0 1) 0 = mobD (g y) a := by
    have hc : HasDerivAt (fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ))
        (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single 0 1 : Fin (d + 1) → ℂ)).const_add z
    have hF' : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z)
        (z + (0 : ℂ) • (Pi.single 0 1 : Fin (d + 1) → ℂ)) := by simpa using hF
    have hcomp := hF'.comp_hasDerivAt (0 : ℂ) hc
    have h0 := (hasDerivAt_pi.1 hcomp) 0
    have hline : ∀ t : ℂ, (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0 =
        mob (g y) (a + t) := by
      intro t
      have ht : (Fin.tail (z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) : Fin d → ℂ) = y := by
        rw [← htail]
        funext i
        simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
      simp only [Function.comp, mob1, Fin.cons_zero, ht]
      simp [hz0]
    have h3 : HasDerivAt (fun t : ℂ => (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0)
        (mobD (g y) a) 0 := by
      simpa only [hline] using hasDerivAt_mob_shift (g y) a h
    exact h0.unique h3
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz1 : ∀ i : Fin d, ReciprocityTheory.AnForm.A.jacC (mob1 g) z i.succ 0 = 0 := by
    intro i
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Fin.succ_ne_zero]
  have hminor : (ReciprocityTheory.AnForm.A.jacC (mob1 g) z).submatrix (Fin.succAbove 0) Fin.succ = 1 := by
    ext i j
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Matrix.one_apply, Fin.succ_inj]
  simp only [hz1, hminor]
  simp [ReciprocityTheory.AnForm.A.jacC, hcorner]

theorem analyticAt_mobius_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧
      (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det =
        GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  intro d g hg y a h
  refine ⟨analyticAt_mobius_first g hg _ ?_, det_jacobian_mobius_first g hg y a h⟩
  rwa [Fin.tail_cons, Fin.cons_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
