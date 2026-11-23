import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.PullSchLI
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PullSch

theorem exists_mul_eq_one_of_linearIndependent {K : Type} [Field K] {r n : ℕ} (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c) : ∃ d : Matrix (Fin n) (Fin r) K, c * d = 1 := by
  have hinj : Function.Injective (Matrix.toLin' cᵀ) := by
    intro v w hvw
    have h1 : ∀ u : Fin r → K, Matrix.toLin' cᵀ u = ∑ i, u i • c i := by
      intro u
      funext j
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h1, h1] at hvw
    have h2 := Fintype.linearIndependent_iff.1 hc (v - w) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hvw, sub_self])
    funext i
    exact sub_eq_zero.1 (h2 i)
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' cᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' h)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' h * cᵀ = 1 := by
    rw [← LinearMap.toMatrix'_toLin' cᵀ, ← LinearMap.toMatrix'_comp, hh, LinearMap.toMatrix'_id]
  rw [← Matrix.transpose_transpose c, ← Matrix.transpose_mul, e, Matrix.transpose_one]

theorem mul_map_finPart (D : D7) {m r n : ℕ} (x : Mx D m r) (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    (x * C).map (finPart D) * Dm.map (finPart D) = x.map (finPart D) := by
  have e1 : x = x * C * Dm := by rw [Matrix.mul_assoc, hCD, Matrix.mul_one]
  conv_rhs => rw [e1]
  simp only [Matrix.map_mul]

theorem exists_finPart_section (D : D7) :
    ∃ s : Af D.host.F ⊗[D.host.F] D.host.E → AE D, Continuous s ∧ ∀ a, finPart D (s a) = a := by
  obtain ⟨e, he, -, hes⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨fun a => e.symm (0, a), hes.comp (continuous_const.prodMk continuous_id), fun a => ?_⟩
  have h := (he (e.symm (0, a))).2
  have h2 : (e (e.symm (0, a))).2 = a := by simp
  exact h.symm.trans h2

theorem continuous_lift_mul (D : D7) {m n r : ℕ} (Dm : Mx D n r) (s : Af D.host.F ⊗[D.host.F] D.host.E → AE D)
    (hs : Continuous s) :
    Continuous (fun z : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (z.map s * Dm).map (finPart D)) :=
  ((continuous_id.matrix_map hs).matrix_mul continuous_const).matrix_map (GlobalTheory.Member.continuous_finPart D)

def mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Mx D m r →+ Mx D m n where
  toFun y := y * C
  map_zero' := Matrix.zero_mul _
  map_add' a b := Matrix.add_mul a b C

theorem mulR_apply (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (y : Mx D m r) : mulR D m C y = y * C := rfl

theorem continuous_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Continuous (mulR D m C) :=
  continuous_id.matrix_mul continuous_const

theorem injective_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    Function.Injective (mulR D m C) := fun a b h => by
  have h' : a * C * Dm = b * C * Dm := congrArg (· * Dm) h
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, hCD, Matrix.mul_one, Matrix.mul_one] at h'

theorem isRealParam_mulR_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (L : (Fin k → ℝ) →+ Mx D m r)
    (hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L) : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam ((mulR D m C).comp L) := by
  refine ⟨(continuous_mulR D m C).comp hL.1, fun t => ?_⟩
  rw [AddMonoidHom.comp_apply, mulR_apply, Matrix.map_mul, hL.2 t, Matrix.zero_mul]

theorem injective_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1)
    (L : (Fin k → ℝ) →+ Mx D m r) (hL : Function.Injective L) : Function.Injective ((mulR D m C).comp L) := by
  intro a b h
  exact hL (injective_mulR D m C Dm hCD h)

theorem pullSchLI : PositivityTheory.GramSchwartzFunctions.PullSchLI := by
  intro D θ hθ m r n c hc φ hφ
  obtain ⟨d, hcd⟩ := exists_mul_eq_one_of_linearIndependent c hc
  rw [← GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA D θ hθ] at hφ ⊢
  set C : Mx D r n := c.map (incA D) with hC
  set Dm : Mx D n r := d.map (incA D) with hD
  have hCD : C * Dm = 1 := by
    rw [hC, hD, ← Matrix.map_mul, hcd, Matrix.map_one _ (map_zero _) (map_one _)]
  have hpull : ∀ y, pull c φ y = φ (mulR D m C y) := fun y => rfl
  obtain ⟨hlev, hsupp, hsch⟩ := hφ
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨U, hUo, hU⟩ := hlev
    refine ⟨U.comap (mulR D m C), hUo.preimage (continuous_mulR D m C), fun u hu h0 x => ?_⟩
    have h0' : (mulR D m C u).map (infPart D) = 0 := by
      rw [mulR_apply, Matrix.map_mul, h0, Matrix.zero_mul]
    rw [hpull, hpull, map_add, hU _ hu h0']
  · obtain ⟨K, hK, hKs⟩ := hsupp
    obtain ⟨s, hs, hfs⟩ := exists_finPart_section D
    have h1 : ∀ y : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E), (y.map s).map (finPart D) = y :=
      fun y => by
        ext i j
        simp [hfs]
    refine ⟨(fun z => (z.map s * Dm).map (finPart D)) '' K, hK.image (continuous_lift_mul D Dm s hs),
      fun x hx => ⟨(mulR D m C x).map (finPart D), hKs _ hx, ?_⟩⟩
    rw [mulR_apply]
    show ((((x * C).map (finPart D)).map s) * Dm).map (finPart D) = x.map (finPart D)
    rw [Matrix.map_mul (L := ((x * C).map (finPart D)).map s), h1]
    exact mul_map_finPart D x C Dm hCD
  · intro k L hL hLinj x
    obtain ⟨g, hg⟩ := hsch k ((mulR D m C).comp L) (isRealParam_mulR_comp D C L hL)
      (injective_comp D C Dm hCD L hLinj) (mulR D m C x)
    exact ⟨g, fun t => by rw [hg, hpull, map_add, AddMonoidHom.comp_apply]⟩

end GlobalTheory.CompanionTheory.PullSch
