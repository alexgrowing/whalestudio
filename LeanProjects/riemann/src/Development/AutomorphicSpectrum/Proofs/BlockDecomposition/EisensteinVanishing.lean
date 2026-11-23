import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisZero

open GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks (pairing gramQ mmul)

variable {D : D7} {m : ℕ}

theorem heis_zy (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {n : ℕ} (y : Mx D V.rank n) (Φ : Mx D V.rank n → ℂ)
    (z : Mx D V.rank n) : EC.Heisenberg₂ ψ V (zy y) Φ z = pairing V.gram ψ z y * Φ z := by
  have hx : xPart (zy y) = 0 := by
    ext i j
    simp only [xPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Matrix.zero_apply]
  have hy : yPart (zy y) = y := by
    ext i j
    simp only [yPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  have hin : ∀ x : Mx D V.rank n, GlobalTheory.StdUnn.inner V x y = gramQ V.gram x y := fun x => by
    unfold GlobalTheory.StdUnn.inner gramQ mmul
    rw [Matrix.mul_assoc]
    rfl
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner]
  unfold EC.Heisenberg₂
  have htr0 : GlobalTheory.StdUnn.trA (0 : AE D) = 0 := map_zero _
  rw [hx, hy, h0, add_zero, Matrix.trace_zero, halfTr, htr0, mul_zero, add_zero, hin]
  rfl

theorem pairing_add_right (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (x y y' : Mx D m n) : pairing T ψ x (y + y') = pairing T ψ x y * pairing T ψ x y' := by
  unfold pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA gramQ mmul
  rw [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]

theorem continuous_pairing (T : Matrix (Fin m) (Fin m) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {n : ℕ} (x : Mx D m n) : Continuous (pairing T ψ x) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold pairing gramQ mmul
  exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)

theorem pairing_zero_left (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (y : Mx D m n) : pairing T ψ 0 y = 1 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj (0 : Mx D m n) = 0 := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj, Formalism.UG.cT]
  simp [pairing, gramQ, mmul, h, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA]

open Classical in

theorem char_integral {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {n : ℕ}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    ∫ y in 𝓕, pairing V.gram ψ (ξ.map (incA D)) y ∂μ = if ξ = 0 then 1 else 0 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram (isHermND_gram V) ψ hψ
  split_ifs with hξ
  · subst hξ
    have h0 : (0 : Matrix (Fin V.rank) (Fin n) D.host.E).map (incA D) = 0 := by
      ext i j
      simp
    simp only [h0, pairing_zero_left, setIntegral_const, smul_eq_mul, mul_one]
    simp [Measure.real, hμ.2.2]
  · set ξ' : Mx D V.rank n := ξ.map (incA D) with hξ'
    have hrat : ξ' ∈ ratMx D V.rank n := ⟨ξ, rfl⟩
    have hne : ξ' ≠ 0 := by
      intro h
      apply hξ
      exact Matrix.ext fun i j => incA_injective ((congrFun (congrFun h i) j).trans (map_zero (incA D)).symm)
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, pairing V.gram ψ ξ' y₀ ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (h2 ξ' hrat hc)
    have hper : ∀ γ ∈ ratMx D V.rank n, ∀ a, pairing V.gram ψ ξ' (γ + a) = pairing V.gram ψ ξ' a := by
      intro γ hγ a
      rw [pairing_add_right, (h1 γ).2 hγ ξ' hrat, one_mul]
    have key := GlobalTheory.TowerRestrict.setIntegral_add_right hμ (pairing V.gram ψ ξ') hper y₀
    simp only [pairing_add_right, integral_mul_const] at key
    have : (∫ y in 𝓕, pairing V.gram ψ ξ' y ∂μ) * (pairing V.gram ψ ξ' y₀ - 1) = 0 := by
      rw [mul_sub, mul_one, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hy₀)

open Classical in

theorem zero : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  intro D ψ hψ θ hθ V n μ 𝓕 hμ Φ hΦ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI i6 : DiscreteTopology (ratMx D V.rank n) := i5
  haveI i7 : SecondCountableTopology (ratMx D V.rank n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D V.rank n) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) := by
    let g : Matrix (Fin V.rank) (Fin n) D.host.E → ratMx D V.rank n := fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩
    have hg : Function.Injective g := by
      intro a b h
      have h' := congrArg Subtype.val h
      exact Matrix.ext fun i j => incA_injective (congrFun (congrFun h' i) j)
    exact hg.countable
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; exact ENNReal.one_ne_top)
  simp only [heis_zy]
  set F : Matrix (Fin V.rank) (Fin n) D.host.E → Mx D V.rank n → ℂ :=
    fun ξ y => pairing V.gram ψ (ξ.map (incA D)) y * Φ (ξ.map (incA D)) with hF
  have hnorm : ∀ ξ y, ‖F ξ y‖ = ‖Φ (ξ.map (incA D))‖ := by
    intro ξ y
    simp only [hF, norm_mul, pairing, hψ.2.1, one_mul]
  have hint : ∀ ξ, Integrable (F ξ) (μ.restrict 𝓕) := fun ξ =>
    (integrable_const ‖Φ (ξ.map (incA D))‖).mono'
      ((continuous_pairing V.gram hψ _).mul continuous_const).aestronglyMeasurable
      (ae_of_all _ fun y => (hnorm ξ y).le)
  have hsum : Summable fun ξ => ∫ y, ‖F ξ y‖ ∂(μ.restrict 𝓕) := by
    simp only [hnorm, integral_const, smul_eq_mul]
    have hr : (μ.restrict 𝓕).real Set.univ = 1 := by simp [Measure.real, hμ.2.2]
    simp only [hr, one_mul]
    exact GlobalTheory.SiegelWeilLitCompare.summable_rat hθ ⟨Φ, hΦ⟩
  show Φ 0 = ∫ y in 𝓕, ∑' ξ, F ξ y ∂μ
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [hF, integral_mul_const, char_integral hψ V hμ]
  rw [tsum_eq_single 0]
  · simp
  · intro b hb
    simp [hb]

end GlobalTheory.CompanionTheory.EisZero
