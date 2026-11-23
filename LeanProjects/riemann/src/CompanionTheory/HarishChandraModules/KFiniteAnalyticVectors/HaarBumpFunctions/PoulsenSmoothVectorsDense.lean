import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.HaarBumpFunctions.ExistsIsBump
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Unimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen

open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.Poul

open PI PI.UpqRep CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.LimBd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem isInvInvariant_haar {ε : Fin (2 * r + k + 1) → Bool} {P : Mat (2 * r + k + 1)} (hP : IsCayley k r ε P)
    (hG : IsMatGroup (UH (Hpk k r))) : (haar : Measure (MG (UH (Hpk k r)) hG)).IsInvInvariant := by
  let f : UJ ε →* MG (UH (Hpk k r)) hG :=
    { toFun := fun g => MG.mk hG _ (SchurHpk.iota_mem hP g)
      map_one' := MG.ext (SchurHpk.iota_one hP)
      map_mul' := fun a b => MG.ext (SchurHpk.iota_mul hP a b) }
  have hf : Continuous f := MG.continuous_iff.2 (SchurHpk.iota_closedEmb hP).continuous
  have hs : Function.Surjective f := fun x => by
    obtain ⟨g, hg⟩ := SchurHpk.exists_iota_eq hP x.mem
    exact ⟨g, MG.ext hg⟩
  have hce : IsClosedEmbedding f :=
    IsClosedEmbedding.of_comp MG.isClosedEmbedding_mat.isEmbedding (SchurHpk.iota_closedEmb hP)
  have hH : IsHaarMeasure (Measure.map f (muG ε)) := isHaarMeasure_map (muG ε) f hf hs hce.tendsto_cocompact
  have hI := (PIW.HCFdeg.stUnimod _ ε).2
  have hinv : (Measure.map f (muG ε)).inv = Measure.map f (muG ε) := by
    rw [Measure.inv_def, Measure.map_map measurable_inv hf.measurable]
    have : (Inv.inv ∘ f : UJ ε → _) = f ∘ Inv.inv := funext fun g => (map_inv f g).symm
    rw [this, ← Measure.map_map hf.measurable measurable_inv, Measure.map_inv_eq_self]
  refine ⟨?_⟩
  rw [isMulLeftInvariant_eq_smul haar (Measure.map f (muG ε)), Measure.inv_def, Measure.map_smul, ← Measure.inv_def,
    hinv]

def theta (k r : ℕ) : Mat (2 * r + k + 1) →L[ℝ] Mat (2 * r + k + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Hpk k r * xᴴ * Hpk k r
      map_add' := fun a b => by rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, star_trivial]; rfl }

theorem theta_eq (x : Mat (2 * r + k + 1)) (hx : x ∈ UH (Hpk k r)) : theta k r x = x⁻¹ :=
  (PI.HwUniqW.inv_eq_UH hx).symm

theorem sum_get {α : Type} (L : List α) (f : α → ℝ) : ∑ i : Fin L.length, f (L.get i) = (L.map f).sum := by
  rw [← List.sum_ofFn, ← Function.comp_def f, ← List.map_ofFn, List.ofFn_get]

theorem exists_op {ε ε' : Fin (2 * r + k + 1) → Bool} {mu mu' : Fin (2 * r + k + 1) → ℝ} {R R' : BranchingSupport.Rep k r}
    (hR : R.IsDS ε mu) (hR' : R'.IsDS ε' mu') {B : R.H → R'.H → ℂ} (hB : BranchingSupport.IsInvForm R R' B) :
    ∃ T : R'.H →L[ℂ] R.H, (∀ g ∈ UH (Hpk k r), ∀ y, T (R'.σ g y) = R.σ g (T y)) ∧
      ∀ x ∈ R.sm, ∀ y ∈ R'.sm, B x y = ⟪T y, x⟫_ℂ := by
  have hG : IsMatGroup (UH (Hpk k r)) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hU := SchurHpk.isURepOn_of_ds hR.2
  have hU' := SchurHpk.isURepOn_of_ds hR'.2
  obtain ⟨h1, h2, h3, h4, h5, C, Ws, Ws', hW, hbd⟩ := hB
  obtain ⟨P, hP, hDS⟩ := id hR.2
  obtain ⟨P', -, hDS'⟩ := id hR'.2
  have := hDS.2.1
  have := hDS'.2.1
  have := isInvInvariant_haar hP.1 hG
  have hI : IsInv (UH (Hpk k r)) R.σ R'.σ Ws.get Ws'.get C B :=
    { add_left := fun x x' y hx hx' hy => h1 x hx x' hx' y hy
      smul_left := fun a x y hx hy => h2 a x hx y hy
      add_right := fun x y y' hx hy hy' => h3 x hx y hy y' hy'
      smul_right := fun a x y hx hy => h4 a x hx y hy
      inv := fun g hg x y hx hy => h5 g hg x hx y hy
      bd := fun x y hx hy => by
        rw [sum_get Ws fun W => ‖dsW R.σ W x‖, sum_get Ws' fun W => ‖dsW R'.σ W y‖]
        simpa only [dsigW_eq'] using hbd x hx y hy }
  obtain ⟨T, hT, hTB⟩ := hI.exists_op (hG := hG) (theta k r) theta_eq ⟨hG.2.1, hG.2.2.1, hU.1.1, hU.1.2⟩
    ⟨hG.2.1, hG.2.2.1, hU'.1.1, hU'.1.2⟩ hU.2.1 hU'.2.1 hU.2.2 hU'.2.2 (SchurHpk.isIrredOn_of_ds hR.2)
    (SchurHpk.isIrredOn_of_ds hR'.2)
    (fun i X hX t => ex_mem_of_lie (hW _ (List.mem_append_left _ (List.get_mem _ _)) X hX) t)
    (fun i X hX t => ex_mem_of_lie (hW _ (List.mem_append_right _ (List.get_mem _ _)) X hX) t)
  exact ⟨T, hT, fun x hx y hy => hTB x y hx hy⟩

theorem vanish_or_equiv {ε ε' : Fin (2 * r + k + 1) → Bool} {mu mu' : Fin (2 * r + k + 1) → ℝ} {R R' : BranchingSupport.Rep k r}
    (hR : R.IsDS ε mu) (hR' : R'.IsDS ε' mu') {B : R.H → R'.H → ℂ} (hB : BranchingSupport.IsInvForm R R' B) :
    (∀ x ∈ R.sm, ∀ y ∈ R'.sm, B x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ BranchingSupport.GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x) := by
  obtain ⟨T, hT, hTB⟩ := exists_op hR hR' hB
  by_cases h0 : T = 0
  · exact Or.inl fun x hx y hy => by rw [hTB x hx y hy, h0]; simp
  right
  obtain ⟨P, hP, hDS⟩ := id hR.2
  obtain ⟨P', -, hDS'⟩ := id hR'.2
  have := hDS.2.1
  have := hDS'.2.1
  obtain ⟨e⟩ := ((SchurHpk.toURep_irred hP.1 R'.σ (SchurHpk.isURepOn_of_ds hR'.2) (SchurHpk.isIrredOn_of_ds hR'.2)).isEquivalent_of_mem_intertwiners
    (SchurHpk.toURep_irred hP.1 R.σ (SchurHpk.isURepOn_of_ds hR.2) (SchurHpk.isIrredOn_of_ds hR.2)) (T := T)
    (fun g v => hT _ (SchurHpk.iota_mem hP.1 g) v) h0).symm
  refine ⟨e.toLinearIsometryEquiv, fun g hg x => ?_⟩
  obtain ⟨a, rfl⟩ := SchurHpk.exists_iota_eq hP.1 hg
  exact e.map_apply' a x

theorem poulsen_smooth_vectors_dense : BranchingSupport.Poulsen := by
  intro k r ε mu mu' R R' hR hR'
  refine ⟨fun B hB => ?_, fun B hB => vanish_or_equiv hR hR' hB⟩
  obtain ⟨T, hT, hTB⟩ := exists_op hR hR hB
  obtain ⟨P, hP, hDS⟩ := id hR.2
  have := hDS.2.1
  obtain ⟨c, hc⟩ := (SchurHpk.toURep_irred hP.1 R.σ (SchurHpk.isURepOn_of_ds hR.2)
    (SchurHpk.isIrredOn_of_ds hR.2)).exists_eq_smul_one (T := T) fun g v => hT _ (SchurHpk.iota_mem hP.1 g) v
  refine ⟨star c, fun x hx y hy => ?_⟩
  rw [hTB x hx y hy, hc]
  show ⟪c • y, x⟫_ℂ = _
  rw [inner_smul_left]
  rfl

end CompanionTheory.D.gk.Poul
