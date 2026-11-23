import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ClsStable

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E]

theorem h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (y : V) : H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := H.h_smul_left 0 0 y
    simpa using this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H.h_add_left, ih]

theorem h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (x : V) : H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.h_herm]

theorem zhat_chg {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ)
    (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hg : GlobalTheory.LocOver.Chg f A g) (hg' : GlobalTheory.LocOver.Chg f' A' g') :
    H.Zhat g g' = A.transpose.map M.L.cj * H.Zhat f f' * A' := by
  ext a b
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [hg a, hg' b, h_sum_left]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [H.h_smul_left, h_sum_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h_smul_right]
  ring

theorem intUni_mul {M : Loc.Model F E} {r : ℕ} {B A : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hB : IntUni M B) (hA : IntUni M A) : IntUni M (B * A) := by
  refine ⟨fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hB.1 a c h, zero_mul]
    · rw [hA.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hB.2.1, hA.2.1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hB.1 a c h, zero_mul]
      · rw [hA.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hB.2.2 a c) (hA.2.2 c b)

theorem span_mul_mem {M : Loc.Model F E} {t x o : E} (hx : x ∈ Submodule.span M.L.O {t}) (ho : o ∈ M.L.O) :
    x * o ∈ Submodule.span M.L.O {t} ∧ o * x ∈ Submodule.span M.L.O {t} := by
  have h1 : (⟨o, ho⟩ : M.L.O) • x ∈ Submodule.span M.L.O {t} := Submodule.smul_mem _ _ hx
  have h2 : (⟨o, ho⟩ : M.L.O) • x = o * x := rfl
  rw [h2] at h1
  exact ⟨by rw [mul_comm]; exact h1, h1⟩

theorem zhat_mem_clsLoc_of_chg : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Y0 f f' g g' A A' hA hA' hint hg hg' hY
  obtain ⟨B, B', hB, hB', hBB, hZ⟩ := hY
  have hIA : IntUni M A := ⟨hA.1, hA.2, fun a b => (hint a b).1⟩
  have hIA' : IntUni M A' := ⟨hA'.1, hA'.2, fun a b => (hint a b).2.1⟩
  refine ⟨B * A, B' * A', intUni_mul hB hIA, intUni_mul hB' hIA', fun a b => ?_, ?_⟩
  · have e : (B * A) a b - (B' * A') a b =
        ∑ c, (B a c - B' a c) * A c b + ∑ c, B' a c * (A c b - A' c b) := by
      simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) (Submodule.sum_mem _ fun c _ => ?_)
    · exact (span_mul_mem (hBB a c) (hIA.2.2 c b)).1
    · exact (span_mul_mem (hint c b).2.2 (hB'.2.2 a c)).2
  · rw [zhat_chg H r f f' g g' A A' hg hg', hZ, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ClsStable
