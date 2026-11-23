import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem mt_mul (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

def locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) : GA D S →* GL Y k where
  toFun g := ⟨F.γ * (mt S g).map q.pr * F.β, F.γ * (mt S g⁻¹).map q.pr * F.β, by
      rw [show F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S g⁻¹).map q.pr * F.β) =
        F.γ * ((mt S g).map q.pr * (F.β * F.γ) * (mt S g⁻¹).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ], by
      rw [show F.γ * (mt S g⁻¹).map q.pr * F.β * (F.γ * (mt S g).map q.pr * F.β) =
        F.γ * ((mt S g⁻¹).map q.pr * (F.β * F.γ) * (mt S g).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ]⟩
  map_one' := by
    ext1; simp only [mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, F.γβ]; rfl
  map_mul' g h := by
    ext1
    change F.γ * (mt S (g * h)).map q.pr * F.β = F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S h).map q.pr * F.β)
    rw [mt_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem locHom_val (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) :
    (locHom q S F g).val = F.γ * (mt S g).map q.pr * F.β := rfl

theorem eq_locHom_iff (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) (x : GL Y k) :
    (mt S g).map q.pr = F.β * x.val * F.γ ↔ x = locHom q S F g := by
  constructor
  · intro h
    ext1
    rw [locHom_val, h]
    simp only [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]
  · rintro rfl
    rw [locHom_val]
    simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

theorem continuous_locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    Continuous (locHom q S F) := by
  rw [Units.continuous_iff]
  have hm : Continuous fun g : GA D S => (mt S g).map q.pr :=
    (GlobalTheory.MixModel.continuous_mt S).matrix_map q.cont_pr
  refine ⟨(continuous_const.matrix_mul hm).matrix_mul continuous_const, ?_⟩
  have hi : Continuous fun g : GA D S => (mt S g⁻¹).map q.pr :=
    ((GlobalTheory.MixModel.continuous_mt S).comp continuous_inv).matrix_map q.cont_pr
  exact (continuous_const.matrix_mul hi).matrix_mul continuous_const

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) : μ.real H' * (H'.relIndex H : ℝ) = μ.real H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

end GlobalTheory.LevIdx
end
