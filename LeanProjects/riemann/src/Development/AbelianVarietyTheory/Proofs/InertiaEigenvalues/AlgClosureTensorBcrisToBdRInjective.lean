import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjointStatement
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeKurOfNorm

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TensorInj

theorem exists_div_of_mem_closure {A D : Type} [CommRing A] [Field D] (g : A →+* D) {y : D}
    (hy : y ∈ Subfield.closure (Set.range g)) (h0 : y ≠ 0) : ∃ a b : A, b ≠ 0 ∧ g a = y * g b := by
  obtain ⟨p, hp, q, hq, e⟩ := Subfield.mem_closure_iff.1 hy
  have hr : Subring.closure (Set.range g) = g.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hr] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  have hb : g b ≠ 0 := fun h => h0 (by rw [← e, h, div_zero])
  refine ⟨a, b, fun h => hb (by rw [h, map_zero]), ?_⟩
  rw [← e, div_mul_cancel₀ _ hb]

theorem indep_of_fractions (l : ℕ) [Fact l.Prime] {A B D : Type} [CommRing A] [CommRing B] [CommRing D]
    (hD : IsField D) (g : A →+* D) (ι : B →+* D) (hι : Function.Injective ι) (o : Om l →+* D)
    (hB : ∀ b : B, ∃ a a' : A, g a' ≠ 0 ∧ ι b * g a' = g a)
    (hu : ∀ c : ↥(MaximalUnramifiedExtension l), ∃ b : B, ι b = o (c : Om l))
    (hv : ∀ (a b : A) (x : Om l), b ≠ 0 → x ≠ 0 → g a = o x * g b → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k)
    (m : ℕ) (x : Fin m → Om l) (hx : LinearIndependent ↥(MaximalUnramifiedExtension l) x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) (i : Fin m) : b i = 0 := by
  letI : Field D := hD.toField
  let F : Subfield D := Subfield.closure (Set.range g)
  have hg : ∀ a, g a ∈ F := fun a => Subfield.subset_closure ⟨a, rfl⟩
  have hιF : ∀ b, ι b ∈ F := fun b => by
    obtain ⟨a, a', h0, e⟩ := hB b
    rw [eq_div_of_mul_eq h0 e]
    exact F.div_mem (hg a) (hg a')
  have hK : ∀ c : ↥(MaximalUnramifiedExtension l), o (c : Om l) ∈ F := fun c => by
    obtain ⟨b, e⟩ := hu c
    exact e ▸ hιF b
  let E : IntermediateField ℚ_[l] (Om l) :=
    (F.comap o).toIntermediateField fun q => hK (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)
  have hE : ∀ y : Om l, o y ∈ F → y ∈ MaximalUnramifiedExtension l := fun y hy => by
    have hint : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
    have hle : IntermediateField.adjoin ℚ_[l] {y} ≤ E :=
      IntermediateField.adjoin_simple_le_iff.2 hy
    refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {y},
      IntermediateField.adjoin.finiteDimensional hint⟩ (fun z hz h0 => ?_)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] y)
    obtain ⟨a, a', h1, e⟩ := exists_div_of_mem_closure g (y := o z) (hle hz) ((map_ne_zero o).2 h0)
    exact hv a a' z h1 h0 e
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := IsGalois.tower_top_of_isGalois ℚ_[l] _ _
  have := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent ↥(MaximalUnramifiedExtension l) (Om l) D o F
    (fun y => ⟨fun h => ⟨⟨y, hE y h⟩, rfl⟩, fun ⟨c, h⟩ => h ▸ hK c⟩) m x hx (fun i => ι (b i))
    (fun i => hιF _) hb i
  exact hι (this.trans (map_zero ι).symm)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem tensorInj (l : ℕ) [Fact l.Prime] (c : Core l) : c.TensorInj := by
  obtain ⟨-, hinj, hD, -⟩ := BdRField.bdR_isField l
  have hι : Function.Injective c.ι := (ULaws.u_laws l c).2.2.2.1
  haveI : Nontrivial (Per.BdR l) := ⟨hD.exists_pair_ne⟩
  refine indep_of_fractions l hD ((algebraMap (Per.BdRp l) (Per.BdR l)).comp c.j) c.ι hι c.oD
    (fun b => ?_) (fun x => ⟨c.u x, c.ι_u x⟩) (fun a b x hb hx e => ?_)
  · obtain ⟨r, a, e⟩ := bcris_eq_acris_localization_periodT_alt l c b
    refine ⟨a, c.t ^ r, ?_, ?_⟩
    · rw [RingHom.comp_apply, ← c.ι_j, map_pow]
      exact ((((core_t_unit_fil l c).1).pow r).map c.ι).ne_zero
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← c.ι_j, ← c.ι_j, ← map_mul, map_pow, e]
  · refine @GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l _ c a b x hb hx (hinj ?_)
    rw [map_mul]
    exact e

end GlobalTheory.MemLoc.TensorInj
