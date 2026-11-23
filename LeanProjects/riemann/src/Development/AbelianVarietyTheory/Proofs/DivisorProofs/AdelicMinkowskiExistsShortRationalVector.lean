import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

open MeasureTheory GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Automorphic.GJGlobal.Modulus

open scoped Pointwise

attribute [-instance] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.measAF

namespace GlobalTheory.AdelicMinkowski

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

noncomputable abbrev ratL : AddSubgroup (Fin n → AF F) :=
  AddSubgroup.pi Set.univ fun _ : Fin n => AdeleRing.principalSubgroup (𝓞 F) F

theorem mem_ratL_iff (x : Fin n → AF F) :
    x ∈ ratL F n ↔ ∃ ξ : Fin n → F, x = fun i => algebraMap F (AF F) (ξ i) := by
  constructor
  · intro hx
    choose ξ hξ using fun i => hx i trivial
    exact ⟨ξ, funext fun i => (hξ i).symm⟩
  · rintro ⟨ξ, rfl⟩ i _
    exact ⟨ξ i, rfl⟩

instance countable_ratL : Countable (ratL F n) := by
  haveI := GroundTheory.Global.countable_numberField F
  have h : (ratL F n : Set (Fin n → AF F)) ⊆
      Set.range (fun ξ : Fin n → F => fun i => algebraMap F (AF F) (ξ i)) := by
    intro x hx
    obtain ⟨ξ, rfl⟩ := (mem_ratL_iff F n x).1 hx
    exact ⟨ξ, rfl⟩
  exact ((Set.countable_range _).mono h).to_subtype

theorem isAddFundamentalDomain :
    IsAddFundamentalDomain (ratL F n) (Set.univ.pi fun _ : Fin n => fundamentalSet F)
      (adeleMeasurePi F (ι := Fin n)) :=
  GlobalTheory.SWQ.RatLattice.isFD_pi (adeleMeasure F) (isAddFundamentalDomain_fundamentalSet F) n

theorem measure_fundamental :
    adeleMeasurePi F (ι := Fin n) (Set.univ.pi fun _ : Fin n => fundamentalSet F) = 1 := by
  rw [adeleMeasurePi, Measure.pi_pi]
  simp [adeleMeasure_fundamentalSet]

theorem one_lt_measure_univ (hn : 0 < n) : 1 < adeleMeasurePi F (ι := Fin n) Set.univ := by
  set μ := adeleMeasurePi F (ι := Fin n)
  set D := Set.univ.pi fun _ : Fin n => fundamentalSet F
  have hfd := isAddFundamentalDomain F n
  set v : Fin n → AF F := fun i => algebraMap F (AF F) ((Pi.single (⟨0, hn⟩ : Fin n) (1 : F) : Fin n → F) i)
  have hv : v ∈ ratL F n := (mem_ratL_iff F n v).2 ⟨_, rfl⟩
  have hv0 : (⟨v, hv⟩ : ratL F n) ≠ 0 := by
    intro h
    have hc := congrFun (congrArg Subtype.val h) ⟨0, hn⟩
    haveI : Nontrivial (AF F) := by
      show Nontrivial (AdeleRing (𝓞 F) F)
      unfold AdeleRing
      infer_instance
    simp [v] at hc
  have hdis : AEDisjoint μ ((0 : ratL F n) +ᵥ D) ((⟨v, hv⟩ : ratL F n) +ᵥ D) :=
    hfd.aedisjoint hv0.symm
  rw [zero_vadd] at hdis
  have hmeas : μ ((⟨v, hv⟩ : ratL F n) +ᵥ D) = μ D := measure_vadd _ _ _
  have h2 : μ (D ∪ ((⟨v, hv⟩ : ratL F n) +ᵥ D)) = 2 := by
    rw [measure_union₀ (hfd.nullMeasurableSet.vadd _) hdis, hmeas, measure_fundamental]
    norm_num
  calc (1 : ENNReal) < 2 := by norm_num
    _ = _ := h2.symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)

end GlobalTheory.AdelicMinkowski

namespace GlobalTheory.AdelicMinkowski

theorem exists_compact_mulVec_rat_mem : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∃ B : Set (Fin n → AF F), IsCompact B ∧ ∀ g : Matrix (Fin n) (Fin n) (AF F), IsUnit g.det → (∃ u : (AF F)ˣ, (u : AF F) = g.det ∧ (GroundTheory.Global.IdeleGroup.ideleModule F u : ℝ) ≤ 1) → ∃ ξ : Fin n → F, ξ ≠ 0 ∧ g *ᵥ (fun i => algebraMap F (AF F) (ξ i)) ∈ B := by
  intro F _ _ n hn
  set μ := adeleMeasurePi F (ι := Fin n)
  set D := Set.univ.pi fun _ : Fin n => fundamentalSet F
  have hfd := isAddFundamentalDomain F n
  obtain ⟨B₀, -, hB₀c, hB₀⟩ := isOpen_univ.exists_lt_isCompact (μ := μ) (one_lt_measure_univ F n hn)
  refine ⟨(fun p : (Fin n → AF F) × (Fin n → AF F) => p.1 - p.2) '' (B₀ ×ˢ B₀),
    (hB₀c.prod hB₀c).image continuous_sub, ?_⟩
  rintro g hg ⟨u, hu, hu1⟩
  set G : GL (Fin n) (AF F) := Matrix.nonsingInvUnit gᵀ (by rwa [Matrix.det_transpose])
  have hG : (G : Matrix (Fin n) (Fin n) (AF F)) = gᵀ := rfl
  have hdetG : Matrix.GeneralLinearGroup.det G = u := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.det_transpose, hu]
  have hmap := map_vecMul_adeleMeasurePi G
  rw [hdetG] at hmap
  set φ : (Fin n → AF F) → (Fin n → AF F) := fun x => x ᵥ* (G : Matrix (Fin n) (Fin n) (AF F))
  have hφ : ∀ x, φ x = g *ᵥ x := fun x => by simp only [φ, hG, Matrix.vecMul_transpose]
  set s := φ ⁻¹' B₀
  have hφm : Measurable φ := measurable_vecMul' G
  have hsm : MeasurableSet s := hφm hB₀c.measurableSet
  have hc : (1 : ENNReal) ≤ ENNReal.ofReal ((IdeleGroup.ideleModule F u : ℝ))⁻¹ := by
    have hpos : 0 < (IdeleGroup.ideleModule F u : ℝ) := (IdeleGroup.ideleModule F u).2
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_inv₀ hpos |>.2 hu1)
  have hs : μ D < μ s := by
    rw [measure_fundamental]
    calc (1 : ENNReal) < μ B₀ := hB₀
      _ ≤ ENNReal.ofReal ((IdeleGroup.ideleModule F u : ℝ))⁻¹ * μ B₀ := le_mul_of_one_le_left' hc
      _ = (μ.map φ) B₀ := by rw [hmap]; rfl
      _ = μ s := Measure.map_apply hφm hB₀c.measurableSet
  obtain ⟨x, y, hxy, hnd⟩ := exists_pair_mem_lattice_not_disjoint_vadd hfd hsm.nullMeasurableSet hs
  obtain ⟨z, hzx, hzy⟩ := Set.not_disjoint_iff.1 hnd
  obtain ⟨a, ha, rfl⟩ := hzx
  obtain ⟨b, hb, hab⟩ := hzy
  change (y : Fin n → AF F) + b = (x : Fin n → AF F) + a at hab
  have hdiff : a - b = (y : Fin n → AF F) - x := by
    rw [sub_eq_sub_iff_add_eq_add, hab, add_comm]
  obtain ⟨ξ, hξ⟩ := (mem_ratL_iff F n _).1 (sub_mem y.2 x.2)
  refine ⟨ξ, ?_, ?_⟩
  · rintro rfl
    apply hxy
    refine (Subtype.ext (sub_eq_zero.1 ?_)).symm
    rw [hξ]
    funext i
    simp
  · rw [← hξ, ← hdiff, Matrix.mulVec_sub, ← hφ, ← hφ]
    exact ⟨(φ a, φ b), ⟨ha, hb⟩, rfl⟩

end GlobalTheory.AdelicMinkowski
