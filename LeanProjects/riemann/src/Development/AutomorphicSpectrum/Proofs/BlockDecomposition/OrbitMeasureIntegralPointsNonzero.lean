import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem eventually_cv_mem_intLoc {D : D7} (a : AE D) :
    ∀ᶠ v : Pl D in cofinite, cv D v a ∈ intLoc D.host.F D.host.E v :=
  GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele a

theorem isOpen_intAll (D : D7) : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
  GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere

theorem exists_intOff {D : D7} {a b : ℕ} (x : Mx D a b) :
    ∀ᶠ v : Pl D in cofinite, ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_cv_mem_intLoc (x i j)

theorem isOpen_nearInt {D : D7} {a b : ℕ} (x : Mx D a b) :
    IsOpen {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h : {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} =
      ⋂ i, ⋂ j, (fun y : Mx D a b => y i j - x i j) ⁻¹' {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  have hT := (top_mx (D := D) a b).1
  haveI hS : ContinuousSub (Mx D a b) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  have hc : Continuous fun y : Mx D a b => y - x := continuous_id.sub continuous_const
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_intAll D).preimage (hc.matrix_elem i j)

theorem nuT_intOff_ne_zero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
      nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  intro D n t B W d hn I μ hμ x₀
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let π : I.l.K × Par D n t W → Mx D B.rank W.rank × Mx D B.rank t :=
    fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
  let p₀ : I.l.K × Par D n t W := (1, (1, (0, 0)))
  have hbad : {v : Pl D | ¬ ((∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v)}.Finite :=
    ((exists_intOff (π p₀).1).and (exists_intOff (π p₀).2))
  refine ⟨hbad.toFinset, fun S hS => ?_⟩
  have hπ : Continuous π := by
    obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
    exact (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  let N : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    {z | (∀ i j, ∀ v : Pl D, cv D v (z.1 i j - (π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, ∀ v : Pl D, cv D v (z.2 i j - (π p₀).2 i j) ∈ intLoc D.host.F D.host.E v}
  have hNo : IsOpen N := ((isOpen_nearInt (π p₀).1).preimage continuous_fst).inter
    ((isOpen_nearInt (π p₀).2).preimage continuous_snd)
  have hN0 : π p₀ ∈ N := by
    constructor <;> intro i j v <;> simp only [sub_self, map_zero, zero_mem]
  have hNO : N ⊆ {z | IntOff S z.1 ∧ IntOff S z.2} := by
    intro z hz
    have key : ∀ v, v ∉ S → (∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
        ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v := fun v hv => by
      by_contra hc
      exact hv (hS (hbad.mem_toFinset.2 hc))
    refine ⟨fun v hv i j => ?_, fun v hv i j => ?_⟩
    · have := add_mem (hz.1 i j v) ((key v hv).1 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
    · have := add_mem (hz.2 i j v) ((key v hv).2 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hGB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.haarK
  have hs1 : SigmaFinite (I.μ₁.prod μ) := inferInstance
  have hs2 : SigmaFinite (Q0 I μ) := sigmaFinite_parameter_product_measure I μ hμ
  have p1 : (I.μ₁.prod μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have p2 : (Q0 I μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hpos : (I.νK.prod (Q0 I μ)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hopen : IsOpen (π ⁻¹' N) := hNo.preimage hπ
  have hne : (I.νK.prod (Q0 I μ)) (π ⁻¹' N) ≠ 0 := hopen.measure_ne_zero _ ⟨p₀, hN0⟩
  intro h0
  apply hne
  have hle : (I.νK.prod (Q0 I μ)) (π ⁻¹' {z | IntOff S z.1 ∧ IntOff S z.2}) ≤ nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} :=
    Measure.le_map_apply (measurable_pi hn I x₀).aemeasurable _
  exact le_antisymm (((measure_mono (Set.preimage_mono hNO)).trans hle).trans h0.le) bot_le

end GlobalTheory.CompanionTheory.ColumnSplitting

end
