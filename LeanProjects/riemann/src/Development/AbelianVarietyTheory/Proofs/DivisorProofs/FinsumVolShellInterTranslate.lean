import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.PureMatch.ShellVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open IsDedekindDomain NumberField MeasureTheory Matrix in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.PureMatch.ShellVolume.isOpen_translate {a : ℕ} (u u' : GL (Fin a) k) :
    IsOpen {g : GL (Fin a) k | u * g * u' ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin a)} :=
  _root_.GlobalTheory.SplitFlip.isOpen_KO.preimage
    ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.PureMatch.ShellVolume

open IsDedekindDomain NumberField MeasureTheory Matrix in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv in
open ValuativeRel in

theorem _root_.GlobalTheory.PureMatch.ShellVolume.finsum_vol_shell_inter_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (ϖ : kˣ) (u u' : GL (Fin a) k), _root_.GlobalTheory.SplitFlip.IsUnif ϖ →
    ∑ᶠ m : {m : Fin a → ℤ // Antitone m}, (_root_.GlobalTheory.SplitFlip.haarVol (_root_.GlobalTheory.SplitWeil.KO k (Fin a))).real (_root_.GlobalTheory.SplitFlip.shellSet ϖ m.1 ∩ {g | u * g * u' ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin a)}) = 1 := by
  intro k _ _ _ _ _ _ a ϖ u u' hϖ
  have hv : valuation k ↑ϖ = uniformizer k := hϖ
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  set K := _root_.GlobalTheory.SplitWeil.KO k (Fin a) with hK
  set μ := _root_.GlobalTheory.SplitFlip.haarVol K with hμ
  haveI : μ.IsHaarMeasure := _root_.GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO
  haveI : μ.IsMulRightInvariant := _root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar μ
  set S : Set (GL (Fin a) k) := {g | u * g * u' ∈ K} with hS
  have hshell : ∀ m : Fin a → ℤ,
      _root_.GlobalTheory.SplitFlip.shellSet ϖ m = _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ m := by
    intro m
    unfold _root_.GlobalTheory.GLDoubling.cell _root_.GlobalTheory.SplitFlip.shellSet
    congr 1
    ext : 1
    rw [_root_.GlobalTheory.GLDoubling.val_torusElt, _root_.GlobalTheory.SplitFlip.diagGL_val]
    simp
  simp only [hshell]
  have hSopen : IsOpen S := _root_.GlobalTheory.PureMatch.ShellVolume.isOpen_translate u u'
  have hSeq : S = (fun x => u⁻¹ * x * u'⁻¹) '' (K : Set (GL (Fin a) k)) := by
    ext g
    constructor
    · intro hg
      exact ⟨u * g * u', hg, by group⟩
    · rintro ⟨x, hx, rfl⟩
      show u * (u⁻¹ * x * u'⁻¹) * u' ∈ K
      have hx' : u * (u⁻¹ * x * u'⁻¹) * u' = x := by group
      rw [hx']
      exact hx
  have hScpt : IsCompact S := by
    rw [hSeq]
    exact _root_.GlobalTheory.SplitFlip.isCompact_KO.image
      ((continuous_const.mul continuous_id).mul continuous_const)
  have hμS : μ S = 1 := by
    have : S = (fun g => u * g) ⁻¹' ((fun g => g * u') ⁻¹' (K : Set (GL (Fin a) k))) := by
      ext g; simp [hS, mul_assoc]
    rw [this, measure_preimage_mul, measure_preimage_mul_right]
    exact _root_.GlobalTheory.SplitFlip.haarVol_self _root_.GlobalTheory.SplitFlip.isOpen_KO le_rfl
  obtain ⟨t, ht⟩ := hScpt.elim_finite_subcover
    (fun e : {m : Fin a → ℤ // Antitone m} => _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1)
    (fun e => _root_.GlobalTheory.GLDoubling.isOpen_cell _ _)
    (by rw [_root_.GlobalTheory.GLDoubling.iUnion_cell hv]; exact Set.subset_univ _)
  have hdisj := _root_.GlobalTheory.GLDoubling.pairwise_disjoint_cell (k := k) (N := a) hv
  have hsupp : Function.support (fun e : {m : Fin a → ℤ // Antitone m} =>
      μ.real (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S)) ⊆ ↑t := by
    intro e he
    by_contra het
    apply he
    have hempty : _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S = ∅ := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hge hgS
      obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht hgS)
      have hie : i ≠ e := fun h => het (h ▸ hi)
      exact Set.disjoint_left.mp (hdisj hie) hgi hge
    simp [hempty]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpd : (↑t : Set {m : Fin a → ℤ // Antitone m}).PairwiseDisjoint
      (fun e => _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S) := by
    intro i _ j _ hij
    exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ i ∈ t, MeasurableSet (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ i.1 ∩ S) := fun i _ =>
    (_root_.GlobalTheory.GLDoubling.isOpen_cell _ _).measurableSet.inter hSopen.measurableSet
  have hfin : ∀ i ∈ t, μ (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ i.1 ∩ S) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (by rw [hμS]; exact ENNReal.one_ne_top) (measure_mono Set.inter_subset_right)
  rw [← measureReal_biUnion_finset hpd hmeas hfin]
  have hU : (⋃ e ∈ t, _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S) = S := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun _ _ => Set.inter_subset_right
    · intro g hg
      obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht hg)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hgi, hg⟩
  rw [hU, measureReal_def, hμS, ENNReal.toReal_one]
