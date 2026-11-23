import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselClosed

open GlobalTheory.BesselCompare (mt_mul mt_one hA_coeff closure_prop spanA)

variable {D : D7}

def spanLt (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (k : ℕ) : Submodule (AE D) (Fin B.rank → AE D) where
  carrier := {v | ∃ c : Fin ρ → AE D, (∀ l : Fin ρ, k ≤ l.1 → c l = 0) ∧ v = ∑ l, c l • vecA B (e l)}
  zero_mem' := ⟨0, fun _ _ => rfl, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun l hl => by simp [hc l hl, hc' l hl], by simp [add_smul, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, fun l hl => by simp [hc l hl], by simp [Finset.smul_sum, smul_smul]⟩

variable {B : HSp D} {ρ : ℕ} {e : Fin ρ → B.V}

theorem spanLt_mono {k k' : ℕ} (h : k ≤ k') : spanLt B e k ≤ spanLt B e k' := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, fun l hl => hc l (h.trans hl), rfl⟩

theorem vec_mem_spanLt {k : ℕ} {l : Fin ρ} (h : l.1 < k) : vecA B (e l) ∈ spanLt B e k := by
  classical
  refine ⟨Pi.single l 1, fun j hj => Pi.single_eq_of_ne (fun e => by subst e; omega) _, ?_⟩
  rw [Finset.sum_eq_single l] <;> simp +contextual

theorem mulVec_mem_spanLt {k : ℕ} (M : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (hM : ∀ l : Fin ρ, l.1 < k → M.mulVec (vecA B (e l)) - vecA B (e l) ∈ spanLt B e l.1)
    {v} (hv : v ∈ spanLt B e k) : M.mulVec v ∈ spanLt B e k := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [← Matrix.mulVecLin_apply, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rcases lt_or_ge l.1 k with hl | hl
  · rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := add_mem (spanLt_mono hl.le (hM l hl)) (vec_mem_spanLt (B := B) (e := e) hl)
    rwa [sub_add_cancel] at this
  · simp [hc l hl]

theorem mem_NS_iff {n : GA D B} : n ∈ GlobalTheory.BesselCompare.NS B e ↔
    (∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1) ∧
      ∀ x : B.V, (∀ i, B.hD x (e i) = 0) → actV B n x - vecA B x ∈ spanLt B e ρ := by
  refine and_congr (forall_congr' fun i => exists_congr fun c => and_congr Iff.rfl sub_eq_iff_eq_add'.symm)
    (forall_congr' fun x => forall_congr' fun _ => exists_congr fun c => ?_)
  rw [sub_eq_iff_eq_add']
  exact ⟨fun h => ⟨fun l hl => absurd l.2 (by omega), h⟩, fun h => h.2⟩

theorem closure_flag (n : GA D B) (hn : n ∈ Subgroup.closure (GlobalTheory.BesselCompare.NS B e)) :
    ∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1 := by
  induction hn using Subgroup.closure_induction'' with
  | one => intro i; simp [actV, mt_one]
  | mem g hg => exact (mem_NS_iff.1 hg).1
  | inv_mem g hg =>
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have h := mulVec_mem_spanLt (mt B g⁻¹) (fun l hl => ih l hl) ((mem_NS_iff.1 hg).1 i)
      rw [Matrix.mulVec_sub, actV, mulVec_inv_cancel] at h
      have := neg_mem h
      rwa [neg_sub] at this
  | mul g h _ _ ihg ihh =>
    intro i
    have := add_mem (mulVec_mem_spanLt (mt B g) (fun l _ => ihg l) (ihh i)) (ihg i)
    rwa [Matrix.mulVec_sub, actV, ← mulVec_mul, actV, sub_add_sub_cancel] at this

theorem closure_NS : (Subgroup.closure (GlobalTheory.BesselCompare.NS B e) : Set (GA D B)) = GlobalTheory.BesselCompare.NS B e := by
  refine subset_antisymm (fun n hn => mem_NS_iff.2 ⟨closure_flag n hn, fun x hx => ?_⟩) Subgroup.subset_closure
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ((closure_prop B e n hn).2 x hx)
  exact ⟨a, fun l hl => absurd l.2 (by omega), ha.symm⟩

theorem mem_spanLt_iff {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) {k : ℕ} {v} :
    v ∈ spanLt B e k ↔ (∀ l : Fin ρ, k ≤ l.1 → hA B v (vecA B (f l)) = 0) ∧
      v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l) := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨c, hc, rfl⟩
  simp only [hA_coeff B e f ef]
  exact ⟨hc, trivial⟩

theorem isClosed_NS {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) :
    IsClosed (GlobalTheory.BesselCompare.NS B e) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := e0.isEmbedding.t2Space
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have hm : Continuous (fun k : GA D B => mt B k) := Units.continuous_val.comp continuous_subtype_val
  have hh : ∀ y, Continuous fun v => hA B v y := fun y =>
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hc : ∀ k, IsClosed (spanLt B e k : Set (Fin B.rank → AE D)) := fun k => by
    have : (spanLt B e k : Set (Fin B.rank → AE D)) =
        (⋂ l : Fin ρ, ⋂ _ : k ≤ l.1, {v | hA B v (vecA B (f l)) = 0}) ∩
          {v | v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l)} := by
      ext v
      simp only [SetLike.mem_coe, mem_spanLt_iff ef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact (isClosed_iInter fun l => isClosed_iInter fun _ => isClosed_eq (hh _) continuous_const).inter
      (isClosed_eq continuous_id (continuous_finsetSum _ fun l _ => (hh _).smul continuous_const))
  have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  have : ContinuousSub (AE D) := IsTopologicalAddGroup.to_continuousSub
  have ha : ∀ x, Continuous fun n : GA D B => actV B n x - vecA B x := fun x =>
    continuous_pi fun j => ((continuous_apply j).comp (hm.matrix_mulVec continuous_const)).sub continuous_const
  have : GlobalTheory.BesselCompare.NS B e =
      (⋂ i : Fin ρ, (fun n => actV B n (e i) - vecA B (e i)) ⁻¹' spanLt B e i.1) ∩
        ⋂ x : B.V, ⋂ _ : ∀ i, B.hD x (e i) = 0, (fun n => actV B n x - vecA B x) ⁻¹' spanLt B e ρ := by
    ext n
    simp only [mem_NS_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact (isClosed_iInter fun i => (hc _).preimage (ha _)).inter
    (isClosed_iInter fun x => isClosed_iInter fun _ => (hc _).preimage (ha _))

theorem N_eq_and_isClosed : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (d.N : Set (GA D B)) = d.NSet ∧ IsClosed (d.N : Set (GA D B)) := by
  intro D A B ι d
  have h : (d.N : Set (GA D B)) = GlobalTheory.BesselCompare.NS B d.e := closure_NS
  exact ⟨h, h ▸ isClosed_NS d.ef⟩

end GlobalTheory.BesselClosed

end
