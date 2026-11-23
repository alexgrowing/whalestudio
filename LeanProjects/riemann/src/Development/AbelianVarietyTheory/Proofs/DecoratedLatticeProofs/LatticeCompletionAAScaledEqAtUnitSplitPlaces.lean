import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.UnitPlaces

variable {D : D7}

theorem pairA_sum {κ : Type} (s : Finset κ) (f : κ → Af D.host.F) :
    pairA D.host.F 0 (∑ i ∈ s, f i) = ∑ i ∈ s, pairA D.host.F 0 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.FinPlLoc.pairA_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.FinPlLoc.pairA_add, ih]

theorem latMul_mono (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    latMul S 𝔞 L P ≤ latMul S 𝔞 L P' := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  exact AddSubgroup.subset_closure ⟨α, hαi, fun v hv => hα v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem latMul_le_of_parts (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (M : AddSubgroup (Fin S.rank → AE D))
    {P : Pl D → Prop} (s : Finset (Pl D)) (hs : ∀ w, P w → w ∈ s) (h : ∀ w ∈ s, latMul S 𝔞 L (· = w) ≤ M) :
    latMul S 𝔞 L P ≤ M := by
  classical
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  have hdec : α = ∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α := by
    refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α)
    rw [map_sum]
    simp only [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u ∈ s
    · simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos hu]
    · have h0 : evalV D.host.F u α = 0 := hα u fun h' => hu (hs u h')
      simp [h0]
  have hsum : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
      ∑ w ∈ s, fun i => pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = w) * α) ⊗ₜ[D.host.F] (a * x i) := by
    funext i
    rw [Finset.sum_apply, ← TensorProduct.sum_tmul, ← pairA_sum, ← hdec]
  show _ ∈ M
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun w hw => h w hw (AddSubgroup.subset_closure
    ⟨GlobalTheory.FinPlLoc.ePl D (· = w) * α, fun u => ?_, fun u hu => ?_, a, ha, x, hx, rfl⟩)
  · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ u) (hαi u)
  · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hu, zero_mul]

theorem latA_eq_latV : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S : HSp D) (L : Lat S), latA S L P = latV S L P := by
  intro D k _ _ _ _ ι p I P hP S L
  classical
  let s : Finset (Pl D) := (I.map fun i => (p i).v).toFinset
  have hs : ∀ w, P w → w ∈ s := by
    intro w hw
    obtain ⟨i, rfl⟩ := (hP.mem w).1 hw
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨i, hP.all i, rfl⟩)
  have hsi : ∀ w ∈ s, ∃ i, w = (p i).v := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
    exact ⟨i, rfl⟩
  have hsP : ∀ w ∈ s, P w := fun w hw => (hP.mem w).2 (hsi w hw)
  have hloc : ∀ w ∈ s, latA S L (· = w) = latV S L (· = w) := by
    intro w hw
    obtain ⟨i, rfl⟩ := hsi w hw
    exact (hP.unit i).2 S L
  apply le_antisymm
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).le.trans (latMul_mono S {1} L fun u (hu : u = w) => hu ▸ hsP w hw)
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).ge.trans (latMul_mono S {a | a ∈ D.host.AA} L fun u (hu : u = w) => hu ▸ hsP w hw)

end GlobalTheory.FinPl.UnitPlaces

end
