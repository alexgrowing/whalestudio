import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfLineMultipleMemIffIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineIdeal

theorem e_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr c ∈ 𝒪[k]) := by

  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hsum hlat c
  have key : (fun r => p.e * (c * incA D (vecB o ζ r))) =
      fun r => p.sec ((α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r) := by
    funext r
    have hb : α₀.b r (Sum.inr 0) = p.pr (incA D (vecB o ζ r)) := by
      rw [hsum]; rfl
    have hv : (α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r = α₀.b r (Sum.inr 0) * p.pr c := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, hb, ← map_mul, p.sec_pr, mul_comm (incA D _) c]
  rw [key, ← hlat, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
  have h1 : (Pi.single (Sum.inr 0) (p.pr c) : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j; simp
  simp [h1]

theorem mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ c : AE D, c ∈ idAt D P → ((fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k])) := by

  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr c hc
  have hyid : ∀ r, (fun r => c * incA D (vecB o ζ r)) r ∈ idAt D P := fun r => Ideal.mul_mem_right _ _ hc
  have hloc : (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ ∀ i,
      GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M (· = (p i).v) := by
    constructor
    · intro h i
      exact GlobalTheory.FinPlLoc.smul_latV _ (GlobalTheory.FinPlLoc.idem_mem_intAt _) h
    · intro h
      refine (GlobalTheory.FinPlLoc.part_lat P S₀ M _ hM.1).2 ⟨hyid, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
      have h1 : e • (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) =
          e • (fun r => c * incA D (vecB o ζ r)) := by
        rw [smul_smul, mul_comm, (GlobalTheory.FinPlLoc.mem_idAt_iff _ e).1 he.1]
      rw [← h1]
      exact GlobalTheory.FinPlLoc.smul_latV _ he (h i)
  rw [hloc]
  refine forall_congr' fun i => ?_
  have hεid : ∀ r, (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r ∈ idAt D (· = (p i).v) :=
    fun r => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_intAt _).1
  rw [GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts D k (p i) S₀ M _ hεid]
  have he : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * (p i).e = (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (FrameLat.e_mem_idAt (p i))
  have hce_id : cA D (p i).e ∈ idAt D (· = (p i).v) := by
    have := Ideal.sub_mem _ (FrameLat.sum_mem_idAt (p i)) (FrameLat.e_mem_idAt (p i))
    rwa [add_sub_cancel_left] at this
  have hce : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * cA D (p i).e = cA D (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hce_id
  have e1 : (fun r => (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (p i).e, he]
  have e2 : (fun r => cA D (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => cA D (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (cA D (p i).e), hce]
  rw [e1, e2, e_half D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) (hfr i).1 (hfr i).2 c,
    GlobalTheory.T.conjugateHalf_lineMultiple_mem_iff_integral D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) hM (hfr i).1 (hfr i).2 c]

end GlobalTheory.LineIdeal

end
