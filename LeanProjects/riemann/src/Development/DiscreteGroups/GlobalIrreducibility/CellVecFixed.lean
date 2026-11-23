import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.InCellMulRightIff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {S : Subgroup (GL (Fin m) k)}

def cellVec (hS1 : KOne k (Fin m) ≤ S)
    (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1) :
    IndSp (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) :=
  ⟨⟨cellFun S, fun p g => by
      rw [cellFun_mul_left hS4]
      simp [dl]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (GlobalTheory.StepData.isOpen_KOne.mem_nhds (one_mem _)) fun x hx =>
      Subtype.ext (funext fun g => cellFun_mul_right hS4 (hS1 hx) g))⟩

variable (hS1 : KOne k (Fin m) ≤ S)
  (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)

theorem cellVec_apply (g : GL (Fin m) k) : (cellVec hS1 hS4).1.1 g = cellFun S g := rfl

theorem cellVec_fixed {s : GL (Fin m) k} (hs : s ∈ S) : psOne k m s (cellVec hS1 hS4) = cellVec hS1 hS4 :=
  Subtype.ext (Subtype.ext (funext fun g => cellFun_mul_right hS4 hs g))

open Classical in
include hS1 hS4 in
theorem cellFun_wRev (hS2 : S ≤ KO k (Fin m))
    (hS3 : ∀ y ∈ S, ∀ a b, a < b → valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b) < 1)
    {c : GL (Fin m) k} (hc : c ∈ unipB k (Fin m)) :
    cellFun S (wRev k m * c⁻¹) = if c ∈ KOne k (Fin m) then 1 else 0 := by
  split_ifs with hK
  · have e : wRev k m * c⁻¹ = (((1 : parab k (eOne m)) : GL (Fin m) k)) * wRev k m * c⁻¹ := by simp
    rw [e, cellFun_eq hS4 1 (hS1 (inv_mem hK)), dl_one, Units.val_one]
  · rw [cellFun, dif_neg]
    rintro ⟨p, y, hy, e⟩
    apply hK
    have hy' : y = (wRev k m * (p : GL (Fin m) k)⁻¹ * wRev k m) * c⁻¹ :=
      calc y = ((p : GL (Fin m) k) * wRev k m)⁻¹ * ((p : GL (Fin m) k) * wRev k m * y) := by group
        _ = ((p : GL (Fin m) k) * wRev k m)⁻¹ * (wRev k m * c⁻¹) := by rw [← e]
        _ = (wRev k m)⁻¹ * (p : GL (Fin m) k)⁻¹ * wRev k m * c⁻¹ := by group
        _ = _ := by rw [wRev_inv]
    have hci : c⁻¹ ∈ unipB k (Fin m) := inv_mem hc
    have hX : ∀ i j, ((((wRev k m * (p : GL (Fin m) k)⁻¹ * wRev k m : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        ((c⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) i j) = ((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j := by
      intro i j; rw [hy']; simp only [Units.val_mul]
    have hpi : ((p : GL (Fin m) k)⁻¹) ∈ parab k (eOne m) := inv_mem p.2
    have key := valuation_unitri_lt (valuation k)
      (((wRev k m * (p : GL (Fin m) k)⁻¹ * wRev k m : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
      (((c⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
      (fun i j hij => by
        rw [wRev_conj_apply]
        exact (mem_parab.1 hpi) (Fin.rev i) (Fin.rev j) (by simpa using Fin.rev_lt_rev.2 hij))
      (fun i => ((mem_unipB _).1 hci).2 i) (fun i j hij => ((mem_unipB _).1 hci).1 i j hij)
      (fun i j => by rw [hX]; exact val_le_of_mem_KO (hS2 hy) i j)
      (fun i => by rw [hX]; exact hS4 y hy i)
      (fun i j hij => by rw [hX]; exact hS3 y hy i j hij)
    have hK' : c⁻¹ ∈ KOne k (Fin m) := mem_KOne_of_unip hci key
    simpa using inv_mem hK'

end DiscreteGroups.sglob.DzType
