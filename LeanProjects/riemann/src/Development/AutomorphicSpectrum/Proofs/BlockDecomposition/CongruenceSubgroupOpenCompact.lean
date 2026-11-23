import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

open GlobalTheory.SplitWeil Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def nearSet (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {A | NearOne s A}

def ballMat (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {B | ∀ a b, B a b ∈ cball s}

theorem ballMat_eq (s : kˣ) (m : ℕ) : ballMat (k := k) s m =
    (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s : Set (Fin m → Fin m → k)) :=
  Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩

theorem isOpen_ballMat (s : kˣ) (m : ℕ) : IsOpen (ballMat (k := k) s m) := by
  simp only [ballMat, Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_cball s).preimage (f := fun A : Matrix (Fin m) (Fin m) k => A i j) (by fun_prop)

theorem isCompact_ballMat (s : kˣ) (m : ℕ) : IsCompact (ballMat (k := k) s m) := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s :
      Set (Fin m → Fin m → k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s
  rw [ballMat_eq]; exact h

theorem nearSet_eq (s : kˣ) (m : ℕ) : nearSet (k := k) s m =
    (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)) ⁻¹' ballMat s m := by
  ext A
  simp only [nearSet, NearOne, ballMat, Set.mem_setOf_eq, Set.mem_preimage, Homeomorph.subRight_apply,
    Matrix.sub_apply]

theorem isOpen_nearSet (s : kˣ) (m : ℕ) : IsOpen (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (isOpen_ballMat s m).preimage (Homeomorph.continuous _)

theorem isCompact_nearSet (s : kˣ) (m : ℕ) : IsCompact (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)).isCompact_preimage.2 (isCompact_ballMat s m)

theorem congGL_eq (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    (congGL k s hs m : Set (GL (Fin m) k)) =
      (fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m ∩
        (fun g : GL (Fin m) k => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m :=
  rfl

theorem isOpen_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsOpen (congGL k s hs m : Set (GL (Fin m) k)) := by
  rw [congGL_eq]
  exact ((isOpen_nearSet s m).preimage Units.continuous_val).inter
    ((isOpen_nearSet s m).preimage Units.continuous_coe_inv)

theorem isCompact_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsCompact (congGL k s hs m : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK := isCompact_nearSet (k := k) s m
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin m) (Fin m) k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [congGL_eq, Set.mem_inter_iff, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem congM_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
  IsOpen (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) := by
  intro k _ _ _ _ n s hs
  have e : (congM k s hs n : Set (Mir k n)) =
      (Subtype.val : Mir k n → GL (Fin (n + 1)) k) ⁻¹' (congGL k s hs (n + 1) : Set (GL (Fin (n + 1)) k)) := rfl
  rw [e]
  exact ⟨(Topo.isOpen_congGL s hs (n + 1)).preimage continuous_subtype_val,
    (GlobalTheory.CompanionTheory.BZMirOnto.isClosed_Mir k n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (Topo.isCompact_congGL s hs (n + 1))⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
