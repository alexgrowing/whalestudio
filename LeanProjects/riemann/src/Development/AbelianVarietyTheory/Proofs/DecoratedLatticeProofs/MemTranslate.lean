import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem rTrans_rTrans {G : Type} [Semigroup G] (a b : G) (F : G → ℂ) : rTrans a (rTrans b F) = rTrans (a * b) F := by
  funext g; simp [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans 1 F = F := by
  funext g; simp [rTrans]

def space (Q : QStep S) : Submodule ℂ (GA D S.B'.V → ℂ) where
  carrier := {f | (∀ y, IsContAut S.B'.V (rTrans (Q.gl₂ y) f)) ∧
    ∃ U : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k), IsOpen (U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)) ∧
      ∀ u ∈ U, rTrans (Q.gl₂ u) f = f}
  zero_mem' := ⟨fun y => ⟨fun _ _ _ => rfl, continuous_const⟩, ⊤, isOpen_univ, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, U, hU, hfU⟩ ⟨hg, V, hV, hgV⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U ⊓ V, hU.inter hV, fun u hu => ?_⟩
    · change f (γ * x * _) + g (γ * x * _) = f (x * _) + g (x * _)
      have h1 := (hf y).1 γ hγ x
      have h2 := (hg y).1 γ hγ x
      simp only [rTrans] at h1 h2
      rw [h1, h2]
    · exact (hf y).2.add (hg y).2
    · have h1 := hfU u hu.1
      have h2 := hgV u hu.2
      funext x
      have e1 := congrFun h1 x
      have e2 := congrFun h2 x
      simp only [rTrans, Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  smul_mem' := by
    rintro a f ⟨hf, U, hU, hfU⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U, hU, fun u hu => ?_⟩
    · have h1 := (hf y).1 γ hγ x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1]
    · exact continuous_const.mul (hf y).2
    · have h1 := hfU u hu
      funext x
      have e1 := congrFun h1 x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [e1]

theorem mem_translate (Q : QStep S) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) {f : GA D S.B'.V → ℂ} (hf : f ∈ space Q) :
    rTrans (Q.gl₂ y) f ∈ space Q := by
  obtain ⟨hc, U, hU, hfU⟩ := hf
  refine ⟨fun y' => ?_, U.comap (MulAut.conj y⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
  · rw [rTrans_rTrans, ← map_mul]; exact hc _
  · have hc : Continuous fun x : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k => y⁻¹ * x * y⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hU.preimage hc
  · have hu' : y⁻¹ * u * y ∈ U := by simpa using hu
    rw [rTrans_rTrans, ← map_mul, show u * y = y * (y⁻¹ * u * y) by group, map_mul, ← rTrans_rTrans, hfU _ hu']

def rep (Q : QStep S) : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) (space Q) where
  toFun y :=
    { toFun := fun f => ⟨rTrans (Q.gl₂ y) f.1, mem_translate Q y f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp [rTrans]
  map_mul' x y := by
    ext f g
    rw [Module.End.mul_apply]
    change f.1 (g * Q.gl₂ (x * y)) = f.1 (g * Q.gl₂ x * Q.gl₂ y)
    rw [map_mul, mul_assoc]

def valK (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ)
    (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ))
    (Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k)) (f : GA D S.B'.V → ℂ) : ℂ :=
  S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) f

theorem smooth (Q : QStep S) : IsSmoothRep (rep Q) := by
  intro v
  obtain ⟨-, U, hU, hfU⟩ := v.2
  let H : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) :=
    { carrier := {g | rep Q g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : U ≤ H := fun u hu => Subtype.ext (hfU u hu)
  exact Subgroup.isOpen_mono hle hU

end GlobalTheory.TriStep
end
