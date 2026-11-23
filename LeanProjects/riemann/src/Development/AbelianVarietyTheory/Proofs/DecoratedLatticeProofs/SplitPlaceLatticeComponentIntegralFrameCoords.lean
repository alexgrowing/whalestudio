import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal.LatChar

variable {D : D7}

theorem finPart_pair_zero (α : Af D.host.F) (x : D.host.E) :
    finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = α ⊗ₜ[D.host.F] x := rfl

theorem latV_int {S : HSp D} {L : Lat S} (hL : ∀ z ∈ L, z ∈ intVec D S.rank) {P : Pl D → Prop}
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) (i : Fin S.rank) : finPart D (y i) ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    change finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) ∈ intAE D
    rw [finPart_pair_zero, one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => rw [Pi.zero_apply, RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Pi.add_apply, RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [Pi.neg_apply, RingHom.map_neg]; exact neg_mem hx

theorem lat_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
    {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    β.IsLat L Λ → (∀ z, z ∈ L ↔ z ∈ intVec D _) → ∀ x : n → k, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  intro D k _ _ _ _ p S n _ _ β L Λ hΛ hL x
  rw [hΛ x]
  constructor
  · intro h r
    exact (p.int_iff _).2 (latV_int (fun z hz => (hL z).1 hz) h r)
  · intro h
    have h1 : (fun i => p.sec ((β.b *ᵥ x) i)) =
        ∑ r, fun i => p.sec ((β.b *ᵥ x) r) * incA D ((Pi.single r 1 : Fin S.rank → D.host.E) i) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, RingHom.map_one, mul_one]
      · intro r _ hr
        rw [Pi.single_eq_of_ne hr.symm, RingHom.map_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h1]
    refine sum_mem fun r _ => GlobalTheory.FinPl.FrameLat.int_mul_mem (GlobalTheory.FinPl.FrameLat.sec_mem_intAt p _ (h r)) ((hL _).2 fun i => ?_)
    by_cases hi : i = r
    · subst hi; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hi]; exact isIntegral_zero

end GlobalTheory.PhiOneVal.LatChar
