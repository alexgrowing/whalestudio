import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.FinZeta (Gv embV VacFin)
open GlobalTheory.AdelicU (frameLat)

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TransferOn (D : D7) (C : HeightOneSpectrum (𝓞 D.host.F) → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t →
  ∀ v, C v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χS w' ∧ GlobalTheory.LFun.UnrAt χT w') →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (U : Submodule ℂ (WO S T → ℂ))
    (hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U) (f : U), VacFin ψ S T v f →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv S v) X) (x : X) (B : Multiset ℂˣ),
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ x B →
  ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (Gv T v) X') (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ a a' (u : U) y, b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a y) = ρ' a' (b u y)) → b f x ≠ 0 →
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig T.gram (frameLat T) h ρ' (b f x) (stepPar χS χT t (fun _ => B) w)

def CosetSym {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∀ g : G, Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)} = Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g⁻¹ : G) : G ⧸ K)}

theorem TransferOn.mono {D : D7} {C C' : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : TransferOn D C) (hC : ∀ v, C' v → C v) :
    TransferOn D C' := fun ψ S T χS χT om hW t ht v hv => h ψ S T χS χT om hW t ht v (hC v hv)

example {G : Type} [Group G] : CosetSym (⊤ : Subgroup G) := fun g => by
  have e : ∀ g : G, Nat.card {c : G ⧸ (⊤ : Subgroup G) // ∃ k ∈ (⊤ : Subgroup G), c = ((k * g : G) : G ⧸ (⊤ : Subgroup G))} = 1 := fun g => by
    haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨⟨_, 1, trivial, rfl⟩⟩⟩
  rw [e, e]

end GlobalTheory.ChainOnto

end
