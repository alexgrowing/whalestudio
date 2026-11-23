import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaCommutant

theorem finrank_eq {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) :
    Module.finrank F (EA P p N) = N ^ P.g := by
  obtain ⟨-, -, hdim, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have h := rank_eq_of_equiv_equiv (R := F) (R' := Γ((Over.mk p).left, ⊤)) σ j.symm σ.bijective
    (fun c w => j.injective (by rw [j.apply_symm_apply, hj, j.apply_symm_apply]))
  have h' : Module.finrank F (EA P p N) = Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) := by
    unfold Module.finrank
    simpa using congrArg Cardinal.toNat h
  rw [h', hdim]

theorem eq_smul_of_commute {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) (T : EA P p N →ₗ[F] EA P p N)
    (hT : ∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → IsActOf P.A P.L (N : ℤ) θ (T v).sec (T v').sec) :
    ∃ c : F, ∀ v, T v = c • v := by
  have hN1 : 0 < N := Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero])
  have hfr := finrank_eq P F p N hN
  have hpos : 0 < Module.finrank F (EA P p N) := by rw [hfr]; positivity
  haveI : Module.Finite F (EA P p N) := Module.finite_of_finrank_pos hpos
  haveI : Nontrivial (EA P p N) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨-, hirr⟩ := GlobalTheory.ThetaIrred.main GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  obtain ⟨ρ, hact, -, hsame, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns S P (N : ℤ) (Over.mk p)
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have hσ : ∀ c : F, σ.symm (σ c) = c := σ.symm_apply_apply
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, ?_⟩
  have key := hirr (Module.End.eigenspace T c) fun θ hθ v v' hvv hv => by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    obtain ⟨θ₀, h₀, hcomm⟩ := hT θ.pt hθ
    obtain ⟨u, hu⟩ := hsame θ₀ θ h₀
    have e₁ : ρ θ (j.symm v) = j.symm v' := (hact θ _ _).1 hvv
    have e₂ : IsActOf P.A P.L (N : ℤ) θ₀ v.sec (j (ρ θ₀ (j.symm v))).sec := (hact θ₀ _ _).2 rfl
    have e₃ : ρ θ₀ (j.symm (T v)) = j.symm (T (j (ρ θ₀ (j.symm v)))) := (hact θ₀ _ _).1 (hcomm _ _ e₂)
    have e₄ : v' = σ.symm (u : Γ((Over.mk p).left, ⊤)) • j (ρ θ₀ (j.symm v)) := by
      rw [← hj, σ.apply_symm_apply, ← hu, e₁, j.apply_symm_apply]
    have e₅ : T (j (ρ θ₀ (j.symm v))) = c • j (ρ θ₀ (j.symm v)) := by
      have e₆ : j.symm (c • v) = σ c • j.symm v := rfl
      rw [← j.apply_symm_apply (T (j (ρ θ₀ (j.symm v)))), ← e₃, hv, e₆, map_smul, hj]
    rw [e₄, map_smul, e₅, smul_comm]
  rcases key with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · intro v
    exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)

end GlobalTheory.ThetaCommutant
