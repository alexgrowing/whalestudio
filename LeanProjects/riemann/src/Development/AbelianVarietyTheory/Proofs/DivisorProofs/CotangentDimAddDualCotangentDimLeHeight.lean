import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebungStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PDivGroup.CotDim in

theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)
  have haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤
      Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))

  have hker : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k := fun a ha => by
    have h1 := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h1
    rw [Submodule.restrictScalars_mem,
      ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]
    exact h1
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤
      Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  have key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤
      p ^ Γ.height := by
    rw [pow_add, mul_comm, ← hdimD, hord]
    exact Nat.mul_le_mul haD (haA.trans hrD)
  exact (Nat.pow_le_pow_iff_right hp2).1 key
