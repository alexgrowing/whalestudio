import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMultOneDimOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOneStatement
open Formalism.BasicNotions GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

def addOf {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) : AddChar (ZMod p) ℂ where
  toFun a := (θ (Multiplicative.ofAdd a) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [ofAdd_add]

theorem addOf_ne_one {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : θ ≠ 1) : addOf θ ≠ 1 := by
  intro h1
  apply h
  refine MonoidHom.ext fun z => Units.ext ?_
  have h2 : addOf θ (Multiplicative.toAdd z) = 1 := by rw [h1]; rfl
  exact h2

theorem addCharHom_addOf {p r : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : unip (ZMod p) r) :
    ((addCharHom (addOf θ) (supHom (ZMod p) r) h : ℂˣ) : ℂ) =
      (θ (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))) : ℂ) :=
  rfl

theorem local_sum_ne_zero {p : ℕ} [hp : Fact p.Prime] {r : ℕ} [Fintype (unip (ZMod p) r)] (θ : GL (Fin r) (ZMod p) → ℂ)
    (hθ : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ) (θ' : Multiplicative (ZMod p) →* ℂˣ) (h' : θ' ≠ 1) :
    ∑ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ)
      ≠ 0 := by
  obtain ⟨d, b, σ, hσ, hθe⟩ := hθ
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.finite_parInd (F := ZMod p) b σ
  have h1 := GlobalTheory.GenericProduct.sum_unip_eq (addOf θ') (parInd b σ)
  rw [GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one (ZMod p) (addOf θ') (addOf_ne_one θ' h') r _ b σ hσ, Nat.cast_one, mul_one] at h1
  have e : ∀ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ) =
      LinearMap.trace ℂ _ (parInd b σ h) * (((addCharHom (addOf θ') (supHom (ZMod p) r) h)⁻¹ : ℂˣ) : ℂ) := by
    intro h
    rw [hθe, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, addCharHom_addOf]
    rfl
  rw [Finset.sum_congr rfl fun h _ => e h, h1]
  exact Nat.cast_ne_zero.2 Nat.card_pos.ne'

end GlobalTheory.WhittakerMeets

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

theorem sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  intro D S _ U _ hU ψ hψ hr χ hχ he
  classical
  subst hU
  haveI hF : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fact (D.host.g kv.1).Prime := fun kv => ⟨D.host.g_prime kv.1⟩
  haveI hN : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), NeZero (D.host.g kv.1) := fun kv => ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ, hθ, hχe⟩ := GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product D (fun k => ⟨_, S.O k, S.eSer_def k⟩) χ hχ he
  obtain ⟨θ', hθ'1, hψe⟩ := hψ
  have hθ' := hθ'1 hr
  letI : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fintype (unip (ZMod (D.host.g kv.1)) D.R.r) := fun kv => Fintype.ofFinite _
  let f : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r → ℂ := fun kv h =>
    θ kv h * (((θ' kv (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
      ((h : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))))⁻¹ : ℂˣ) : ℂ)
  let e : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ≃
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r :=
    { toFun := fun u kv => ⟨u.1 kv, (u.2 kv).1, (u.2 kv).2⟩
      invFun := fun y => ⟨fun kv => (y kv).1, fun kv => ⟨(y kv).2.1, (y kv).2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hterm : ∀ u : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r,
      χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) = ∏ kv, f kv (e u kv) := by
    intro u
    rw [hχe, hψe, Formalism.L2.NX.stdVal, ← Finset.prod_inv_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
    rfl
  rw [Finset.sum_congr rfl fun u _ => hterm u, Fintype.sum_equiv e _ (fun y => ∏ kv, f kv (y kv)) fun _ => rfl,
    ← Fintype.prod_sum]
  exact Finset.prod_ne_zero_iff.2 fun kv _ => local_sum_ne_zero (θ kv) (hθ kv) (θ' kv) (hθ' kv)

end GlobalTheory.WhittakerMeets
