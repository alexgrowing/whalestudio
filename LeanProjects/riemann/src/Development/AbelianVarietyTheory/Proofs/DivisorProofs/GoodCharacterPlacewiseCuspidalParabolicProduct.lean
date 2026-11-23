import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.LocalToGlobal.Columns.GoodXgFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.CharacterEqOfRepIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCoeffChiIdemMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProducStatement

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.GoodCharProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isIrrChar_of_abs {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K] (σ : K →+* ℂ) {χ : G → K}
    (h : IsAbsIrrChar χ) : Formalism.L2.NT.IsIrrChar (fun g => σ (χ g)) := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  letI : Algebra K ℂ := σ.toAlgebra
  let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have hι : ∀ x : K, ι (algebraMap K (AlgebraicClosure K) x) = σ x := fun x => ι.commutes x
  have hch : ∀ g, ρ.character g = Matrix.trace (LinearMap.toMatrix' (ρ g)) := fun g => by
    rw [Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n)),
      LinearMap.toMatrix_eq_toMatrix']
  let ρm : G →* GL (Fin n) (AlgebraicClosure K) :=
    MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv' : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K)
      ≃ₐ[AlgebraicClosure K] Matrix (Fin n) (Fin n) (AlgebraicClosure K)).toRingEquiv.toMonoidHom.comp ρ)
  let ρc : G →* GL (Fin n) ℂ := (Matrix.GeneralLinearGroup.map (ι : AlgebraicClosure K →+* ℂ)).comp ρm
  have htr : ∀ g, Matrix.trace (ρc g : Matrix (Fin n) (Fin n) ℂ) = σ (χ g) := fun g => by
    rw [← hι, ← hχ g, hch g]
    simp [ρc, ρm, Matrix.trace, Matrix.diag, map_sum]
  have hC : ∀ g, star (σ (χ g)) = σ (χ g⁻¹) := fun g => by
    have := PI.SerBridgeGLW.conjugate_character_formula G (PI.SerBridgeGLW.repOfGL ρc) g
    rwa [PI.SerBridgeGLW.repOfGL_character, PI.SerBridgeGLW.repOfGL_character, htr, htr] at this
  refine ⟨⟨n, ρc, fun g => (htr g).symm⟩, ?_⟩
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := AlgebraicClosure K) (ψ := ρ.character) (ψ' := ρ.character)
    ⟨n, ρ, hρ, rfl⟩ ⟨n, ρ, hρ, rfl⟩
  rw [if_pos rfl] at horth
  have hcard : (Nat.card G : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : AlgebraicClosure K) := by
    rw [← mul_one (Nat.card G : AlgebraicClosure K), ← horth, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  unfold Formalism.L2.NT.ipG
  simp only [hC]
  have := congrArg ι hsum
  rw [map_sum, map_natCast, Nat.card_eq_fintype_card] at this
  rw [← this]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, hχ, hχ, hι, hι]

theorem isIrrChar_comp {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (e : G' ≃* G) {χ : G → ℂ}
    (h : Formalism.L2.NT.IsIrrChar χ) : Formalism.L2.NT.IsIrrChar fun x => χ (e x) := by
  obtain ⟨⟨n, ρ, hρ⟩, hip⟩ := h
  refine ⟨⟨n, ρ.comp e.toMonoidHom, fun x => hρ _⟩, ?_⟩
  unfold Formalism.L2.NT.ipG at hip ⊢
  rw [Fintype.card_congr e.toEquiv, ← hip]
  exact Fintype.sum_equiv e.toEquiv _ _ fun _ => rfl

theorem isProdCuspChar_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hrec hE hX χ hχ
  classical
  obtain ⟨eR, plg, iso, h1, -, h2⟩ := hrec
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  have hirr : Formalism.L2.NT.IsIrrChar fun x : G0g D.nd => D.what₂.embLL (χ (eR.symm x)) :=
    isIrrChar_comp eR.symm (isIrrChar_of_abs D.what₂.embLL (hX χ hχ))
  have he0 : ∑ x : G0g D.nd, D.ntypes.e0.coeff x * D.what₂.embLL (χ (eR.symm x)) = D.what₂.embLL (χ (eR.symm 1)) := by
    have h0 := congrArg D.what₂.embLL (GlobalTheory.IdemChar.sum_coeff_idemOf_mul D.what₂.LL G A.X hX χ hχ)
    rw [map_sum] at h0
    rw [map_one, ← h0]
    symm
    refine Fintype.sum_equiv eR.toEquiv _ _ fun g => ?_
    simp [h1]
  obtain ⟨θ, hθ, hχθ⟩ := GlobalTheory.T.irreducible_character_good_idempotent_cuspidal_product' D hE _ hirr he0
  have key : ∀ PP : R.Pg, ∃ θ' : GL (Fin D.R.r) (kP PP.1) → ℂ,
      @GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) D.R.r θ' ∧
        ∀ g, θ' (R.eG g PP) = θ (plg.symm PP) (eR g (plg.symm PP)) := by
    intro PP
    obtain ⟨kv, rfl⟩ := plg.surjective PP
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    letI := Ideal.Quotient.field (plg kv).1.asIdeal
    refine ⟨_, GlobalTheory.FinGL.Transport.isCuspProdChar_transport _ _ (iso kv) _ _ (hθ kv), fun g => ?_⟩
    rw [Equiv.symm_apply_apply, h2]
    exact congrArg _ ((GlobalTheory.FinGL.Transport.glEquiv (iso kv) D.R.r).symm_apply_apply _)
  choose θ' hθ' hθ'' using key
  refine ⟨θ', hθ', fun x => ?_⟩
  obtain ⟨g, rfl⟩ := R.eG.surjective x
  simp only [hθ'', MulEquiv.symm_apply_apply]
  have h3 := hχθ (eR g)
  rw [MulEquiv.symm_apply_apply] at h3
  rw [h3]
  exact (Fintype.prod_equiv plg.symm _ _ fun _ => rfl).symm

end GlobalTheory.GoodCharProd

end
