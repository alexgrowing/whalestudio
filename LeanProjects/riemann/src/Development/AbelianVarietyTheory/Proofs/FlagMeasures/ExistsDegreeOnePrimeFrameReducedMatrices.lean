import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddEquivOfCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped Matrix

namespace GlobalTheory.RowLev

theorem exists_coords_of_frame {A κ : Type} [CommRing A] [CommRing κ] {n : ℕ} (R : Subring A)
    (L : Submodule R (Fin n → A)) (β : GL (Fin n) A)
    (hβ : ∀ y, y ∈ L ↔ ∀ i, ((β⁻¹ : GL (Fin n) A).1 *ᵥ y) i ∈ R) (r : R →+* κ) (hr : Function.Surjective r) :
    ∃ c : L →ₛₗ[r] (Fin n → κ), Function.Surjective c ∧
      (∀ y : L, c y = 0 ↔ (y : Fin n → A) ∈ RingHom.ker r • L) ∧
      ∀ (X : GL (Fin n) A) (M : Matrix (Fin n) (Fin n) κ),
        (∀ y ∈ L, X.1 *ᵥ y ∈ L) →
        (∀ i j (h : (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R), r ⟨_, h⟩ = M i j) →
        ∀ (y : L) (h : X.1 *ᵥ (y : Fin n → A) ∈ L), c ⟨_, h⟩ = M *ᵥ c y := by
  classical
  set B : Matrix (Fin n) (Fin n) A := (β⁻¹ : GL (Fin n) A).1 with hB
  have hBβ : B * β.1 = 1 := by rw [hB]; exact Units.inv_mul β
  have hβB : β.1 * B = 1 := by rw [hB]; exact Units.mul_inv β
  have hmem : ∀ y : L, ∀ i, (B *ᵥ (y : Fin n → A)) i ∈ R := fun y => (hβ y).1 y.2

  have hcol : ∀ j, (fun k => β.1 k j) ∈ L := by
    intro j
    refine (hβ _).2 fun i => ?_
    have e : (B *ᵥ fun k => β.1 k j) i = (B * β.1) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    change (B *ᵥ fun k => β.1 k j) i ∈ R
    rw [e, hBβ, Matrix.one_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem

  have hexp : ∀ v : Fin n → A, v = ∑ j, (B *ᵥ v) j • (fun k => β.1 k j) := by
    intro v
    have h1 : β.1 *ᵥ (B *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hβB, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  let c : L →ₛₗ[r] (Fin n → κ) :=
    { toFun := fun y i => r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩
      map_add' := by
        intro y z
        funext i
        have e : (⟨(B *ᵥ ((y + z : L) : Fin n → A)) i, hmem (y + z) i⟩ : R) =
            ⟨_, hmem y i⟩ + ⟨_, hmem z i⟩ := Subtype.ext (by simp [Matrix.mulVec_add])
        simp only [Pi.add_apply]
        rw [e, map_add]
      map_smul' := by
        intro a y
        funext i
        have e : (⟨(B *ᵥ ((a • y : L) : Fin n → A)) i, hmem (a • y) i⟩ : R) = a * ⟨_, hmem y i⟩ := by
          apply Subtype.ext
          change (B *ᵥ ((a : A) • (y : Fin n → A))) i = (a : A) * (B *ᵥ (y : Fin n → A)) i
          rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [e, map_mul] }
  have hc : ∀ (y : L) i, c y i = r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩ := fun _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  ·
    intro v
    choose x hx using fun i => hr (v i)
    set y0 : Fin n → A := β.1 *ᵥ fun i => (x i : A) with hy0
    have hc0 : ∀ i, (B *ᵥ y0) i = x i := by
      intro i
      rw [hy0, Matrix.mulVec_mulVec, hBβ, Matrix.one_mulVec]
    have hm : y0 ∈ L := (hβ y0).2 fun i => by rw [hc0 i]; exact (x i).2
    refine ⟨⟨y0, hm⟩, ?_⟩
    funext i
    rw [hc, ← hx i]
    congr 1
    exact Subtype.ext (hc0 i)
  · intro y
    constructor
    · intro hy
      have hk : ∀ j, (⟨_, hmem y j⟩ : R) ∈ RingHom.ker r := by
        intro j
        rw [RingHom.mem_ker, ← hc]
        exact congrFun hy j
      have e : (y : Fin n → A) = ∑ j, (⟨_, hmem y j⟩ : R) • (fun k => β.1 k j) := hexp _
      rw [e]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hk j) (hcol j)
    · intro hy
      have key : ∀ i, ∃ h : (B *ᵥ (y : Fin n → A)) i ∈ R, r ⟨_, h⟩ = 0 := by
        refine Submodule.smul_induction_on
          (p := fun z : Fin n → A => ∀ i, ∃ h : (B *ᵥ z) i ∈ R, r ⟨_, h⟩ = 0) hy ?_ ?_
        · intro a ha m hm i
          have e : (B *ᵥ (a • m)) i = (a : A) * (B *ᵥ m) i := by
            change (B *ᵥ ((a : A) • m)) i = _
            rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
          have hm' : (B *ᵥ m) i ∈ R := (hβ m).1 hm i
          refine ⟨e ▸ R.mul_mem a.2 hm', ?_⟩
          have e2 : (⟨(B *ᵥ (a • m)) i, e ▸ R.mul_mem a.2 hm'⟩ : R) = a * ⟨_, hm'⟩ := Subtype.ext e
          rw [e2, map_mul, (RingHom.mem_ker).1 ha, zero_mul]
        · intro u v hu hv i
          obtain ⟨h1, e1⟩ := hu i
          obtain ⟨h2, e2⟩ := hv i
          have e : (B *ᵥ (u + v)) i = (B *ᵥ u) i + (B *ᵥ v) i := by
            rw [Matrix.mulVec_add, Pi.add_apply]
          refine ⟨e ▸ R.add_mem h1 h2, ?_⟩
          have e3 : (⟨(B *ᵥ (u + v)) i, e ▸ R.add_mem h1 h2⟩ : R) = ⟨_, h1⟩ + ⟨_, h2⟩ := Subtype.ext e
          rw [e3, map_add, e1, e2, add_zero]
      funext i
      obtain ⟨_, h⟩ := key i
      rw [hc]
      exact h
  · intro X M hXL hM y h
    have hP : ∀ i j, (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R := by
      intro i j
      have hXc : X.1 *ᵥ (fun k => β.1 k j) ∈ L := hXL _ (hcol j)
      have e : (β⁻¹ * X * β : GL (Fin n) A).1 i j = (B *ᵥ (X.1 *ᵥ fun k => β.1 k j)) i := by
        rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec]
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e]
      exact (hβ _).1 hXc i
    have hPv : B *ᵥ (X.1 *ᵥ (y : Fin n → A)) =
        (β⁻¹ * X * β : GL (Fin n) A).1 *ᵥ (B *ᵥ (y : Fin n → A)) := by
      rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc (B * X.1), hβB, Matrix.mul_one]
    funext i
    have e : (⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ : R) =
        ∑ j, (⟨_, hP i j⟩ : R) * ⟨_, hmem y j⟩ := by
      apply Subtype.ext
      change (B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i = _
      rw [hPv]
      simp [Matrix.mulVec, dotProduct]
    rw [hc]
    change r ⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ = _
    rw [e, map_sum]
    simp only [map_mul, hM, Matrix.mulVec, dotProduct, hc]

private theorem hatL_eq_Lf' (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem exists_plFrame_of_isFrame : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (N p : ℕ) (hN : I.n = N) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)), p.Prime → Nat.card (𝓞 I.E ⧸ w.asIdeal) = p → ∃ fr : GlobalTheory.RowLev.PlFrame I N p w, ∀ k ∈ I.Kset, ∀ M : Matrix (Fin N) (Fin N) (ZMod p), (∀ (i j : Fin N) (hij : ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (Fin.cast hN.symm i) (Fin.cast hN.symm j) ∈ Formalism.L2.Herm.intAf I.F I.E), Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w)) → fr.ActsAs k M := by
  intro I β₀ hF N p hN w hp hcard
  subst hN
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hL : ∀ y, y ∈ I.Lf ↔
      ∀ i, ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).1 *ᵥ y) i ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    intro y
    rw [← hatL_eq_Lf' I]
    exact hF y

  have : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let : Fintype (Formalism.L2.DIV.kP w) := Fintype.ofFinite _
  have hcard' : Fintype.card (Formalism.L2.DIV.kP w) = p := by rw [Fintype.card_eq_nat_card]; exact hcard
  have : CharP (Formalism.L2.DIV.kP w) p := charP_of_card_eq_prime hcard'
  let e : ZMod p ≃+* Formalism.L2.DIV.kP w := ZMod.ringEquiv (Formalism.L2.DIV.kP w) hcard'
  let r : Formalism.MainNotions.S.IntAf I.F I.E →+* ZMod p :=
    (e.symm : Formalism.L2.DIV.kP w →+* ZMod p).comp (Formalism.L2.DIV.resS I.F w)
  have hr : ∀ s, r s = e.symm (Formalism.L2.DIV.resS I.F w s) := fun _ => rfl
  have hres : ∀ a : 𝓞 I.E, r (Formalism.L2.DIV.oToS I.F I.E a) = 0 ↔ a ∈ w.asIdeal := by
    intro a
    rw [hr, Formalism.L2.DIV.resS_oToS, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hrs : Function.Surjective r := by
    intro q
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := w.asIdeal) (e q)
    refine ⟨Formalism.L2.DIV.oToS I.F I.E a, ?_⟩
    rw [hr, Formalism.L2.DIV.resS_oToS, ha, RingEquiv.symm_apply_apply]
  obtain ⟨c, hcs, hck, hca⟩ := exists_coords_of_frame (Formalism.MainNotions.S.IntAf I.F I.E) I.Lf β₀ hL r hrs
  have hker : RingHom.ker r = extId I w.asIdeal := by
    refine Inhab.ker_eq_extId hp.ne_zero r fun a => ?_
    have e1 : Inhab.psi I.F I.E a = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  refine ⟨{ r := r, r_ker := fun a h => ?_, c := c, c_surj := hcs, c_ker := fun y => ?_ }, ?_⟩
  · have e1 : (⟨_, h⟩ : Formalism.MainNotions.S.IntAf I.F I.E) = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  · rw [hck y, hker]
  · intro k hk M hM y h
    refine hca (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) M (fun y hy => Inhab.mulVec_mem hk hy)
      (fun i j hij => ?_) y h
    have h1 : Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w) := hM i j hij
    rw [hr, h1, map_natCast, ZMod.natCast_zmod_val]

end GlobalTheory.RowLev
