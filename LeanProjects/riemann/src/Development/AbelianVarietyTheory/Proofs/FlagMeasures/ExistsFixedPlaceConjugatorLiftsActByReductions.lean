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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponentsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactUnitaryOfSplitPlaceLiftStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryConjugatorOfSplitIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdelesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCastStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRectangularConjInstanceMatrixStandardPsiStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOnePrimeFrameReducedMatricesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceBaseNeOfDistinctTypePrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.FixedConj
open ReciprocityTheory.Aut

theorem smul_mul_mul_of_idem {R : Type} [CommRing R] {a b : ℕ} (e : R) (he : e * e = e)
    (M : Matrix (Fin a) (Fin b) R) (N : Matrix (Fin b) (Fin b) R) (Q : Matrix (Fin b) (Fin a) R) :
    e • (M * N * Q) = (e • M) * N * (e • Q) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, he]

theorem castMatrix_mul_mul_castMatrix_apply {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (X : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    ((Matrix.of fun (i : Fin a) (j : Fin b) => if (i : ℕ) = (j : ℕ) then (1 : R) else 0) * X *
      (Matrix.of fun (i : Fin b) (j : Fin a) => if (i : ℕ) = (j : ℕ) then (1 : R) else 0)) i j =
      X (Fin.cast h i) (Fin.cast h j) := by
  subst h
  have e1 : (Matrix.of fun (i : Fin a) (j : Fin a) => if (i : ℕ) = (j : ℕ) then (1 : R) else 0) = 1 := by
    ext i j; simp [Matrix.one_apply, Fin.ext_iff]
  rw [e1, Matrix.one_mul, Matrix.mul_one]
  rfl

theorem conj_sub_one {R : Type} [CommRing R] {a b : ℕ} (U : Matrix (Fin a) (Fin b) R) (U' : Matrix (Fin b) (Fin a) R)
    (hU : U * U' = 1) (C Ci X : Matrix (Fin b) (Fin b) R) (hC : C * Ci = 1) :
    U * (C * X * Ci) * U' - 1 = U * (C * (X - 1) * Ci) * U' := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hC, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]

theorem actsAs_congr {I : Formalism.MainNotions.S.AutInst} {N p : ℕ} {w w' : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)} (e : w = w')
    (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf) (M : Matrix (Fin N) (Fin N) (ZMod p)) :
    (e ▸ fr).ActsAs x M ↔ fr.ActsAs x M := by
  subst e; rfl

theorem castMatrix_mul_castMatrix {R : Type} [CommRing R] {a b : ℕ} (h : a = b) :
    (Matrix.of fun (i : Fin a) (j : Fin b) => if (i : ℕ) = (j : ℕ) then (1 : R) else 0) *
      (Matrix.of fun (i : Fin b) (j : Fin a) => if (i : ℕ) = (j : ℕ) then (1 : R) else 0) = 1 := by
  subst h
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [Matrix.one_apply, Fin.ext_iff]
  · intro k _ hk
    have : (i : ℕ) ≠ k := fun e => hk (Fin.ext e.symm)
    simp [this]
  · simp

theorem exists_unitary_transport {A R : Type} [CommRing A] [CommRing R] (θ : A ≃+* R) (σA : A →+* A) (σ : R →+* R)
    (hθσ : ∀ a, θ (σA a) = σ (θ a)) (n : ℕ) (cE : GL (Fin n) R)
    (hcE : (cE : Matrix (Fin n) (Fin n) R) * ReciprocityTheory.Aut.conjT σ (cE : Matrix (Fin n) (Fin n) R) = 1) :
    ∃ cA : GL (Fin n) A, (cA : Matrix (Fin n) (Fin n) A) * ReciprocityTheory.Aut.conjT σA (cA : Matrix (Fin n) (Fin n) A) = 1 ∧
      (cA : Matrix (Fin n) (Fin n) A).map θ = (cE : Matrix (Fin n) (Fin n) R) ∧
      ((cA⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).map θ = ((cE⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
  have hσ' : ∀ b, σA (θ.symm b) = θ.symm (σ b) := fun b => by
    apply θ.injective
    rw [hθσ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  refine ⟨Matrix.GeneralLinearGroup.map (θ.symm : R →+* A) cE, ?_, ?_, ?_⟩
  · have e2 : ReciprocityTheory.Aut.conjT σA ((Matrix.GeneralLinearGroup.map (θ.symm : R →+* A) cE : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) =
        (ReciprocityTheory.Aut.conjT σ (cE : Matrix (Fin n) (Fin n) R)).map θ.symm := by
      ext i j; simp [ReciprocityTheory.Aut.conjT, hσ']
    rw [e2]
    show (cE : Matrix (Fin n) (Fin n) R).map θ.symm * _ = 1
    rw [← Matrix.map_mul, hcE, Matrix.map_one _ (map_zero _) (map_one _)]
  · ext i j; simp
  · have : ((Matrix.GeneralLinearGroup.map (θ.symm : R →+* A) cE)⁻¹ : GL (Fin n) A) =
        Matrix.GeneralLinearGroup.map (θ.symm : R →+* A) cE⁻¹ := (map_inv _ _).symm
    rw [this]; ext i j
    exact RingEquiv.apply_symm_apply θ _

theorem part_eq {R : Type} [CommRing R] {m n : ℕ} (e : R) (he : e * e = e) (Z P : Matrix (Fin m) (Fin n) R)
    (Z' P' : Matrix (Fin n) (Fin m) R) (C : GL (Fin n) R)
    (hZ : e • (Z * (C : Matrix (Fin n) (Fin n) R)) = e • P)
    (hZ' : e • (((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') = e • P') (X : Matrix (Fin n) (Fin n) R) :
    e • (Z * ((C : Matrix (Fin n) (Fin n) R) * X * ((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) * Z') = e • (P * X * P') := by
  have e1 : Z * ((C : Matrix (Fin n) (Fin n) R) * X * ((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) * Z' =
      (Z * (C : Matrix (Fin n) (Fin n) R)) * X * (((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') := by
    simp only [Matrix.mul_assoc]
  rw [e1, smul_mul_mul_of_idem e he, hZ, hZ', ← smul_mul_mul_of_idem e he]

theorem res_eq_of_part {R k : Type} [CommRing R] [CommRing k] (S : Subring R) (res : S →+* k) (e : R) (he : e ∈ S)
    (hres : res ⟨e, he⟩ = 1) (a x : R) (ha : a ∈ S) (hx : x ∈ S) (h : e * a = e * x) :
    res ⟨a, ha⟩ = res ⟨x, hx⟩ := by
  have h1 : res ⟨e * a, S.mul_mem he ha⟩ = res ⟨e * x, S.mul_mem he hx⟩ := by
    congr 1; exact Subtype.ext h
  have h2 : res ⟨e * a, S.mul_mem he ha⟩ = res ⟨e, he⟩ * res ⟨a, ha⟩ := by rw [← map_mul]; rfl
  have h3 : res ⟨e * x, S.mul_mem he hx⟩ = res ⟨e, he⟩ * res ⟨x, hx⟩ := by rw [← map_mul]; rfl
  rw [h2, h3, hres, one_mul, one_mul] at h1
  exact h1

theorem res_eq_of_off {R k : Type} [CommRing R] [CommRing k] (S : Subring R) (res : S →+* k) (e : R) (he : e ∈ S)
    (hres : res ⟨e, he⟩ = 0) (a d : R) (ha : a ∈ S) (hd : d ∈ S) (h : (1 - e) * (a - d) = 0) :
    res ⟨a, ha⟩ = res ⟨d, hd⟩ := by
  have e1 : a = d + e * (a - d) := by linear_combination h
  have h1 : (⟨a, ha⟩ : S) = ⟨d, hd⟩ + ⟨e, he⟩ * (⟨a, ha⟩ - ⟨d, hd⟩) := Subtype.ext e1
  rw [h1, map_add, map_mul, hres, zero_mul, add_zero]

theorem smul_conj_sub_one {R : Type} [CommRing R] {m n : ℕ} (U : Matrix (Fin m) (Fin n) R) (U' : Matrix (Fin n) (Fin m) R)
    (hUU : U * U' = 1) (C : GL (Fin n) R) (X : Matrix (Fin n) (Fin n) R) (f : R) (hX : f • (X - 1) = 0) :
    f • (U * ((C : Matrix (Fin n) (Fin n) R) * X * ((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) * U' - 1) = 0 := by
  have hC : (C : Matrix (Fin n) (Fin n) R) * ((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := C.mul_inv
  rw [conj_sub_one U U' hUU _ _ X hC]
  have e2 : f • (U * ((C : Matrix (Fin n) (Fin n) R) * (X - 1) * ((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) * U') =
      U * ((C : Matrix (Fin n) (Fin n) R) * (f • (X - 1)) * ((C⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) * U' := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [e2, hX]
  simp

theorem smul_conj_sub_one' {R : Type} [CommRing R] {m : ℕ} (Bi B M : Matrix (Fin m) (Fin m) R) (hBiB : Bi * B = 1)
    (f : R) (h : f • (M - 1) = 0) : f • (Bi * M * B - 1) = 0 := by
  have : Bi * M * B - 1 = Bi * (M - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBiB]
  have e2 : f • (Bi * (M - 1) * B) = Bi * (f • (M - 1)) * B := by simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [this, e2, h]
  simp

theorem frame_algebra {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (U : Matrix (Fin m) (Fin n) R)
    (U' : Matrix (Fin n) (Fin m) R) (hUU : U * U' = 1) (hU'U : U' * U = 1) (β : GL (Fin m) R) :
    ∃ (Z P : Matrix (Fin m) (Fin n) R) (Z' P' : Matrix (Fin n) (Fin m) R), Z * Z' = 1 ∧ Z' * Z = 1 ∧ P * P' = 1 ∧
      P' * P = 1 ∧ Z = ((β⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * U ∧ Z' = U' * (β : Matrix (Fin m) (Fin m) R) ∧
      ∀ (X : Matrix (Fin n) (Fin n) R) (i j : Fin m), (P * X * P') i j = X (Fin.cast h i) (Fin.cast h j) := by
  refine ⟨_, Matrix.of fun (i : Fin m) (j : Fin n) => if (i : ℕ) = (j : ℕ) then (1 : R) else 0, _,
    Matrix.of fun (i : Fin n) (j : Fin m) => if (i : ℕ) = (j : ℕ) then (1 : R) else 0, ?_, ?_, castMatrix_mul_castMatrix h,
    castMatrix_mul_castMatrix h.symm, rfl, rfl, castMatrix_mul_mul_castMatrix_apply h⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU, Matrix.one_mul, β.inv_mul]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β : Matrix (Fin m) (Fin m) R), β.mul_inv, Matrix.one_mul, hU'U]

theorem assoc_five {R : Type} [CommRing R] {m n : ℕ} (Bi B : Matrix (Fin m) (Fin m) R) (U : Matrix (Fin m) (Fin n) R)
    (U' : Matrix (Fin n) (Fin m) R) (X : Matrix (Fin n) (Fin n) R) :
    Bi * (U * X * U') * B = (Bi * U) * X * (U' * B) := by
  simp only [Matrix.mul_assoc]

theorem res_one_apply {R k : Type} [CommRing R] [CommRing k] (S : Subring R) (res : S →+* k) {m r p : ℕ} [Fact (1 < p)]
    (a b : Fin m) (hd : (1 : Matrix (Fin m) (Fin m) R) a b ∈ S) (i j : Fin r) (hab : a = b ↔ i = j) :
    res ⟨(1 : Matrix (Fin m) (Fin m) R) a b, hd⟩ = ((((1 : Matrix (Fin r) (Fin r) (ZMod p)) i j).val : ℕ) : k) := by
  by_cases hij : i = j
  · have hab' : a = b := hab.2 hij
    have : (⟨(1 : Matrix (Fin m) (Fin m) R) a b, hd⟩ : S) = 1 := Subtype.ext (by show (1 : Matrix (Fin m) (Fin m) R) a b = (1 : R); rw [hab', Matrix.one_apply_eq])
    rw [this, map_one, hij, Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one]
  · have hab' : a ≠ b := fun e => hij (hab.1 e)
    have : (⟨(1 : Matrix (Fin m) (Fin m) R) a b, hd⟩ : S) = 0 := Subtype.ext (by show (1 : Matrix (Fin m) (Fin m) R) a b = (0 : R); exact Matrix.one_apply_ne hab')
    rw [this, map_zero, Matrix.one_apply_ne hij, ZMod.val_zero, Nat.cast_zero]

local notation "INST" D => Formalism.L2.SG.InstExistsPf.instOf D

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem core0 (D : D7) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hStd : StdPsi hF PY)
    (hn : (Formalism.L2.SG.InstExistsPf.instOf D).n = D.R.r)
    (huniq : ∀ s s' : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = s'.w → s = s') :
    ∃ (c : GAf D.host.E D.R.r) (fr : ∀ (k : Fin 2) (v : D.nd.PlG k),
        GlobalTheory.RowLev.PlFrame (Formalism.L2.SG.InstExistsPf.instOf D) D.R.r (D.host.g k) (D.naut.plGw k v)),
      ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
        ∀ (x : GAf D.host.E D.R.r) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), IsLift s x γ →
          (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ∧
          (fr kv.1 kv.2).ActsAs (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2
            (γ : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) ∧
          ∀ kv' : Σ k : Fin 2, D.nd.PlG k, kv' ≠ kv →
            (fr kv'.1 kv'.2).ActsAs (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 1 := by
  classical
  obtain ⟨β₀, hβ₀⟩ := Formalism.L2.DIV.frame_exists_alt (INST D).F (INST D).E (INST D).n (INST D).L ⟨(INST D).L_fg, (INST D).L_span⟩
  obtain ⟨U, U', hUU, hUU', hFM⟩ := GlobalTheory.T.exists_rectangular_conj_instanceMatrix_standardPsi D hF PY t hStd
  have hsp := fun kv : Σ k : Fin 2, D.nd.PlG k => GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D kv
  choose sp hsp using hsp
  have hid := fun kv : Σ k : Fin 2, D.nd.PlG k => GlobalTheory.T.exists_integralIdempotent_splitPlace_cmFiniteAdeles D.host.E (sp kv)
  choose ε₀ hε₀ using hid
  let σ : Formalism.IndefR.Lev.EAf D →+* Formalism.IndefR.Lev.EAf D := Formalism.L2.SG.HidaSetting.sigA (INST D)
  let θ : ReciprocityTheory.Aut.AL D.host.E ≃+* Formalism.IndefR.Lev.EAf D := adeleEquiv D hF
  have hθσ : ∀ a, θ (conjAL D.host.E a) = σ (θ a) := fun a => GlobalTheory.ConjFrame.swapAE_conjAL hF a
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    obtain ⟨b, rfl⟩ := θ.surjective a
    rw [← hθσ, ← hθσ, conjAL_conjAL]
  have hdist : ∀ kv kv' : Σ k : Fin 2, D.nd.PlG k, kv ≠ kv' → (sp kv).v ≠ (sp kv').v := fun kv kv' hne =>
    GlobalTheory.T.splitPlace_base_ne_of_distinct_type_primes D (sp kv) (sp kv') kv kv' (hsp kv) (hsp kv') hne
  have horth0 : ∀ kv kv' : Σ k : Fin 2, D.nd.PlG k, kv ≠ kv' →
      ε₀ kv * ε₀ kv' = 0 ∧ ε₀ kv * conjAL D.host.E (ε₀ kv') = 0 := by
    intro kv kv' hne
    constructor <;>
    · apply GlobalTheory.T.finiteAdelesCmField_eq_zero_of_components
      intro v
      rw [map_mul]
      by_cases hv : v = (sp kv).v
      · subst hv
        have := (hε₀ kv').2.2.2.2.2 (sp kv).v (hdist kv kv' hne)
        simp [this.1, this.2]
      · simp [((hε₀ kv).2.2.2.2.2 v hv).1]
  let ε : (Σ k : Fin 2, D.nd.PlG k) → Formalism.IndefR.Lev.EAf D := fun kv => θ (ε₀ kv)
  have hεidem : ∀ kv, ε kv * ε kv = ε kv := fun kv => by
    simp only [ε]; rw [← map_mul, (hε₀ kv).1]
  have hεσ : ∀ kv, ε kv * σ (ε kv) = 0 := fun kv => by
    simp only [ε]; rw [← hθσ, ← map_mul, (hε₀ kv).2.1, map_zero]
  have hεorth : ∀ kv kv', kv ≠ kv' → ε kv * ε kv' = 0 ∧ ε kv * σ (ε kv') = 0 := by
    intro kv kv' hne
    simp only [ε]
    rw [← hθσ, ← map_mul, ← map_mul, (horth0 kv kv' hne).1, (horth0 kv kv' hne).2, map_zero]
    exact ⟨rfl, rfl⟩
  obtain ⟨Z, P, Z', P', hZZ', hZ'Z, hPP', hP'P, hZ, hZ', hPXP⟩ :=
    frame_algebra (R := Formalism.IndefR.Lev.EAf D) hn U U' hUU hUU' β₀
  obtain ⟨cE, hcE, hcZ⟩ := GlobalTheory.T.exists_unitary_conjugator_of_split_idempotents (Formalism.IndefR.Lev.EAf D) σ hσσ (INST D).n D.R.r
    (Σ k : Fin 2, D.nd.PlG k) ε hεidem hεσ hεorth Z P Z' P' hZZ' hZ'Z hPP' hP'P
  obtain ⟨cA, hcA1, hcA2, hcA3⟩ := exists_unitary_transport θ (conjAL D.host.E) σ hθσ D.R.r cE hcE
  let c : GAf D.host.E D.R.r := ⟨cA, hcA1⟩
  have hfr := fun kv : Σ k : Fin 2, D.nd.PlG k => GlobalTheory.T.exists_degreeOne_prime_frame_reduced_matrices (INST D) β₀ hβ₀ D.R.r (D.host.g kv.1) hn
    (D.naut.plGw kv.1 kv.2) (D.host.g_prime kv.1) (Formalism.L2.SG.Pf.RowDictPf.card_res_host kv.1 kv.2)
  choose fr hfr using hfr
  refine ⟨c, fun k v => fr ⟨k, v⟩, ?_⟩
  intro kv s hs x γ hlift
  obtain rfl : s = sp kv := huniq _ _ (hs.trans (hsp kv).symm)
  have hεint : ε kv ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles D hF _ (hε₀ kv).2.2.1
  have hgw : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (sp kv).w.asIdeal := by
    rw [hsp kv]; exact D.naut.plGw_over kv.1 kv.2
  have hxU : x ∈ Umax D.host.E D.R.r :=
    GlobalTheory.T.mem_maximalCompactUnitary_of_splitPlaceLift D.host.E D.R.r (sp kv) (D.host.g kv.1) (D.host.g_prime kv.1) hgw x γ hlift
  have hKof : ∀ z : GAf D.host.E D.R.r,
      (INST D).fmat (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * z * c⁻¹)))).2 =
        U * ((cE : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) *
          ((z : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)).map θ *
          ((cE⁻¹ : GL (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D))) * U' := by
    intro z
    rw [hFM]
    congr 2
    show ((cA : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)) * ((z : GL (Fin D.R.r) (AL D.host.E)) : Matrix _ _ _) *
      ((cA⁻¹ : GL (Fin D.R.r) (AL D.host.E)) : Matrix _ _ _)).map θ = _
    rw [Matrix.map_mul, Matrix.map_mul, hcA2, hcA3]
  have hAeq : ∀ z : GAf D.host.E D.R.r,
      (((β₀⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * z * c⁻¹)))).2 :
        GL (Fin (INST D).n) ((INST D).E ⊗[(INST D).F] Formalism.MainNotions.S.Af (INST D).F)) * β₀ :
          GL (Fin (INST D).n) ((INST D).E ⊗[(INST D).F] Formalism.MainNotions.S.Af (INST D).F)).val :
            Matrix (Fin (INST D).n) (Fin (INST D).n) (Formalism.IndefR.Lev.EAf D))) =
        Z * ((cE : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) *
          ((z : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)).map θ *
          ((cE⁻¹ : GL (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D))) * Z' := by
    intro z
    rw [hZ, hZ']
    show ((β₀⁻¹).val : Matrix (Fin (INST D).n) (Fin (INST D).n) (Formalism.IndefR.Lev.EAf D)) *
      (INST D).fmat (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * z * c⁻¹)))).2 * (β₀.val : Matrix (Fin (INST D).n) (Fin (INST D).n) (Formalism.IndefR.Lev.EAf D)) = _
    rw [hKof z]
    exact assoc_five _ _ _ _ _
  have hpart : ∀ z : GAf D.host.E D.R.r, ∀ a b : Fin (INST D).n,
      ε kv * (@id (Formalism.IndefR.Lev.EAf D) ((β₀⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * z * c⁻¹)))).2 :
        GL (Fin (INST D).n) ((INST D).E ⊗[(INST D).F] Formalism.MainNotions.S.Af (INST D).F)) * β₀ :
          GL (Fin (INST D).n) ((INST D).E ⊗[(INST D).F] Formalism.MainNotions.S.Af (INST D).F)).val a b)) =
        ε kv * θ (((z : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E))
          (Fin.cast hn a) (Fin.cast hn b)) := by
    intro z a b
    have h1 := congrFun (congrFun (part_eq (ε kv) (hεidem kv) Z P Z' P' cE (hcZ kv).1 (hcZ kv).2
      (((z : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)).map θ)) a) b
    rw [← hAeq z] at h1
    simp only [Matrix.smul_apply, smul_eq_mul] at h1
    rw [hPXP] at h1
    exact h1
  have hx1 : ∀ i j, (1 - (ε₀ kv + conjAL D.host.E (ε₀ kv))) *
      (((x : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)) i j -
        (1 : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)) i j) = 0 := by
    intro i j
    apply GlobalTheory.T.finiteAdelesCmField_eq_zero_of_components
    intro v
    rw [map_mul, map_sub, map_sub, map_one]
    by_cases hv : v = (sp kv).v
    · subst hv; rw [(hε₀ kv).2.2.2.2.1, sub_self, zero_mul]
    · have h1 := congrFun (congrFun (hlift.1 v (by simpa using hv)) i) j
      simp only [Matrix.map_apply] at h1
      rw [h1]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  obtain ⟨f, hfdef⟩ : ∃ f : Formalism.IndefR.Lev.EAf D, f = θ (1 - (ε₀ kv + conjAL D.host.E (ε₀ kv))) := ⟨_, rfl⟩
  have hf : f = 1 - ε kv - σ (ε kv) := by
    rw [hfdef, map_sub, map_add, map_one, hθσ]; ring
  have hfx : f • ((((x : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)).map θ) - 1) = 0 := by
    ext i j
    have h1 : f * θ (((x : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)) i j -
        (1 : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)) i j) = 0 := by
      rw [hfdef, ← map_mul, hx1 i j, map_zero]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← h1, map_sub]
    congr 2
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  obtain ⟨MK, hMK⟩ : ∃ MK : Matrix (Fin (INST D).n) (Fin (INST D).n) (Formalism.IndefR.Lev.EAf D),
      MK = (INST D).fmat (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 := ⟨_, rfl⟩
  have hfK : f • (MK - 1) = 0 := by
    rw [hMK, hKof x]
    exact smul_conj_sub_one U U' hUU cE _ f hfx
  have hKinv : ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2)⁻¹ =
      (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * x⁻¹ * c⁻¹)))).2 := by
    have e1 : PY.ψ (c * x⁻¹ * c⁻¹) = (PY.ψ (c * x * c⁻¹))⁻¹ := by
      rw [← map_inv]; congr 1; group
    have h2 : ∀ g : Formalism.L2.Theta.GA D (D.sp.Y 0),
        (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t g⁻¹)).2 = ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t g)).2)⁻¹ := by
      intro g; rw [map_inv, map_inv, Prod.snd_inv]
    rw [e1]
    exact (h2 _).symm
  have hcc : ∀ i : Fin D.R.r, Fin.cast hn (Fin.cast hn.symm i) = i := fun i => Fin.ext rfl
  have hK : (Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 ∈ (INST D).Kset := by
    refine GlobalTheory.T.mem_maximalCompact_of_trivial_off_splitPair (INST D) β₀ hβ₀ (ε kv) (hεidem kv) (hεσ kv) hεint _ (fun i j => ?_) (fun i j => ?_) (fun i j => ?_)
    · have h1 := congrFun (congrFun hfK i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h1
      rw [hf, hMK] at h1
      exact h1
    · have h2 : ε kv * θ (((x : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E))
          (Fin.cast hn i) (Fin.cast hn j)) ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E :=
        mul_mem hεint (GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles D hF _ (hxU _ _))
      rw [← hpart x i j] at h2
      exact h2
    · rw [hKinv]
      have h2 : ε kv * θ ((((x⁻¹ : GAf D.host.E D.R.r) : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E))
          (Fin.cast hn i) (Fin.cast hn j)) ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E :=
        mul_mem hεint (GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles D hF _ (inv_mem hxU _ _))
      rw [← hpart x⁻¹ i j] at h2
      exact h2
  refine ⟨hK, ?_, ?_⟩
  · apply (hfr kv) _ hK
    intro i j hij
    rw [← hsp kv]
    have hres1 : Formalism.L2.DIV.resS (↥D.host.F) (sp kv).w ⟨ε kv, hεint⟩ = 1 := by
      have h1 := GlobalTheory.T.residue_cmFieldFiniteAdeleTensorEquiv_eq_natCast D hF (sp kv) (ε₀ kv) hεint 1 (hε₀ kv).2.2.1
        (by rw [(hε₀ kv).2.2.2.1, Nat.cast_one, sub_self, map_zero]; exact zero_lt_one)
      rw [Nat.cast_one] at h1
      exact h1
    have hxθ : θ (((x : GL (Fin D.R.r) (AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (AL D.host.E)) i j) ∈
        Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles D hF _ (hxU i j)
    have h3 := hpart x (Fin.cast hn.symm i) (Fin.cast hn.symm j)
    rw [hcc, hcc] at h3
    exact (res_eq_of_part _ _ (ε kv) hεint hres1 _ _ hij hxθ h3).trans
      (GlobalTheory.T.residue_cmFieldFiniteAdeleTensorEquiv_eq_natCast D hF (sp kv) _ hxθ ((γ : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j).val
        (hxU i j) (hlift.2 i j))
  · intro kv' hne
    apply (hfr kv') _ hK
    intro i j hij
    rw [← hsp kv']
    have hemem : ε₀ kv + conjAL D.host.E (ε₀ kv) ∈ ALint D.host.E :=
      add_mem (hε₀ kv).2.2.1 (conjAL_mem_ALint D.host.E (hε₀ kv).2.2.1)
    have he : θ (ε₀ kv + conjAL D.host.E (ε₀ kv)) ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles D hF _ hemem
    have hcomp : compAt D.host.E (sp kv').v (ε₀ kv + conjAL D.host.E (ε₀ kv)) = 0 := by
      have := (hε₀ kv).2.2.2.2.2 (sp kv').v (hdist kv' kv hne)
      rw [map_add, this.1, this.2, add_zero]
    have hres0 : Formalism.L2.DIV.resS (↥D.host.F) (sp kv').w ⟨_, he⟩ = 0 := by
      have h1 := GlobalTheory.T.residue_cmFieldFiniteAdeleTensorEquiv_eq_natCast D hF (sp kv') (ε₀ kv + conjAL D.host.E (ε₀ kv)) he 0 hemem
        (by rw [GlobalTheory.T.splitPlaceProjection_eq_zero_of_placeComponent_eq_zero D.host.E (sp kv') _ hcomp, Nat.cast_zero, sub_zero, map_zero]; exact zero_lt_one)
      rw [Nat.cast_zero] at h1
      exact h1
    have h3 := smul_conj_sub_one' ((β₀⁻¹ : GL _ _).val : Matrix (Fin (INST D).n) (Fin (INST D).n) (Formalism.IndefR.Lev.EAf D))
      (β₀.val : Matrix (Fin (INST D).n) (Fin (INST D).n) (Formalism.IndefR.Lev.EAf D)) MK β₀.inv_mul f hfK
    have h4 := congrFun (congrFun h3 (Fin.cast hn.symm i)) (Fin.cast hn.symm j)
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.zero_apply] at h4
    have hfe : f = 1 - θ (ε₀ kv + conjAL D.host.E (ε₀ kv)) := by rw [hfdef, map_sub, map_one]
    rw [hfe, hMK] at h4
    have hd : (1 : Matrix (Fin (INST D).n) (Fin (INST D).n) (Formalism.IndefR.Lev.EAf D)) (Fin.cast hn.symm i) (Fin.cast hn.symm j) ∈
        Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
      by_cases hij' : Fin.cast hn.symm i = Fin.cast hn.symm j
      · rw [hij', Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne hij']; exact zero_mem _
    refine (res_eq_of_off _ _ _ he hres0 _ _ hij hd h4).trans ?_
    haveI : Fact (1 < D.host.g kv'.1) := ⟨(D.host.g_prime kv'.1).one_lt⟩
    exact res_one_apply _ _ _ _ hd i j (Fin.cast_injective hn.symm).eq_iff

theorem core (D : D7) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hpin : ∀ x, HEq (ιE x) x) (hn : I.n = D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hStd : StdPsi hF PY)
    (huniq : ∀ s s' : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = s'.w → s = s') :
    ∃ (c : GAf D.host.E D.R.r) (fr : ∀ (k : Fin 2) (v : D.nd.PlG k),
        GlobalTheory.RowLev.PlFrame I D.R.r (D.host.g k) (primeComap ιE (D.naut.plGw k v))),
      ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
        ∀ (x : GAf D.host.E D.R.r) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), IsLift s x γ →
          (((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)) (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 ∈ I.Kset ∧
          (fr kv.1 kv.2).ActsAs (((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)) (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2
            (γ : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) ∧
          ∀ kv' : Σ k : Fin 2, D.nd.PlG k, kv' ≠ kv →
            (fr kv'.1 kv'.2).ActsAs (((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)) (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 1 := by
  subst h
  have hid : ∀ x, ιE x = x := fun x => eq_of_heq (hpin x)
  have hw : ∀ w, primeComap ιE w = w := fun w => by
    ext a
    show RingOfIntegers.mapRingEquiv ιE a ∈ w.asIdeal ↔ a ∈ w.asIdeal
    have : RingOfIntegers.mapRingEquiv ιE a = a := RingOfIntegers.ext (by simp [hid] <;> rfl)
    rw [this]
    exact Iff.rfl
  obtain ⟨c, fr, H⟩ := core0 D t PY hF hStd hn huniq
  refine ⟨c, fun k v => ((hw (D.naut.plGw k v)).symm ▸ fr k v :
    GlobalTheory.RowLev.PlFrame (Formalism.L2.SG.InstExistsPf.instOf D) D.R.r (D.host.g k) (primeComap ιE (D.naut.plGw k v))), ?_⟩
  intro kv s hs x γ hl
  obtain ⟨h1, h2, h3⟩ := H kv s hs x γ hl
  exact ⟨h1, (actsAs_congr _ _ _ _).mpr h2, fun kv' hne => (actsAs_congr _ _ _ _).mpr (h3 kv' hne)⟩

theorem exists_conj_frames : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ s s' : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = s'.w → s = s') → ∃ (c : GAf D.host.E D.R.r) (fr : ∀ (k : Fin 2) (v : D.nd.PlG k), GlobalTheory.RowLev.PlFrame X.B.I D.R.r (D.host.g k) (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v))), ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 → ∀ (x : GAf D.host.E D.R.r) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), IsLift s x γ → (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 ∈ X.B.I.Kset ∧ (fr kv.1 kv.2).ActsAs (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 (γ : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) ∧ ∀ kv' : Σ k : Fin 2, D.nd.PlG k, kv' ≠ kv → (fr kv'.1 kv'.2).ActsAs (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 1 := by
  intro D X h t PY hF hStd hpin huniq
  exact core D X.B.I h X.ιE hpin X.n_eq t PY hF hStd huniq

end GlobalTheory.FixedConj

end
