import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoverTensorHom

noncomputable section

namespace GlobalTheory

open Formalism.BasicNotions.TH MvPolynomial GlobalTheory.FockAlg
open scoped Matrix

namespace Oscillator

variable {P Q : ℕ}

abbrev OscPol (P Q : ℕ) : Type := MvPolynomial (Ix P Q) ℂ

def sgn : Ix P Q → ℤ
  | .inl _ => 1
  | .inr _ => -1

def low (l : Ix P Q) : Module.End ℂ (OscPol P Q) :=
  if l.isLeft then (pderiv l).toLinearMap else LinearMap.mulLeft ℂ (X l)

def rai (l : Ix P Q) : Module.End ℂ (OscPol P Q) :=
  if l.isLeft then LinearMap.mulLeft ℂ (X l) else -(pderiv l).toLinearMap

def unitOp (l l' : Ix P Q) : Module.End ℂ (OscPol P Q) :=
  rai l * low l' + if l = l' then (1 / 2 : ℂ) • 1 else 0

def oscAct (P Q : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (OscPol P Q) :=
  ∑ l, ∑ l', (Matrix.entryLinearMap ℂ ℂ l l').smulRight (unitOp l l')

theorem oscAct_apply (Z : Mat P Q) : oscAct P Q Z = ∑ l, ∑ l', Z l l' • unitOp l l' := by
  simp [oscAct, LinearMap.sum_apply]

theorem oscAct_single (a b : Ix P Q) (c : ℂ) : oscAct P Q (Matrix.single a b c) = c • unitOp a b := by
  simp [oscAct_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_smul]

theorem oscAct_Eab (a b : Ix P Q) : oscAct P Q (Eab a b) = unitOp a b := by
  rw [Eab, oscAct_single, one_smul]

theorem unitOp_inl_inl (i j : Fin P) (f : OscPol P Q) :
    unitOp (.inl i) (.inl j) f = X (.inl i) * pderiv (.inl j) f + if i = j then (1 / 2 : ℂ) • f else 0 := by
  by_cases h : i = j <;> simp [unitOp, rai, low, h]

theorem unitOp_inl_inr (i : Fin P) (j : Fin Q) (f : OscPol P Q) :
    unitOp (.inl i) (.inr j) f = X (.inl i) * (X (.inr j) * f) := by
  simp [unitOp, rai, low]

theorem unitOp_inr_inl (i : Fin Q) (j : Fin P) (f : OscPol P Q) :
    unitOp (.inr i) (.inl j) f = -pderiv (.inr i) (pderiv (.inl j) f) := by
  simp [unitOp, rai, low]

theorem unitOp_inr_inr (i j : Fin Q) (f : OscPol P Q) :
    unitOp (.inr i) (.inr j) f = -(X (.inr j) * pderiv (.inr i) f) - if i = j then (1 / 2 : ℂ) • f else 0 := by
  by_cases h : i = j
  · subst h
    simp only [unitOp, rai, low, Sum.isLeft_inr, Bool.false_eq_true, if_false, if_true]
    change -(pderiv (.inr i) ((X (.inr i) : OscPol P Q) * f)) + (1 / 2 : ℂ) • f = _
    rw [Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one]
    module
  · simp [unitOp, rai, low, h, Ne.symm h]

theorem unitOp_diag (l : Ix P Q) (α : Ix P Q →₀ ℕ) :
    unitOp l l (monomial α 1) = ((sgn l : ℂ) * (((α l : ℕ) : ℂ) + 1 / 2)) • monomial α 1 := by
  rcases l with i | i
  · rw [unitOp_inl_inl, Formalism.BasicNotions.TH.X_mul_pderiv_monomial]; simp [sgn, add_smul]
  · rw [unitOp_inr_inr, Formalism.BasicNotions.TH.X_mul_pderiv_monomial]; simp [sgn, add_smul, sub_eq_add_neg, add_comm]

theorem pderiv_pderiv_comm (a b : Ix P Q) (f : OscPol P Q) : pderiv a (pderiv b f) = pderiv b (pderiv a f) := by
  have h : ⁅(pderiv a : Derivation ℂ (OscPol P Q) (OscPol P Q)), (pderiv b : Derivation ℂ (OscPol P Q) (OscPol P Q))⁆ = 0 :=
    derivation_ext fun i => by
      rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
      simp [Pi.single_apply, apply_ite]
  have := congrArg (fun D : Derivation ℂ (OscPol P Q) (OscPol P Q) => D f) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem low_mul_low (a b : Ix P Q) : low a * low b = low b * low a := by
  refine LinearMap.ext fun f => ?_
  rcases a with a | a <;> rcases b with b | b <;> simp [low, pderiv_pderiv_comm, mul_left_comm]

theorem rai_mul_rai (a b : Ix P Q) : rai a * rai b = rai b * rai a := by
  refine LinearMap.ext fun f => ?_
  rcases a with a | a <;> rcases b with b | b <;> simp [rai, pderiv_pderiv_comm, mul_left_comm]

theorem low_mul_rai (a b : Ix P Q) : low a * rai b = rai b * low a + if a = b then 1 else 0 := by
  refine LinearMap.ext fun f => ?_
  by_cases h : a = b
  · subst h
    rcases a with a | a <;> simp [low, rai]
  · rcases a with a | a <;> rcases b with b | b <;>
      simp_all [low, rai, pderiv_pderiv_comm, mul_left_comm, Ne.symm h, eq_comm]

theorem unitOp_comm (i j k l : Ix P Q) :
    unitOp i j * unitOp k l - unitOp k l * unitOp i j =
      (if j = k then unitOp i l else 0) - if l = i then unitOp k j else 0 := by
  have h1 : rai i * low j * (rai k * low l) = rai i * rai k * (low j * low l) + if j = k then rai i * low l else 0 := by
    rw [mul_assoc, ← mul_assoc (low j), low_mul_rai]
    split_ifs <;> noncomm_ring
  have h2 : rai k * low l * (rai i * low j) = rai i * rai k * (low j * low l) + if l = i then rai k * low j else 0 := by
    rw [mul_assoc, ← mul_assoc (low l), low_mul_rai, rai_mul_rai i k, low_mul_low j l]
    split_ifs <;> noncomm_ring
  have h3 : ∀ a b : Ix P Q, unitOp a b = rai a * low b + (if a = b then (1 / 2 : ℂ) else 0) • 1 := fun a b => by
    rw [unitOp]; split_ifs <;> simp
  have h4 : unitOp i j * unitOp k l - unitOp k l * unitOp i j =
      rai i * low j * (rai k * low l) - rai k * low l * (rai i * low j) := by
    simp only [h3, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [h4, h1, h2, add_sub_add_left_eq_sub, unitOp, unitOp]
  by_cases hjk : j = k <;> by_cases hli : l = i
  · subst hjk hli; simp
  · simp [hjk, hli, Ne.symm hli]
  · simp [hjk, hli, Ne.symm hjk]
  · simp [hjk, hli]

theorem isLieAct_oscAct (P Q : ℕ) : IsLieAct (oscAct P Q) := by
  intro X Y
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add X X' h h' =>
    rw [add_mul, mul_add, add_sub_add_comm, map_add, h, h', map_add]; noncomm_ring
  | h_std_basis i j c =>
    induction Y using Matrix.induction_on' with
    | h_zero => simp
    | h_add Y Y' h h' =>
      rw [add_mul, mul_add, add_sub_add_comm, map_add, h, h', map_add]; noncomm_ring
    | h_std_basis k l d =>
      rw [oscAct_single, oscAct_single, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm d c, ← smul_sub,
        unitOp_comm, map_sub, smul_sub]
      congr 1
      · split_ifs with h
        · subst h; rw [Matrix.single_mul_single_same, oscAct_single]
        · rw [Matrix.single_mul_single_of_ne (h := h), map_zero, smul_zero]
      · split_ifs with h
        · subst h; rw [Matrix.single_mul_single_same, oscAct_single, mul_comm]
        · rw [Matrix.single_mul_single_of_ne (h := h), map_zero, smul_zero]

section Adjoint

variable {σ H : Type} [DecidableEq σ] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

omit [DecidableEq σ] in

theorem mfact_add_single (α : σ →₀ ℕ) (l : σ) :
    FockSeq.mfact (α + Finsupp.single l 1) = (α l + 1) * FockSeq.mfact α := by
  classical
  have key : ∀ β : σ →₀ ℕ, FockSeq.mfact β = (β l).factorial * FockSeq.mfact (β.erase l) := fun β =>
    (Finsupp.mul_prod_erase' β l (fun _ k => k.factorial) fun _ => rfl).symm
  rw [key (α + _), key α, Finsupp.erase_add, Finsupp.erase_single, add_zero]
  simp [Nat.factorial_succ, mul_assoc]

theorem inner_X_mul (h : IsFockIP ι) (l : σ) (f g : MvPolynomial σ ℂ) :
    inner ℂ (ι (X l * f)) (ι g) = inner ℂ (ι f) (ι (pderiv l g)) := by
  induction f using MvPolynomial.induction_on' with
  | add f f' hf hf' => simp only [mul_add, map_add, inner_add_left, hf, hf']
  | monomial α a =>
    induction g using MvPolynomial.induction_on' with
    | add g g' hg hg' => simp only [map_add, inner_add_right, hg, hg']
    | monomial β b =>
      have e : ∀ (γ : σ →₀ ℕ) (c : ℂ), (monomial γ c : MvPolynomial σ ℂ) = c • monomial γ 1 := fun γ c => by
        simp [smul_monomial]
      rw [X, monomial_mul, pderiv_monomial, e _ (1 * a), e α a, e β b, e _ (b * _)]
      simp only [map_smul, inner_smul_left, inner_smul_right, h _ _, ← FockSeq.mfact_cast]
      by_cases hβ : Finsupp.single l 1 + α = β
      · subst hβ
        rw [if_pos rfl, if_pos (by simp), add_comm, mfact_add_single]
        simp; ring
      · rw [if_neg hβ]
        by_cases h0 : β l = 0
        · simp [h0]
        · rw [if_neg]
          · simp
          · rintro rfl
            apply hβ
            rw [add_comm, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero h0))]

theorem inner_pderiv (h : IsFockIP ι) (l : σ) (f g : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv l f)) (ι g) = inner ℂ (ι f) (ι (X l * g)) := by
  rw [← inner_conj_symm, ← inner_X_mul h, inner_conj_symm]

end Adjoint

section AdjointAct

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : OscPol P Q →ₗ[ℂ] H}

theorem inner_rai (h : IsFockIP ι) (l : Ix P Q) (f g : OscPol P Q) :
    inner ℂ (ι (rai l f)) (ι g) = (sgn l : ℂ) * inner ℂ (ι f) (ι (low l g)) := by
  rcases l with i | i <;> simp [rai, low, sgn, inner_X_mul h, inner_pderiv h]

theorem inner_low (h : IsFockIP ι) (l : Ix P Q) (f g : OscPol P Q) :
    inner ℂ (ι (low l f)) (ι g) = (sgn l : ℂ) * inner ℂ (ι f) (ι (rai l g)) := by
  rcases l with i | i <;> simp [rai, low, sgn, inner_X_mul h, inner_pderiv h]

theorem inner_unitOp (h : IsFockIP ι) (a b : Ix P Q) (f g : OscPol P Q) :
    inner ℂ (ι (unitOp a b f)) (ι g) = (sgn a : ℂ) * (sgn b : ℂ) * inner ℂ (ι f) (ι (unitOp b a g)) := by
  simp only [unitOp, LinearMap.add_apply, Module.End.mul_apply, map_add, inner_add_left, inner_add_right,
    inner_rai h, inner_low h, mul_add, mul_assoc]
  congr 1
  by_cases hab : a = b
  · subst hab
    rcases a with i | i <;> simp [sgn, inner_smul_left, inner_smul_right, map_ofNat]
  · simp [hab, Ne.symm hab]

theorem adjZ_apply (Z : Mat P Q) (a b : Ix P Q) :
    adjZ Z a b = (sgn a : ℂ) * (sgn b : ℂ) * (starRingEnd ℂ) (Z b a) := by
  rw [adjZ, Jm, FockEmb.Jpq_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn]

theorem inner_oscAct (h : IsFockIP ι) (Z : Mat P Q) (f g : OscPol P Q) :
    inner ℂ (ι (oscAct P Q Z f)) (ι g) = inner ℂ (ι f) (ι (oscAct P Q (adjZ Z) g)) := by
  simp only [oscAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, inner_unitOp h, adjZ_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end AdjointAct

section Lines

variable {p q r s : ℕ}

def renum (p q r s : ℕ) : Pol p q r s ≃ₐ[ℂ] OscPol (p * r + q * s) (p * s + q * r) :=
  renameEquiv ℂ (lineEquiv p q r s)

theorem renum_lowB (l : Ln p q r s) (f : Pol p q r s) :
    renum p q r s (lowB l f) = low (lineEquiv p q r s l) (renum p q r s f) := by
  simp only [lowB, low, lineEquiv_isLeft, renum]
  split_ifs <;> simp [pderiv_rename (lineEquiv p q r s).injective]

theorem renum_raiB (l : Ln p q r s) (f : Pol p q r s) :
    renum p q r s (raiB l f) = rai (lineEquiv p q r s l) (renum p q r s f) := by
  simp only [raiB, rai, lineEquiv_isLeft, renum]
  split_ifs <;> simp [pderiv_rename (lineEquiv p q r s).injective]

theorem renum_omE (l l' : Ln p q r s) (f : Pol p q r s) :
    renum p q r s (omE l l' f) = unitOp (lineEquiv p q r s l) (lineEquiv p q r s l') (renum p q r s f) := by
  by_cases h : l = l' <;> simp [omE, unitOp, renum_lowB, renum_raiB, h]

theorem renum_omAct (Z : Mat (p * r + q * s) (p * s + q * r)) (f : Pol p q r s) :
    renum p q r s (omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) f) =
      oscAct _ _ Z (renum p q r s f) := by
  simp only [omAct_apply, oscAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, renum_omE,
    Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  rw [← (lineEquiv p q r s).sum_comp]
  exact Finset.sum_congr rfl fun l _ => (lineEquiv p q r s).sum_comp
    fun b => Z (lineEquiv p q r s l) b • unitOp (lineEquiv p q r s l) b (renum p q r s f)

end Lines

theorem isFockIsometry_comp_renameEquiv {σ τ H : Type} [DecidableEq σ] [DecidableEq τ] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial τ ℂ →ₗ[ℂ] H} (h : IsFockIP ι) (e : σ ≃ τ) :
    IsFockIP (ι ∘ₗ (renameEquiv ℂ e).toLinearMap) := fun α β => by
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, renameEquiv_apply, rename_monomial, h _ _,
    (Finsupp.mapDomain_injective e.injective).eq_iff]
  rw [Finsupp.prod_mapDomain_index_inj e.injective]

end Oscillator

open Oscillator

structure Osc (P Q : ℕ) (T0 : GrpData P Q) where

  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]

  Om : T0.G →* (H →L[ℂ] H)
  isom : ∀ g x, ‖Om g x‖ = ‖x‖
  cont : ∀ x, Continuous fun g => Om g x

  ι : OscPol P Q →ₗ[ℂ] H
  ι_inj : Function.Injective ι
  dense : Dense (Set.range ι)

  fockIP : ∀ α β, inner ℂ (ι (monomial α 1)) (ι (monomial β 1)) =
    if α = β then α.prod (fun _ k => (k.factorial : ℂ)) else 0

  der : ∀ Z ∈ upq P Q, ∀ f,
    HasDerivAt (fun t : ℝ => Om (T0.expt (t • Z)) (ι f)) (ι (oscAct P Q Z f)) 0

attribute [instance] Osc.nacg Osc.ips Osc.cs

namespace Osc

variable {P Q : ℕ} {T0 : GrpData P Q}

def toURep (O : Osc P Q T0) : URep T0 where
  H := O.H
  π := O.Om
  isom := O.isom
  cont := O.cont

theorem isFockIP (O : Osc P Q T0) : IsFockIP O.ι := fun α β => by convert O.fockIP α β

theorem norm_vacuum (O : Osc P Q T0) : ‖O.ι 1‖ = 1 := by
  have h := O.fockIP 0 0
  rw [if_pos rfl, Finsupp.prod_zero_index, inner_self_eq_norm_sq_to_K, monomial_zero', C_1] at h
  have h2 : ‖O.ι 1‖ ^ 2 = 1 := Complex.ofReal_injective (by simpa using h)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

theorem inner_oscAct (O : Osc P Q T0) (Z : Mat P Q) (f g : OscPol P Q) :
    inner ℂ (O.ι (oscAct P Q Z f)) (O.ι g) = inner ℂ (O.ι f) (O.ι (oscAct P Q (adjZ Z) g)) :=
  Oscillator.inner_oscAct O.isFockIP Z f g

theorem isDer (O : Osc P Q T0) {Z : Mat P Q} (hZ : Z ∈ upq P Q) (f : OscPol P Q) :
    IsDer T0 O.Om Z (O.ι f) (O.ι (oscAct P Q Z f)) := ⟨hZ, O.der Z hZ f⟩

theorem smooth (O : Osc P Q T0) (f : OscPol P Q) : Smooth T0 O.Om (O.ι f) :=
  ⟨LinearMap.range O.ι, ⟨f, rfl⟩, by
    rintro _ ⟨g, rfl⟩ Z hZ
    exact ⟨_, ⟨_, rfl⟩, O.isDer hZ g⟩⟩

section Pair

variable {p q r s : ℕ} {T : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

def ofFockData (F : FockData T T1 T2) : Osc _ _ T where
  H := F.H
  Om := F.Om
  isom := F.isom
  cont := F.cont
  ι := F.ι ∘ₗ (renum p q r s).symm.toLinearMap
  ι_inj := F.ι_inj.comp (renum p q r s).symm.injective
  dense := by
    exact F.dense.mono ((renum p q r s).symm.surjective.range_comp F.ι).ge
  fockIP α β := by
    convert isFockIsometry_comp_renameEquiv (isFockIsometry_of_fockData F) (lineEquiv p q r s).symm α β <;> rfl
  der Z hZ f := by
    obtain ⟨g, rfl⟩ := (renum p q r s).surjective f
    simpa [← renum_omAct] using F.der Z hZ g

def toFockData (O : Osc _ _ T) (emb : T1.G × T2.G →* T.G)
    (emb_cov : ∀ g h, ((T.cov (emb (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) =
      Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
        (Matrix.kroneckerMap (· * ·) ((T1.cov g : GL _ ℂ) : Mat p q) ((T2.cov h : GL _ ℂ) : Mat r s)))
    (emb_sq : ∀ g h, T.sq (emb (g, h)) = T1.sq g ^ (r + s) * T2.sq h ^ (p + q)) : FockData T T1 T2 where
  H := O.H
  Om := O.Om
  isom := O.isom
  cont := O.cont
  ι := O.ι ∘ₗ (renum p q r s).toLinearMap
  ι_inj := O.ι_inj.comp (renum p q r s).injective
  dense := by
    exact O.dense.mono ((renum p q r s).surjective.range_comp O.ι).ge
  fockIP α β := by
    convert isFockIsometry_comp_renameEquiv O.isFockIP (lineEquiv p q r s) α β <;> rfl
  der Z hZ f := by
    simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, renum_omAct] using O.der Z hZ _
  emb := emb
  emb_cov := emb_cov
  emb_sq := emb_sq

theorem nonempty_fockData_iff : Nonempty (FockData T T1 T2) ↔ Nonempty (Osc _ _ T) := by
  refine ⟨fun ⟨F⟩ => ⟨ofFockData F⟩, fun ⟨O⟩ => ?_⟩
  obtain ⟨emb, h1, h2⟩ := exists_cover_tensor_hom p q r s T T1 T2
  exact ⟨O.toFockData emb h1 h2⟩

end Pair

section RankOne

variable [Unique (Ix P Q)]

def expo (α : Ix P Q →₀ ℕ) : ℤ := sgn (default : Ix P Q) * (2 * α default + 1)

theorem oscAct_monomial_of_unique (Z : Mat P Q) (α : Ix P Q →₀ ℕ) (c : ℂ) :
    oscAct P Q Z (monomial α c) = ((expo α : ℂ) * (Z.trace / 2)) • monomial α c := by
  have e : (monomial α c : OscPol P Q) = c • monomial α 1 := by simp [smul_monomial]
  rw [e, map_smul, smul_comm, oscAct_apply, Fintype.sum_unique, Fintype.sum_unique, LinearMap.smul_apply,
    unitOp_diag, smul_smul (Z _ _), Matrix.trace, Fintype.sum_unique, expo]
  congr 2
  simp; ring

theorem norm_sq_zpow (g : T0.G) (α : Ix P Q →₀ ℕ) : ‖((T0.sq g : ℂˣ) : ℂ) ^ expo α‖ = 1 := by
  rw [norm_zpow, RealPar.Cover.norm_sq, one_zpow]

def rankOneRep (T0 : GrpData P Q) : T0.G →* (FockSeq.L2 (Ix P Q) →L[ℂ] FockSeq.L2 (Ix P Q)) where
  toFun g := FockSeq.diag (fun α => ((T0.sq g : ℂˣ) : ℂ) ^ expo α) (norm_sq_zpow g)
  map_one' := by ext x α; simp
  map_mul' g h := by ext x α; simp [mul_zpow, mul_assoc]

theorem rankOneRep_monomial (g : T0.G) (α : Ix P Q →₀ ℕ) (c : ℂ) :
    rankOneRep T0 g (FockSeq.emb _ (monomial α c)) =
      ((T0.sq g : ℂˣ) : ℂ) ^ expo α • FockSeq.emb _ (monomial α c) :=
  FockSeq.diag_emb_monomial _ (norm_sq_zpow g) α c

def rankOne (T0 : GrpData P Q) : Osc P Q T0 where
  H := FockSeq.L2 (Ix P Q)
  Om := rankOneRep T0
  isom g := FockSeq.norm_diag _ (norm_sq_zpow g)
  cont := by
    refine FockSeq.continuous_of_dense _ (fun g => FockSeq.norm_diag _ (norm_sq_zpow g)) FockSeq.dense_range_emb ?_
    rintro _ ⟨f, rfl⟩
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg => simpa only [map_add] using hf.fun_add hg
    | monomial α c =>
      simp only [rankOneRep_monomial]
      exact (RealPar.Cover.continuous_sq.zpow₀ _ fun g => .inl (T0.sq g).ne_zero).smul continuous_const
  ι := FockSeq.emb _
  ι_inj := FockSeq.emb_injective
  dense := FockSeq.dense_range_emb
  fockIP α β := by convert FockSeq.isFockIsometry_embedding α β
  der Z hZ f := by
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg =>
      simp only [map_add]
      exact @HasDerivAt.fun_add ℝ _ _ _ NormedSpace.complexToReal _ _ _ _ _ hf hg
    | monomial α c =>
      simp only [rankOneRep_monomial, oscAct_monomial_of_unique, map_smul]
      have h1 := RealPar.Cover.hasDerivAt_sq (T := T0) hZ
      have h2 := (hasDerivAt_zpow (expo α) ((T0.sq (T0.expt ((0 : ℝ) • Z)) : ℂˣ) : ℂ)
        (.inl (Units.ne_zero _))).scomp (0 : ℝ) h1
      refine (h2.smul_const _).congr_deriv ?_
      simp [T0.expt_zero, mul_comm]

end RankOne

instance uniqueIxOneZero : Unique (Ix 1 0) := ⟨⟨.inl 0⟩, by rintro (i | i); exacts [congrArg _ (Subsingleton.elim _ _), i.elim0]⟩

instance uniqueIxZeroOne : Unique (Ix 0 1) := ⟨⟨.inr 0⟩, by rintro (i | i); exacts [i.elim0, congrArg _ (Subsingleton.elim _ _)]⟩

def circlePos : Osc 1 0 (DetSqrtCover.grpOf 1 0 MeasureTheory.Measure.haar) := rankOne _

def circleNeg : Osc 0 1 (DetSqrtCover.grpOf 0 1 MeasureTheory.Measure.haar) := rankOne _

example (T0 : GrpData 1 0) (g : T0.G) (k : ℕ) :
    (rankOne T0).Om g ((rankOne T0).ι (monomial (Finsupp.single (.inl 0) k) 1)) =
      ((T0.sq g : ℂˣ) : ℂ) ^ (2 * k + 1 : ℤ) • (rankOne T0).ι (monomial (Finsupp.single (.inl 0) k) 1) := by
  have h : expo (Finsupp.single (Sum.inl 0 : Ix 1 0) k) = 2 * k + 1 := by
    change (1 : ℤ) * (2 * (Finsupp.single (Sum.inl 0 : Ix 1 0) k (.inl 0) : ℕ) + 1) = _
    simp
  exact h ▸ rankOneRep_monomial g (Finsupp.single (.inl 0) k) 1

example : oscAct 0 1 (Eab (.inr 0) (.inr 0)) 1 = (-(1 / 2) : ℂ) • 1 := by
  rw [oscAct_Eab, unitOp_inr_inr]; simp

example : oscAct 1 1 (Eab (.inl 0) (.inr 0)) 1 = X (.inl 0) * X (.inr 0) := by
  rw [oscAct_Eab, unitOp_inl_inr, mul_one]

end Osc

end GlobalTheory

open Formalism.BasicNotions Formalism.BasicNotions.TH

namespace GlobalTheory.Mem.Osc

def oscillatorLowering {P Q : ℕ} (l : Ix P Q) : Module.End ℂ (MvPolynomial (Ix P Q) ℂ) :=
  if l.isLeft then (MvPolynomial.pderiv l).toLinearMap else LinearMap.mulLeft ℂ (MvPolynomial.X l)

def oscillatorRaising {P Q : ℕ} (l : Ix P Q) : Module.End ℂ (MvPolynomial (Ix P Q) ℂ) :=
  if l.isLeft then LinearMap.mulLeft ℂ (MvPolynomial.X l) else -(MvPolynomial.pderiv l).toLinearMap

def oscillatorMatrixUnit {P Q : ℕ} (l l' : Ix P Q) : Module.End ℂ (MvPolynomial (Ix P Q) ℂ) :=
  oscillatorRaising l * oscillatorLowering l' + if l = l' then (1 / 2 : ℂ) • 1 else 0

def omAct0 (P Q : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (MvPolynomial (Ix P Q) ℂ) :=
  ∑ l, ∑ l', (Matrix.entryLinearMap ℂ ℂ l l').smulRight (oscillatorMatrixUnit l l')

structure Fock (σ : Type) [DecidableEq σ] where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  ι : MvPolynomial σ ℂ →ₗ[ℂ] H
  ι_inj : Function.Injective ι
  dense : Dense (Set.range ι)
  fockIP : ∀ α β, inner ℂ (ι (MvPolynomial.monomial α 1)) (ι (MvPolynomial.monomial β 1)) =
    if α = β then α.prod (fun _ k => (k.factorial : ℂ)) else 0

attribute [instance] Fock.nacg Fock.ips Fock.cs

structure IsOsc {P Q : ℕ} (T0 : GrpData P Q) (F : Fock (Ix P Q)) (Om : T0.G →* (F.H →L[ℂ] F.H)) : Prop where
  isom : ∀ g x, ‖Om g x‖ = ‖x‖
  cont : ∀ x, Continuous fun g => Om g x
  der : ∀ Z ∈ upq P Q, ∀ f, HasDerivAt (fun t : ℝ => Om (T0.expt (t • Z)) (F.ι f)) (F.ι (omAct0 P Q Z f)) 0

def HasCoeff {σ : Type} [DecidableEq σ] (F : Fock σ) (v : F.H) (c : MvPowerSeries σ ℂ) : Prop :=
  ∀ α, inner ℂ (F.ι (MvPolynomial.monomial α 1)) v = α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α c

def expPS {σ : Type} (q : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ :=
  fun α => ∑ n ∈ Finset.range (α.degree + 1), MvPolynomial.coeff α (q ^ n) / (n.factorial : ℂ)

def gaussPoly {P Q : ℕ} (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : MvPolynomial (Ix P Q) ℂ :=
  ∑ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr j) +
    ∑ l, MvPolynomial.C (x l) * MvPolynomial.X l

section Bridge

open MvPolynomial GlobalTheory.Oscillator

variable {P Q : ℕ} {T0 : GrpData P Q}

theorem loweringOperator_eq (l : Ix P Q) : oscillatorLowering l = low l := rfl

theorem raisingOperator_eq (l : Ix P Q) : oscillatorRaising l = rai l := rfl

theorem matrixUnitOperator_eq (l l' : Ix P Q) : oscillatorMatrixUnit l l' = unitOp l l' := rfl

theorem omAct0_eq (P Q : ℕ) : omAct0 P Q = oscAct P Q := rfl

def seqFock (σ : Type) [DecidableEq σ] : Fock σ where
  H := FockSeq.L2 σ
  ι := FockSeq.emb σ
  ι_inj := FockSeq.emb_injective
  dense := FockSeq.dense_range_emb
  fockIP α β := by convert FockSeq.isFockIsometry_embedding α β

instance instInhabitedFock (σ : Type) [DecidableEq σ] : Inhabited (Fock σ) := ⟨seqFock σ⟩

def fockOf (O : GlobalTheory.Osc P Q T0) : Fock (Ix P Q) where
  H := O.H
  ι := O.ι
  ι_inj := O.ι_inj
  dense := O.dense
  fockIP := O.fockIP

theorem isOsc_fockOf (O : GlobalTheory.Osc P Q T0) : IsOsc T0 (fockOf O) O.Om :=
  ⟨O.isom, O.cont, O.der⟩

def IsOsc.toOsc {F : Fock (Ix P Q)} {Om : T0.G →* (F.H →L[ℂ] F.H)} (h : IsOsc T0 F Om) : GlobalTheory.Osc P Q T0 where
  H := F.H
  Om := Om
  isom := h.isom
  cont := h.cont
  ι := F.ι
  ι_inj := F.ι_inj
  dense := F.dense
  fockIP := F.fockIP
  der := h.der

theorem IsOsc.fockOf_toOsc {F : Fock (Ix P Q)} {Om : T0.G →* (F.H →L[ℂ] F.H)} (h : IsOsc T0 F Om) :
    fockOf h.toOsc = F := rfl

theorem toOsc_isOsc_fockOf (O : GlobalTheory.Osc P Q T0) : (isOsc_fockOf O).toOsc = O := rfl

theorem nonempty_osc_iff :
    Nonempty (GlobalTheory.Osc P Q T0) ↔ ∃ (F : Fock (Ix P Q)) (Om : T0.G →* (F.H →L[ℂ] F.H)), IsOsc T0 F Om :=
  ⟨fun ⟨O⟩ => ⟨_, _, isOsc_fockOf O⟩, fun ⟨_, _, h⟩ => ⟨h.toOsc⟩⟩

theorem isOsc_rankOne [Unique (Ix P Q)] (T0 : GrpData P Q) :
    IsOsc T0 (seqFock (Ix P Q)) (GlobalTheory.Osc.rankOneRep T0) :=
  isOsc_fockOf (GlobalTheory.Osc.rankOne T0)

theorem isOsc_circlePos : IsOsc _ (fockOf GlobalTheory.Osc.circlePos) GlobalTheory.Osc.circlePos.Om := isOsc_fockOf _

theorem isOsc_circleNeg : IsOsc _ (fockOf GlobalTheory.Osc.circleNeg) GlobalTheory.Osc.circleNeg.Om := isOsc_fockOf _

theorem not_isOsc_one (T0 : GrpData 1 0) (F : Fock (Ix 1 0)) : ¬ IsOsc T0 F 1 := fun h => by
  have hZ : (Complex.I • (1 : Mat 1 0)) ∈ upq 1 0 := by
    simp [upq, Matrix.conjTranspose_smul]
  have h1 := (h.der _ hZ (monomial 0 1)).unique (hasDerivAt_const (0 : ℝ) (F.ι (monomial 0 1)))
  rw [omAct0_eq, GlobalTheory.Osc.oscAct_monomial_of_unique, ← map_zero F.ι] at h1
  have h2 := congrArg (coeff 0) (F.ι_inj h1)
  have h3 : GlobalTheory.Osc.expo (0 : Ix 1 0 →₀ ℕ) = 1 := rfl
  simp [h3] at h2

theorem hasCoeff_coe {σ : Type} [DecidableEq σ] (F : Fock σ) (f : MvPolynomial σ ℂ) :
    HasCoeff F (F.ι f) (f : MvPowerSeries σ ℂ) := by
  intro α
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, inner_add_right, hf, hg, MvPolynomial.coe_add, mul_add]
  | monomial β c =>
    have e : (monomial β c : MvPolynomial σ ℂ) = c • monomial β 1 := by simp [smul_monomial]
    rw [MvPolynomial.coeff_coe, coeff_monomial, e, map_smul, inner_smul_right, F.fockIP]
    by_cases h : α = β
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h]

theorem coeff_zero_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : coeff 0 (gaussPoly A x) = 0 := by
  change constantCoeff (gaussPoly A x) = 0
  simp [gaussPoly]

example : oscillatorMatrixUnit (P := 1) (Q := 1) (.inl 0) (.inr 0) 1 = X (.inl 0) * X (.inr 0) := by
  rw [matrixUnitOperator_eq, unitOp_inl_inr, mul_one]

example : oscillatorMatrixUnit (P := 1) (Q := 1) (.inr 0) (.inr 0) 1 = (-(1 / 2) : ℂ) • 1 := by
  rw [matrixUnitOperator_eq, unitOp_inr_inr]; simp

end Bridge

end GlobalTheory.Mem.Osc

end
