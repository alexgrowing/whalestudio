import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLatticeExistsScalarBoundAttainedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShapeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionInvariantPairFunctionalResidueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoTransvectionInvariantPairOnScaledKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section

namespace GlobalTheory.LatPair.StabScal

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]

def scal (s : k) (hs : s ≠ 0) : GL n k :=
  ⟨s • 1, s⁻¹ • 1, by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hs, one_smul],
    by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs, one_smul]⟩

theorem scal_inv_smul (s : k) (hs : s ≠ 0) (x : n → k) : (scal s hs : GL n k)⁻¹ • x = s⁻¹ • x := by
  show (s⁻¹ • (1 : Matrix n n k)) *ᵥ x = _
  rw [Matrix.smul_mulVec, one_mulVec]

theorem scal_comm (s : k) (hs : s ≠ 0) (h : GL n k) : h * scal s hs = scal s hs * h := by
  ext1
  show h.val * (s • (1 : Matrix n n k)) = (s • (1 : Matrix n n k)) * h.val
  rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]

def trv (b d : n) (t : k) (hbd : b ≠ d) : GL n k :=
  ⟨Matrix.transvection b d t, Matrix.transvection b d (-t),
   by rw [Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero],
   by rw [Matrix.transvection_mul_transvection_same b d hbd, neg_add_cancel, Matrix.transvection_zero]⟩

theorem transvection_mulVec' (b d : n) (t : k) (x : n → k) :
    Matrix.transvection b d t *ᵥ x = x + Pi.single b (t * x d) := by
  ext j
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.single_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_and]
  by_cases h : b = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem trv_inv_smul (b d : n) (t : k) (hbd : b ≠ d) (x : n → k) :
    (trv b d t hbd)⁻¹ • x = x + Pi.single b (-t * x d) := transvection_mulVec' b d (-t) x

end SlopeTestRemainingChoices

theorem transvection_smul_stdPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i b d : n) (t : 𝒪[k]) (g : GL n k), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → g.val = Matrix.transvection b d (t : k) → g • GlobalTheory.LatPair.stdPair k i = GlobalTheory.LatPair.stdPair k i := by
  intro k _ _ _ _ n _ _ i b d t g hbd hbi hg
  have hinv : (g⁻¹ : GL n k).val = Matrix.transvection b d (-(t : k)) := by
    have h1 : (g⁻¹ : GL n k).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹ : GL n k).val = (g⁻¹ : GL n k).val * (g.val * Matrix.transvection b d (-(t : k))) := by
          rw [hg, Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero,
            mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have htO : (t : k) ∈ 𝒪[k] := t.2
  refine Pair.ext fun x a => ?_
  let y : n → k := x + Pi.single b (-(t : k) * x d)
  have hyj : ∀ j, y j = x j + (Pi.single b (-(t : k) * x d) : n → k) j := fun j => rfl
  have hsm : g⁻¹ • x = y := by
    show (g⁻¹ : GL n k).val *ᵥ x = _
    rw [hinv, transvection_mulVec']
  rw [Pair.smul_hasVal, hsm, stdPair_hasVal, stdPair_hasVal]
  have hd : y d = x d := by rw [hyj]; simp [Pi.single_apply, Ne.symm hbd]
  have hint : (∀ j, y j ∈ 𝒪[k]) ↔ ∀ j, x j ∈ 𝒪[k] := by
    constructor
    · intro hy j
      have hxd : x d ∈ 𝒪[k] := by rw [← hd]; exact hy d
      have : x j = y j + (Pi.single b ((t : k) * x d) : n → k) j := by
        rw [hyj]
        simp only [Pi.single_apply]
        split_ifs <;> ring
      rw [this]
      refine add_mem (hy j) ?_
      rw [Pi.single_apply]
      split_ifs
      · exact mul_mem htO hxd
      · exact zero_mem _
    · intro hx j
      rw [hyj, Pi.single_apply]
      split_ifs
      · exact add_mem (hx j) (mul_mem (neg_mem htO) (hx d))
      · simpa using hx j
  have hres : ∀ (hx : ∀ j, x j ∈ 𝒪[k]) (hy : ∀ j, y j ∈ 𝒪[k]),
      IsLocalRing.residue 𝒪[k] ⟨y i, hy i⟩ = IsLocalRing.residue 𝒪[k] ⟨x i, hx i⟩ := by
    intro hx hy
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    by_cases hb : b = i
    · subst hb
      have hm : t ∈ IsLocalRing.maximalIdeal 𝒪[k] := hbi.resolve_left (not_not.2 rfl)
      have : (⟨y b, hy b⟩ : 𝒪[k]) - ⟨x b, hx b⟩ = -(t * ⟨x d, hx d⟩) := by
        apply Subtype.ext
        push_cast
        rw [hyj, Pi.single_eq_same]
        ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ hm)
    · have : (⟨y i, hy i⟩ : 𝒪[k]) - ⟨x i, hx i⟩ = 0 := by
        apply Subtype.ext
        show y i - x i = 0
        rw [hyj]
        simp [Pi.single_apply, Ne.symm hb]
      rw [this]
      exact zero_mem _
  constructor
  · rintro ⟨hy, rfl⟩
    exact ⟨hint.1 hy, (hres _ hy).symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hint.2 hx, hres hx _⟩

theorem eq_scalar_smul_of_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (P P' : GlobalTheory.LatPair.Pair k n), 3 ≤ Fintype.card n → (∀ g : GL n k, g • P = P ↔ g • P' = P') → ∃ (g : GL n k) (s : k), s ≠ 0 ∧ g.val = s • (1 : Matrix n n k) ∧ P' = g • P := by
  intro k _ _ _ _ n _ _ P P' hn hst
  obtain ⟨i⟩ : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  set Q := h⁻¹ • P' with hQ
  clear_value Q
  have hstQ : ∀ g : GL n k, g • stdPair k i = stdPair k i → g • Q = Q := by
    intro g hg
    have h1 : (h * g * h⁻¹) • P = P := by rw [← hh, smul_smul, show h * g * h⁻¹ * h = h * g by group, mul_smul, hg]
    have h2 := (hst _).1 h1
    rw [hQ, smul_smul]
    calc (g * h⁻¹) • P' = h⁻¹ • (h * g * h⁻¹) • P' := by rw [smul_smul]; congr 1; group
      _ = h⁻¹ • P' := by rw [h2]
  have hcl : ∀ (x : n → k) (a : 𝓀[k]), Q.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d →
      (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → Q.HasVal (x + Pi.single b ((t : k) * x d)) a := by
    intro x a hx b d t hbd hbi
    have hg : trv b d ((-t : 𝒪[k]) : k) hbd • stdPair k i = stdPair k i :=
      transvection_smul_stdPair k n i b d (-t) _ hbd (hbi.imp id (fun h => (IsLocalRing.maximalIdeal 𝒪[k]).neg_mem_iff.2 h)) rfl
    have h2 : (trv b d ((-t : 𝒪[k]) : k) hbd • Q).HasVal x a := by rw [hstQ _ hg]; exact hx
    rw [Pair.smul_hasVal, trv_inv_smul] at h2
    convert h2 using 3
    push_cast
    ring
  have hlat : ∀ x ∈ Q.lat, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) →
      x + Pi.single b ((t : k) * x d) ∈ Q.lat := fun x hx b d t hbd hbi =>
    (hcl x _ (Q.hasVal_fn ⟨x, hx⟩) b d t hbd hbi).mem
  obtain ⟨c, hc0, hcb, hca⟩ := GlobalTheory.T.localLattice_exists_scalar_bound_attained k n Q.lat Q.isLat ⟨i⟩
  rcases GlobalTheory.T.transvectionStable_localLattice_shape k n i Q.lat c hn hc0 hlat hcb hca with hA | hB
  swap
  · exact (GlobalTheory.T.no_transvectionInvariant_pair_on_scaledKernel k n i Q c hn hc0 hB hcl).elim
  obtain ⟨ε, hε0, hε⟩ := GlobalTheory.T.transvectionInvariant_pair_functional_residue k n i Q c (by omega) hc0 hA hcl
  obtain ⟨w, hw⟩ := IsLocalRing.residue_surjective (R := 𝒪[k]) ε
  have hwu : IsUnit w := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hw]
    exact hε0
  obtain ⟨u, hu⟩ := hwu
  have huw : (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * (w : k) = 1 := by
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * w = 1 := by rw [← hu, Units.inv_mul]
    have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
    simpa using h2
  have hw0 : (w : k) ≠ 0 := fun h0 => by simp [h0] at huw
  have hint : ∀ y : k, (w : k) * y ∈ 𝒪[k] → y ∈ 𝒪[k] := by
    intro y hy
    have : y = (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * ((w : k) * y) := by rw [← mul_assoc, huw, one_mul]
    rw [this]
    exact mul_mem (u⁻¹ : 𝒪[k]ˣ).val.2 hy
  set s := c * (w : k)⁻¹ with hs_def
  have hs : s ≠ 0 := mul_ne_zero hc0 (inv_ne_zero hw0)
  have key : ∀ y : k, s⁻¹ * y = (w : k) * (c⁻¹ * y) := by
    intro y
    rw [hs_def, mul_inv, inv_inv]
    ring
  have hQs : Q = (scal s hs : GL n k) • stdPair k i := by
    refine Pair.ext fun x a => ?_
    rw [Pair.smul_hasVal, stdPair_hasVal, scal_inv_smul]
    constructor
    · intro hQx
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := (hA x).1 hQx.mem
      refine ⟨fun j => ?_, ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, key]
        exact mul_mem w.2 (hx j)
      · rw [hQx.unique (hε x hx), ← hw, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Pi.smul_apply, smul_eq_mul, key]
        push_cast
        ring
    · rintro ⟨hx', rfl⟩
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := fun j => hint _ (by have := hx' j; rwa [Pi.smul_apply, smul_eq_mul, key] at this)
      convert hε x hx using 1
      rw [← hw, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Pi.smul_apply, smul_eq_mul, key]
      push_cast
      ring
  refine ⟨(scal s hs : GL n k), s, hs, rfl, ?_⟩
  calc P' = h • Q := by rw [hQ, smul_inv_smul]
    _ = h • (scal s hs : GL n k) • stdPair k i := by rw [hQs]
    _ = (scal s hs : GL n k) • P := by rw [← hh, smul_smul, smul_smul, scal_comm]

end GlobalTheory.LatPair.StabScal

end
