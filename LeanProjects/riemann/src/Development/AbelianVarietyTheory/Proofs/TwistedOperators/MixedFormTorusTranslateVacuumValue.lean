import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDuStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacuStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesUnitaryDiagonalTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CayleyUnitaryTorusInvDetIntegralOrderStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SphTheta.TorusVac

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def lmulI {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) : Matrix (Fin n') (Fin n) L →ₗ[intL L] Matrix (Fin n') (Fin n) L where
  toFun x := A * x
  map_add' := Matrix.mul_add A
  map_smul' r x := Matrix.mul_smul A r x

def ex (n' : ℕ) (k : Fin (n' / 2)) (i : Fin n') : ℤ :=
  if i = lo n' k then 1 else if i = (lo n' k).rev then -1 else 0

theorem tMat_single (ϖ : L) (n' : ℕ) (k : Fin (n' / 2)) :
    tMat ϖ n' (n' / 2) (Pi.single k 1) = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := by
  unfold tMat
  congr 1
  funext i
  simp only [ex, lo, Fin.ext_iff, Fin.val_rev, Pi.single_apply]
  have hk := k.2
  have hi := i.2
  split_ifs <;> first | (exfalso; omega) | simp_all

variable {σ : L →+* L} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem pairing_unitary (h : GU σ n') (x y : Matrix (Fin n') (Fin n) L) :
    pairing σ δ ψ (h.1.1 * x) (h.1.1 * y) = pairing σ δ ψ x y := by
  have hu : cT σ h.1.1 * antiJ L n' * h.1.1 = antiJ L n' := h.2
  have hl : locH σ δ (antiG L n) (antiG L n') (h.1.1 * x) (h.1.1 * y) = locH σ δ (antiG L n) (antiG L n') x y := by
    unfold locH
    congr 1
    have e1 : ((h.1.1 * y).map σ)ᵀ = (y.map σ)ᵀ * cT σ h.1.1 := by
      rw [Matrix.map_mul, Matrix.transpose_mul]; rfl
    have e2 : ((antiG L n' : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = antiJ L n' := rfl
    rw [e1, e2]
    congr 1
    calc _ = (((antiG L n)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (y.map σ)ᵀ * (cT σ h.1.1 * antiJ L n' * h.1.1) * x := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]
  have e3 : ∀ a b : Matrix (Fin n') (Fin n) L, pairing σ δ ψ a b =
      ψ (locH σ δ (antiG L n) (antiG L n') a b + σ (locH σ δ (antiG L n) (antiG L n') a b)) := by
    intro a b; rw [locH_antiG]; rfl
  rw [e3, e3, hl]

theorem mul_inv_val (t : GU σ n') : t.1.1 * (t⁻¹).1.1 = 1 := by
  rw [show t.1.1 * (t⁻¹).1.1 = (t * t⁻¹).1.1 from rfl, mul_inv_cancel]; rfl

theorem selfDual_map (t : GU σ n') {A : Submodule (intL L) (Matrix (Fin n') (Fin n) L)}
    (hA : SelfDual (pairing σ δ ψ) A) : SelfDual (pairing σ δ ψ) (A.map (lmulI t.1.1)) := by
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨b, hb, rfl⟩
    show pairing σ δ ψ (t.1.1 * y) (t.1.1 * b) = 1
    rw [pairing_unitary]
    exact (hA y).1 hy b hb
  · intro H
    have hy : (t⁻¹).1.1 * x ∈ A := by
      refine (hA _).2 fun b hb => ?_
      rw [← pairing_unitary t, ← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]
      exact H _ ⟨b, hb, rfl⟩
    refine ⟨_, hy, ?_⟩
    show t.1.1 * ((t⁻¹).1.1 * x) = x
    rw [← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]

theorem idx_translate_ne {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (t : GU σ n') (d : Fin n' → ℤ)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    idx (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) ≠ 0 := by
  have h := GlobalTheory.LatIdx.relIndex_intMat_translate ϖ σ q hU n' n d t ht 1 (one_mem _) 1 (one_mem _)
  simp only [one_mul, mul_one] at h
  have e1 : (intMat L (Fin n') (Fin n)).toAddSubgroup = GlobalTheory.InertHomIdx.intMat L n' n :=
    AddSubgroup.ext fun _ => Iff.rfl
  have e2 : ((intMat L (Fin n') (Fin n)).map (lmulI (n := n) t.1.1)).toAddSubgroup =
      AddSubgroup.map (GlobalTheory.InertHomIdx.lmul t.1.1) (GlobalTheory.InertHomIdx.intMat L n' n) :=
    AddSubgroup.ext fun _ => Iff.rfl
  unfold idx
  rw [e1, e2, h]
  exact pow_ne_zero _ (pow_ne_zero _ (by have := hU.2.2.2.2.2.1; omega))

theorem mem_of_mixLat {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) (k : Fin (n' / 2)) (t : GU σ n')
    (hT : t.1.1 = Matrix.diagonal fun i => ϖ ^ ex n' k i) {x a : Matrix (Fin n') (Fin n) L}
    (hx : x ∈ (intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ha : a ∈ mixLat L n' n)
    (hxa : x - a ∈ intMat L (Fin n') (Fin n)) : x ∈ intMat L (Fin n') (Fin n) := by
  obtain ⟨y, hy, rfl⟩ := hx
  intro r c
  by_cases hr : r = (lo n' k).rev
  · have hk := k.2
    have h0 : a r c = 0 := (ha r c).1 (Or.inl (by subst hr; simp only [lo, Fin.val_rev]; omega))
    have := hxa r c
    rwa [Matrix.sub_apply, h0, sub_zero] at this
  · show (t.1.1 * y) r c ∈ intL L
    rw [hT, Matrix.diagonal_mul]
    have hp : ϖ ^ ex n' k r ∈ intL L := by
      have he : ex n' k r = 1 ∨ ex n' k r = 0 := by
        unfold ex; split_ifs <;> simp_all
      rcases he with he | he <;> rw [he]
      · simpa using mem_intL.2 hϖ
      · simpa using one_mem (intL L)
    exact mul_mem hp (hy r c)

end GlobalTheory.SphTheta.TorusVac

open GlobalTheory.SphTheta.TorusVac in

theorem GlobalTheory.SphTheta.mixed_torus_value : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → ℓ (ω (1, t) s) = (-1) ^ n * (q : ℂ) ^ (-(n : ℤ)) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC ℓ hℓs hℓmix hℓzero k t ht
  have hU := hS.1.unr
  have hH := hS.isHeis
  have hΛ := hS.selfDual
  have hϖle : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1:ℤ)) ≤ 1)
  have hT : t.1.1 = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := ht.trans (tMat_single ϖ n' k)
  have hΛ' := selfDual_map (n := n) (δ := δ) (ψ := ψ) t hΛ
  have hidx := idx_translate_ne (n := n) hU t _ hT
  obtain ⟨e, he1, heinv⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ (fun a ha b hb => hH.iso hΛ ha hb)
  have hv : Fixes ρ ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ω (1, t) s) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hS.1.norm 1 t y)
    simp only [Module.End.mul_apply] at h1
    rw [hS.fixes y hy] at h1
    simp at h1
    exact h1.symm
  have hsum : ℓ (sumOp ρ (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) s) = 1 := by
    obtain ⟨N, f, hf, hu⟩ := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').2.1 hidx).1
    rw [((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').1 s hS.fixes (Fin N) f hf hu).1, map_sum]
    obtain ⟨i0, hi0, huniq⟩ := hu 0 (zero_mem _)
    have key : ∀ i, ℓ (ρ (f i) s) = if i = i0 then 1 else 0 := by
      intro i
      by_cases hfi : f i ∈ intMat L (Fin n') (Fin n)
      · have : i = i0 := huniq i (by show 0 - f i ∈ _; rw [zero_sub]; exact neg_mem hfi)
        rw [if_pos this, hS.fixes _ hfi, hℓs]
      · have hne : i ≠ i0 := by
          rintro rfl
          apply hfi
          have := neg_mem hi0
          rwa [zero_sub, neg_neg] at this
        rw [if_neg hne]
        apply hℓzero
        rintro ⟨a, ha, hxa⟩
        exact hfi (mem_of_mixLat hϖle k t hT (hf i) ha hxa)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨hd, hint, hord⟩ := GlobalTheory.T.cayley_unitaryTorus_inv_det_integral_order L ϖ σ q hU hS.v_two n' k t ht
  have hev := hC e heinv t⁻¹ hd hint
  rw [inv_inv, hord, he1, mul_one] at hev
  have hco := (GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ hΛ' hidx).2 e he1 heinv _ hv
  rw [hco, map_smul, hsum, smul_eq_mul, mul_one]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hev
  rw [hev, _root_.zpow_neg, zpow_one, mul_inv, _root_.zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
