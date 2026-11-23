import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

noncomputable section

namespace UpperTheory.V.Z.Sym.Al.InfV

open MvPolynomial

private abbrev Y (a : Fin 2) : MvPolynomial (Fin 2 × Fin 2) ℂ := X (a, 0)

private def lin (a b : ℂ) : MvPolynomial (Fin 2 × Fin 2) ℂ := C a * Y 1 - C b * Y 0

private theorem natW_eq (lam : DomWeight 2) {j : ℕ} (hj : lam.w 0 - lam.w 1 = j) : lam.natW = ![j, 0] := by
  have h : lam.detShift = lam.w 1 := rfl
  funext i
  fin_cases i
  · simp [DomWeight.natW, h, hj]
  · simp [DomWeight.natW, h]

private theorem mono_mem (lam : DomWeight 2) {j : ℕ} (hj : lam.w 0 - lam.w 1 = j) (k : ℕ) (hk : k ≤ j) :
    Y 1 ^ k * Y 0 ^ (j - k) ∈ nablaSq ℂ 2 lam := by
  have hY : ∀ a, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW 2 2) (Y a) (![1, 0] : Fin 2 → ℕ) := fun a => by
    have hw : Formalism.GradedWeylDivisibility.colW 2 2 ((a, 0) : Fin 2 × Fin 2) = (![1, 0] : Fin 2 → ℕ) := by
      funext i
      fin_cases i <;> simp [Formalism.GradedWeylDivisibility.colW]
    have := isWeightedHomogeneous_X ℂ (Formalism.GradedWeylDivisibility.colW 2 2) ((a, 0) : Fin 2 × Fin 2)
    rwa [hw] at this
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule, natW_eq lam hj]
    have := ((hY 1).pow k).mul ((hY 0).pow (j - k))
    have e : k • (![1, 0] : Fin 2 → ℕ) + (j - k) • (![1, 0] : Fin 2 → ℕ) = ![j, 0] := by
      funext i
      fin_cases i
      · simp; omega
      · simp
    rwa [e] at this
  · simp only [Submodule.mem_iInf]
    intro l m hlm
    have hl : l = 0 := by omega
    have hm : m = 1 := by omega
    subst hl hm
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp [Formalism.GradedWeylDivisibility.colAddGen, Y]

private def mon (lam : DomWeight 2) {j : ℕ} (hj : lam.w 0 - lam.w 1 = j) (k : Fin (j + 1)) : nablaSq ℂ 2 lam :=
  ⟨Y 1 ^ (k : ℕ) * Y 0 ^ (j - k), mono_mem lam hj k (Nat.lt_succ_iff.1 k.2)⟩

private def cf (j : ℕ) (k : Fin (j + 1)) (a b : ℂ) : ℂ := (j.choose k : ℂ) * (a ^ (k : ℕ) * (-b) ^ (j - k))

private def D (lam : DomWeight 2) {j : ℕ} (hj : lam.w 0 - lam.w 1 = j) (a b : ℂ) : nablaSq ℂ 2 lam :=
  ∑ k, cf j k a b • mon lam hj k

private theorem D_coe (lam : DomWeight 2) {j : ℕ} (hj : lam.w 0 - lam.w 1 = j) (a b : ℂ) :
    (D lam hj a b : MvPolynomial (Fin 2 × Fin 2) ℂ) = lin a b ^ j := by
  have e : lin a b = C a * Y 1 + C (-b) * Y 0 := by simp [lin, sub_eq_add_neg]
  rw [e, add_pow, Finset.sum_range]
  simp only [D, Submodule.coe_sum, Submodule.coe_smul, mon, cf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul]
  simp only [map_mul, map_pow, map_natCast, mul_pow]
  ring

private theorem rowAct_lin (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := 2) M.transpose (lin a b) = lin (a * M 1 1 - b * M 1 0) (b * M 0 0 - a * M 0 1) := by
  simp only [lin, Y, Formalism.GradedWeylDivisibility.rowAct, map_sub, map_mul, algHom_C, aeval_X, Fin.sum_univ_two, Matrix.transpose_apply,
    map_sub, map_mul]
  simp only [algebraMap_eq]
  ring

private theorem lin_scale (d a b : ℂ) : lin (d * a) (d * b) = C d * lin a b := by
  simp only [lin, map_mul]
  ring

private theorem sq_D (lam : DomWeight 2) {j : ℕ} (hj : lam.w 0 - lam.w 1 = j) (h : GL (Fin 2) ℂ) (a b : ℂ) :
    GlobalTheory.Branching.sqRep ℂ 2 lam h (D lam hj a b) = ((Matrix.GeneralLinearGroup.det h ^ (lam.w 1 + (j : ℤ)) : ℂˣ) : ℂ) •
      D lam hj (a * (h⁻¹).val 0 0 + b * (h⁻¹).val 1 0) (a * (h⁻¹).val 0 1 + b * (h⁻¹).val 1 1) := by
  apply Subtype.ext
  have hs : lam.detShift = lam.w 1 := rfl
  have h1 : h.val * (h⁻¹).val = 1 := Units.mul_inv h
  have hadj : h.val.det • (h⁻¹).val = h.val.adjugate := by
    calc h.val.det • (h⁻¹).val = (h.val.adjugate * h.val) * (h⁻¹).val := by rw [Matrix.adjugate_mul]; simp
      _ = h.val.adjugate := by rw [mul_assoc, h1, mul_one]
  have e00 := congrFun (congrFun hadj 0) 0
  have e01 := congrFun (congrFun hadj 0) 1
  have e10 := congrFun (congrFun hadj 1) 0
  have e11 := congrFun (congrFun hadj 1) 1
  simp only [Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at e00 e01 e10 e11
  have hl : lin (a * h.val 1 1 - b * h.val 1 0) (b * h.val 0 0 - a * h.val 0 1) =
      C h.val.det * lin (a * (h⁻¹).val 0 0 + b * (h⁻¹).val 1 0) (a * (h⁻¹).val 0 1 + b * (h⁻¹).val 1 1) := by
    rw [← lin_scale]
    congr 1
    · linear_combination (-a) * e00 + (-b) * e10
    · linear_combination (-a) * e01 + (-b) * e11
  rw [GlobalTheory.Branching.sqRep_coe, Submodule.coe_smul, D_coe, D_coe, sqAct, map_pow, rowAct_lin, detPow, hs, hl, mul_pow,
    ← map_pow, ← smul_eq_C_mul, smul_smul, zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val,
    Matrix.GeneralLinearGroup.val_det_apply]

private theorem cf_scale (j : ℕ) (k : Fin (j + 1)) (s a b : ℂ) : cf j k (s * a) (s * b) = s ^ j * cf j k a b := by
  have h : s ^ j = s ^ (k : ℕ) * s ^ (j - k) := by
    rw [← pow_add]
    congr 1
    have := k.2
    omega
  simp only [cf, ← mul_neg, mul_pow, h]
  ring

section Places

variable {L : Type} [Field L] [NumberField L] [IsCMField L] (lam : InfinitePlace L → DomWeight 2) {j : ℕ}
  (hj : ∀ v, (lam v).w 0 - (lam v).w 1 = j)

private def cv (x : InfinitePlace L × Fin 2 → ℂ) : GlobalTheory.BCT.TrKer.Wsp lam :=
  PiTensorProduct.tprod ℂ fun v => D (lam v) (hj v) (x (v, 0)) (x (v, 1))

private theorem wInf_cv (u : UA L 2) (x : InfinitePlace L × Fin 2 → ℂ) :
    GlobalTheory.BCT.TrKer.wInf lam u (cv lam hj x) =
      ((∏ v : InfinitePlace L, Matrix.GeneralLinearGroup.det (cEmb v.embedding u) ^ ((lam v).w 1 + (j : ℤ)) : ℂˣ) : ℂ) •
        cv lam hj (Wt.act (infC L 2 u⁻¹) x) := by
  rw [cv, GlobalTheory.BCT.TrKer.wInf_tprod]
  simp only [sq_D]
  rw [MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ), Units.coe_prod, cv]
  congr 2
  funext v
  simp [Wt.act, Fin.sum_univ_two, infC, map_inv]
  rfl

private def A (I : Type) [Fintype I] (j : ℕ) (κ : I → Fin (j + 1)) : MvPolynomial (I × Fin 2) ℂ :=
  ∏ v, (C (j.choose (κ v) : ℂ) * (X (v, 0) ^ (κ v : ℕ) * (-X (v, 1)) ^ (j - κ v)))

private theorem eval_A (I : Type) [Fintype I] (j : ℕ) (κ : I → Fin (j + 1)) (x : I × Fin 2 → ℂ) :
    eval x (A I j κ) = ∏ v, cf j (κ v) (x (v, 0)) (x (v, 1)) := by
  simp [A, cf]

private theorem A_mem (I : Type) [Fintype I] (j : ℕ) (κ : I → Fin (j + 1)) : A I j κ ∈ Wt.VD I j := by
  intro s x
  rw [eval_A, eval_A, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => cf_scale j (κ v) (s v) _ _

variable [DecidableEq (InfinitePlace L)]

private theorem cv_eq (x : InfinitePlace L × Fin 2 → ℂ) :
    cv lam hj x = ∑ κ : InfinitePlace L → Fin (j + 1), eval x (A (InfinitePlace L) j κ) •
      PiTensorProduct.tprod ℂ fun v => mon (lam v) (hj v) (κ v) := by
  simp only [cv, D]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MultilinearMap.map_smul_univ, eval_A]

omit [DecidableEq (InfinitePlace L)] in
private theorem cv_ne : ∃ x, cv lam hj x ≠ 0 := by
  have hne : ∀ v, D (lam v) (hj v) 1 0 ≠ 0 := fun v h => by
    have := congrArg Subtype.val h
    rw [D_coe] at this
    simp [lin] at this
  have hl : ∀ v, ∃ l : Module.Dual ℂ (nablaSq ℂ 2 (lam v)), l (D (lam v) (hj v) 1 0) ≠ 0 := fun v => by
    by_contra hc
    push_neg at hc
    exact hne v ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  choose l hl using hl
  refine ⟨fun p => if p.2 = 0 then 1 else 0, fun h => ?_⟩
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (InfinitePlace L) ℂ).compLinearMap l)) h
  simp only [cv, PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at this
  refine Finset.prod_ne_zero_iff.2 (fun v _ => ?_) this
  simpa using hl v

end Places

end UpperTheory.V.Z.Sym.Al.InfV

open UpperTheory.V.Z.Sym.Al.InfV in
theorem UpperTheory.V.Z.Sym.Al.infVec :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (π : Submodule ℂ (UA L 2 → ℂ)), IsAutRepU π → ∀ j : ℕ,
        (∀ v : InfinitePlace L, ∃ lam, HasWeightAt π v.embedding lam ∧ lam.w 0 - lam.w 1 = j) →
        ∃ (e : InfinitePlace L → ℤ) (φ : UA L 2 → Wt.VD (InfinitePlace L) j), φ ≠ 0 ∧ CoefIn φ π ∧ IsAF (repE j e) ⊥ φ := by
  classical
  intro L _ _ _ π hπ j hW
  choose lam hlam hj using hW
  obtain ⟨T, hT0, hTπ, hT⟩ := GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep L 2 lam π hπ hlam
  let c : (InfinitePlace L → Fin (j + 1)) → GlobalTheory.BCT.TrKer.Wsp lam := fun κ =>
    PiTensorProduct.tprod ℂ fun v => mon (lam v) (hj v) (κ v)
  let a : (InfinitePlace L → Fin (j + 1)) → Wt.VD (InfinitePlace L) j := fun κ => ⟨A _ j κ, A_mem _ j κ⟩
  let φ : UA L 2 → Wt.VD (InfinitePlace L) j := fun g => ∑ κ, T (c κ) g • a κ
  have key : ∀ g x, MvPolynomial.eval x (φ g).1 = T (cv lam hj x) g := by
    intro g x
    rw [cv_eq, map_sum, Finset.sum_apply]
    simp only [φ, Submodule.coe_sum, Submodule.coe_smul, map_sum, MvPolynomial.smul_eval, map_smul, Pi.smul_apply,
      smul_eq_mul, a]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  refine ⟨fun v => -((lam v).w 1 + (j : ℤ)), φ, fun h0 => ?_, fun f => ?_, fun γ hγ g => ?_, fun u hu g => ?_,
    fun u hu g => ?_⟩
  · have hz : ∀ x, T (cv lam hj x) = 0 := fun x => funext fun g => by
      rw [← key, show φ g = 0 from congrFun h0 g]
      simp
    obtain ⟨-, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 (GlobalTheory.BCT.TrKer.isIrreducible_wInfU lam)
    have hst : ∀ (g : infU L 2), ∀ w ∈ Submodule.span ℂ (Set.range (cv lam hj)),
        GlobalTheory.BCT.TrKer.wInfU lam g w ∈ Submodule.span ℂ (Set.range (cv lam hj)) := by
      intro g w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨x, rfl⟩ := h
        change GlobalTheory.BCT.TrKer.wInf lam g.1 _ ∈ _
        rw [wInf_cv]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      | zero => simp
      | add p q _ _ hp hq => rw [map_add]; exact add_mem hp hq
      | smul s p _ hp => rw [map_smul]; exact Submodule.smul_mem _ s hp
    rcases hirr _ hst with h | h
    · obtain ⟨x, hx⟩ := cv_ne lam hj
      have : cv lam hj x ∈ Submodule.span ℂ (Set.range (cv lam hj)) := Submodule.subset_span ⟨x, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hx this
    · refine hT0 (LinearMap.ext fun w => ?_)
      have hw : w ∈ Submodule.span ℂ (Set.range (cv lam hj)) := by rw [h]; trivial
      have hle : Submodule.span ℂ (Set.range (cv lam hj)) ≤ LinearMap.ker T :=
        Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hz x)
      exact hle hw
  · have : f ∘ φ = ∑ κ, f (a κ) • T (c κ) := by
      funext g
      simp only [Function.comp, φ, map_sum, map_smul, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [this]
    exact π.sum_mem fun κ _ => π.smul_mem _ (hTπ _)
  · refine Finset.sum_congr rfl fun κ _ => ?_
    rw [(hπ.aut _ (hTπ (c κ))).left γ hγ g]
  · apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    have h1 : T (cv lam hj x) (g * u) = T (GlobalTheory.BCT.TrKer.wInf lam u (cv lam hj x)) g := by
      rw [hT u hu]
      rfl
    rw [key, h1, wInf_cv, map_smul, Pi.smul_apply, smul_eq_mul, ← key]
    change _ = MvPolynomial.eval x (((∏ v, Matrix.GeneralLinearGroup.det ((infC L 2 u⁻¹) v) ^ (-((lam v).w 1 + (j : ℤ))) : ℂˣ) : ℂ) •
      (Wt.mRep 2 _ (infC L 2 u⁻¹) (φ g))).1
    rw [Submodule.coe_smul, MvPolynomial.smul_eval, Wt.eval_mRep]
    congr 2
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [infC, map_inv, zpow_neg, inv_zpow]
    rfl
  · rw [Subgroup.mem_bot.1 hu, mul_one]

end
