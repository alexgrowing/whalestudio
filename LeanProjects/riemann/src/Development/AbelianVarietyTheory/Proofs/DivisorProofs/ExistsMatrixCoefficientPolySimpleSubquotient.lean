import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyCoefEqZeroOfCol

set_option autoImplicit false

noncomputable section

section Lemmas

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWt GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD

namespace GlobalTheory.HighWtEmb

variable {O : Type} [CommRing O] {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {lam : ι → ℕ → ℕ}
  {k : Type} [CommRing k] [Algebra O k] {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm]

variable (O N k) in

def blockEmb (τ : ι) : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (BVar N ι) k := aeval fun v => X (τ, v)

omit [Fintype ι] [DecidableEq ι] in
theorem blockEmb_monomial (τ : ι) (m : Fin N × Fin N →₀ ℕ) :
    blockEmb O N k τ (monomial m 1) = rename (Prod.mk τ) (monomial m (1 : k)) := by
  rw [monomial_eq, monomial_eq, C_1, C_1, one_mul, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow, rename_X, blockEmb, aeval_X]

omit [Fintype ι] in
theorem blockEmb_of_ne {τ σ : ι} (h : σ ≠ τ) (m : Fin N × Fin N →₀ ℕ) :
    blockEmb O N k σ (monomial m 1) ∈ (rename (R := k) (Subtype.val : OVar N τ → BVar N ι)).range := by
  refine ⟨rename (fun v => ⟨(σ, v), h⟩) (monomial m 1), ?_⟩
  rw [blockEmb_monomial]
  exact rename_rename _ _ _

variable (c : ι → (Fin N × Fin N →₀ ℕ) → alg O N lam)

def stepT (τ : ι) (ψ : Gm →+ MvPolynomial (BVar N ι) k) : Gm →+ MvPolynomial (BVar N ι) k where
  toFun z := ∑ m ∈ expSet N (res N (lam τ)), blockEmb O N k τ (monomial m 1) * ψ (c τ m • z)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

omit [Fintype ι] in
theorem stepT_apply (τ : ι) (ψ : Gm →+ MvPolynomial (BVar N ι) k) (z : Gm) :
    stepT c τ ψ z = ∑ m ∈ expSet N (res N (lam τ)), blockEmb O N k τ (monomial m 1) * ψ (c τ m • z) := rfl

variable (O lam) in

def Semi (ψ : Gm →+ MvPolynomial (BVar N ι) k) : Prop :=
  ∀ (r : O) z, ψ (algebraMap O (alg O N lam) r • z) = algebraMap O _ r * ψ z

def Good (τ : ι) (w : Fin N → ℕ) (ψ : Gm →+ MvPolynomial (BVar N ι) k) : Prop :=
  Semi O lam ψ ∧ (∀ z, ψ z ∈ (rename (R := k) (Subtype.val : OVar N τ → BVar N ι)).range) ∧
    ∀ m : Fin N × Fin N →₀ ℕ, (Finsupp.weight (colW N N) m ≠ w ∨
      ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v) → ∀ z, ψ (c τ m • z) = 0

omit [Fintype ι] in
theorem Semi.stepT {ψ : Gm →+ MvPolynomial (BVar N ι) k} (h : Semi O lam ψ) (τ : ι) : Semi O lam (stepT c τ ψ) := by
  intro r z
  rw [stepT_apply, stepT_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_smul, ← Algebra.commutes, mul_smul, h, mul_left_comm]

variable (hc : ∀ τ m, (c τ m : Module.End O (NablaT O N lam)) = atN O N lam τ (coefEnd O N _ m))
include hc

theorem Good.stepT {τ σ : ι} {w : Fin N → ℕ} {ψ : Gm →+ MvPolynomial (BVar N ι) k} (h : Good c τ w ψ) (hσ : σ ≠ τ) :
    Good c τ w (stepT c σ ψ) := by
  refine ⟨h.1.stepT c σ, fun z => ?_, fun m hm z => ?_⟩
  · rw [stepT_apply]
    exact Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ (blockEmb_of_ne hσ m) (h.2.1 _)
  · rw [stepT_apply]
    refine Finset.sum_eq_zero fun m' _ => ?_
    rw [smul_smul, coef_comm c hc hσ, mul_smul, h.2.2 m hm, mul_zero]

theorem stepT_comm {τ σ : ι} (hσ : σ ≠ τ) (ψ : Gm →+ MvPolynomial (BVar N ι) k) :
    stepT c σ (stepT c τ ψ) = stepT c τ (stepT c σ ψ) := by
  ext1 z
  simp only [stepT_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  rw [smul_smul, smul_smul, coef_comm c hc hσ, mul_left_comm]

theorem eval_stepT {ψ : Gm →+ MvPolynomial (BVar N ι) k} (h : Semi O lam ψ) (τ : ι) (z : Gm) :
    eval (fun p : BVar N ι => if p.2.1 = p.2.2 then (1 : k) else 0) (stepT c τ ψ z) =
      eval (fun p : BVar N ι => if p.2.1 = p.2.2 then (1 : k) else 0) (ψ z) := by
  let ev := eval (fun p : BVar N ι => if p.2.1 = p.2.2 then (1 : k) else 0)
  let θ : MvPolynomial Empty O →ₐ[O] k := aeval fun _ => 0
  refine Eq.trans ?_ (sum_unit c hc (ev.toAddMonoidHom.comp ψ) (fun r z => ?_) θ τ z)
  · rw [stepT_apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]
    refine congrArg (· * _) ?_
    rw [monomial_eq, C_1, one_mul]
    simp only [Finsupp.prod, map_prod, map_pow, blockEmb, unitHom, aeval_X, eval_X, apply_ite θ, map_one, map_zero]
  · show ev (ψ _) = _ * ev (ψ z)
    rw [h, map_mul, MvPolynomial.algebraMap_apply, eval_C]

theorem stepT_grp_single {τ : ι} {w : Fin N → ℕ} {ψ : Gm →+ MvPolynomial (BVar N ι) k} (h : Good c τ w ψ) (g : GL (Fin N) O) (z : Gm) :
    stepT c τ ψ (grpA O N lam (Pi.mulSingle τ g) • z) = blockSub k N
      (fun σ => ((((Pi.mulSingle τ g : ι → GL (Fin N) O) σ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (algebraMap O k))
        (stepT c τ ψ z) := by
  set B := blockSub k N
      (fun σ => ((((Pi.mulSingle τ g : ι → GL (Fin N) O) σ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (algebraMap O k)) with hB
  have h1 : (blockEmb O N k τ).comp (rowAct O ((g⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O)) =
      (B.restrictScalars O).comp (blockEmb O N k τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [hB, blockSub, blockEmb, rowAct, -Matrix.coe_units_inv]
  have h2 : B.comp (rename (Subtype.val : OVar N τ → BVar N ι)) = rename Subtype.val := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [hB, blockSub, Pi.mulSingle_eq_of_ne v.2, Matrix.one_apply, apply_ite (C : k →+* MvPolynomial (BVar N ι) k)]
  rw [stepT_apply, stepT_apply, sum_grp c hc ψ h.1, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  obtain ⟨q, hq⟩ := h.2.1 (c τ m • z)
  rw [map_mul, ← hq]
  exact congrArg₂ (· * ·) (AlgHom.congr_fun h1 _) (AlgHom.congr_fun h2 q).symm

theorem stepT_proj {τ : ι} {w : Fin N → ℕ} {ψ : Gm →+ MvPolynomial (BVar N ι) k} (h : Good c τ w ψ) (v : Fin N → ℕ) (z : Gm) :
    stepT c τ ψ (projA O N lam τ v • z) = weightedHomogeneousComponent (blockW N τ) v (stepT c τ ψ z) := by
  rw [stepT_apply, stepT_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : IsWeightedHomogeneous (blockW N τ) (blockEmb O N k τ (monomial m 1) * ψ (c τ m • z)) (Finsupp.weight (rowW N N) m) := by
    obtain ⟨q, hq⟩ := h.2.1 (c τ m • z)
    rw [← hq, blockEmb_monomial, ← add_zero (Finsupp.weight (rowW N N) m)]
    refine (isWH_algHom_monomial _ (rowW N N) _ (fun u => ?_) m 1).mul (isWH_algHom _ 0 _ (fun u => ?_) fun d _ => ?_)
    · rw [rename_X]
      simpa [blockW, rowW] using isWeightedHomogeneous_X k (blockW N τ) (τ, u)
    · rw [rename_X]
      simpa [blockW, u.2] using isWeightedHomogeneous_X k (blockW N τ) u.1
    · simp [Finsupp.weight_apply]
  rw [weightedHomogeneousComponent_of_mem h1, smul_smul, coef_mul_proj c hc]
  by_cases hv : Finsupp.weight (rowW N N) m = v
  · rw [if_pos hv, if_pos hv.symm]
  · rw [if_neg hv, if_neg (Ne.symm hv), zero_smul, map_zero, mul_zero]

theorem stepT_mem {τ : ι} {w : Fin N → ℕ} {ψ : Gm →+ MvPolynomial (BVar N ι) k} (h : Good c τ w ψ) (z : Gm) :
    toBlock k N τ (stepT c τ ψ z) ∈ dualWeyl (MvPolynomial (OVar N τ) k) N N w := by
  let ψ' : Gm →+ MvPolynomial (OVar N τ) k := (constantCoeff.comp (toBlock k N τ).toRingHom).toAddMonoidHom.comp ψ
  have hψ' : ∀ z, ψ' z = constantCoeff (toBlock k N τ (ψ z)) := fun _ => rfl
  have h1 : ∀ z, toBlock k N τ (ψ z) = C (ψ' z) := by
    intro z
    obtain ⟨q, hq⟩ := h.2.1 z
    have : (toBlock k N τ).toRingHom.comp (rename (Subtype.val : OVar N τ → BVar N ι)).toRingHom = C := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro u; simp [toBlock, u.2]
    have e : toBlock k N τ (ψ z) = C q := by rw [← hq]; exact RingHom.congr_fun this q
    rw [hψ', e, constantCoeff_C]
  have h2 : ∀ m, toBlock k N τ (blockEmb O N k τ (monomial m 1)) = monomial m 1 := by
    intro m
    rw [monomial_eq, monomial_eq, C_1, C_1, one_mul, one_mul]
    simp only [Finsupp.prod, map_prod, map_pow, blockEmb, toBlock, aeval_X, dif_pos]
  have h3 : toBlock k N τ (stepT c τ ψ z) = ∑ m ∈ expSet N (res N (lam τ)), monomial m 1 * C (ψ' (c τ m • z)) := by
    rw [stepT_apply, map_sum]
    simp only [map_mul, h1, h2]
  have h4 : ∀ m : Fin N × Fin N →₀ ℕ, (Finsupp.weight (colW N N) m ≠ w ∨
      ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v) → ∀ z, ψ' (c τ m • z) = 0 :=
    fun m hm z => by rw [hψ', h.2.2 m hm, map_zero, map_zero]
  rw [h3, rowst_mem_dualWeyl_iff]
  refine ⟨IsWeightedHomogeneous.sum _ _ _ fun m _ => ?_, fun l j hlj => ?_⟩
  · by_cases hm : Finsupp.weight (colW N N) m = w
    · rw [mul_comm]
      exact (isWeightedHomogeneous_monomial _ _ _ hm).C_mul _
    · rw [h4 m (Or.inl hm), map_zero, mul_zero]
      exact isWeightedHomogeneous_zero _ _ _
  · let θ : MvPolynomial (Option (Fin N × Fin N)) O →ₐ[O] MvPolynomial (Option (Fin N × Fin N)) (MvPolynomial (OVar N τ) k) := aeval X
    have := sum_col_eq c hc ((C : _ →+* MvPolynomial (Option (Fin N × Fin N)) (MvPolynomial (OVar N τ) k)).toAddMonoidHom.comp ψ')
      (fun r z => by
        show C (ψ' _) = _ * C (ψ' z)
        rw [hψ', hψ', h.1, map_mul, map_mul, map_mul]
        refine congrArg (· * _) ?_
        simp [MvPolynomial.algebraMap_apply]) θ τ l j hlj
      (fun m hm z => by
        show C (ψ' _) = 0
        rw [h4 m (Or.inr hm), map_zero]) z
    rw [map_sum, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) (this.trans (Finset.sum_congr rfl fun m _ => ?_))
    · rw [map_mul, MvPolynomial.algHom_C]
      refine congrArg (· * _) ?_
      rw [monomial_eq, monomial_eq, C_1, C_1, one_mul, one_mul]
      simp only [Finsupp.prod, map_prod, map_pow, colAddGen, aeval_X, apply_ite θ, map_add, map_mul, θ]
    · rw [map_mul, rename_C]
      refine congrArg (· * _) ?_
      rw [monomial_eq, monomial_eq, C_1, C_1, one_mul, one_mul]
      simp only [Finsupp.prod, map_prod, map_pow, rename_X, aeval_X, θ]

theorem exists_poly (w : ι → Fin N → ℕ) (ψ : Gm →+ MvPolynomial (BVar N ι) k) (h : ∀ τ, Good c τ (w τ) ψ) (hs : Semi O lam ψ)
    (s : Finset ι) : ∃ P : Gm →+ MvPolynomial (BVar N ι) k, Semi O lam P ∧
      (∀ z, eval (fun p : BVar N ι => if p.2.1 = p.2.2 then (1 : k) else 0) (P z) =
        eval (fun p : BVar N ι => if p.2.1 = p.2.2 then (1 : k) else 0) (ψ z)) ∧
      (∀ τ ∉ s, Good c τ (w τ) P) ∧ ∀ τ ∈ s, ∃ ψ', Good c τ (w τ) ψ' ∧ P = stepT c τ ψ' := by
  induction s using Finset.induction_on with
  | empty => exact ⟨ψ, hs, fun _ => rfl, fun τ _ => h τ, by simp⟩
  | insert σ s hσ ih =>
    obtain ⟨P, h1, h2, h3, h4⟩ := ih
    refine ⟨stepT c σ P, h1.stepT c σ, fun z => (eval_stepT c hc h1 σ z).trans (h2 z), fun τ hτ => ?_, fun τ hτ => ?_⟩
    · rw [Finset.mem_insert, not_or] at hτ
      exact (h3 τ hτ.2).stepT c hc (Ne.symm hτ.1)
    · rcases Finset.mem_insert.1 hτ with rfl | hτ'
      · exact ⟨P, h3 τ hσ, rfl⟩
      · obtain ⟨ψ', h5, rfl⟩ := h4 τ hτ'
        have hne : σ ≠ τ := by rintro rfl; exact hσ hτ'
        exact ⟨_, h5.stepT c hc hne, stepT_comm c hc hne ψ'⟩

omit hc [Fintype ι] [DecidableEq ι] in
theorem blockSub_blockSub (A A' : ι → Matrix (Fin N) (Fin N) k) (P : MvPolynomial (BVar N ι) k) :
    blockSub k N A (blockSub k N A' P) = blockSub k N (fun τ => A' τ * A τ) P := by
  have : (blockSub k N A).comp (blockSub k N A') = blockSub k N (fun τ => A' τ * A τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [blockSub, AlgHom.comp_apply, aeval_X, map_sum, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  exact AlgHom.congr_fun this P

omit hc in
theorem grp_of_single (P : Gm →+ MvPolynomial (BVar N ι) k)
    (h : ∀ τ (g : GL (Fin N) O) z, P (grpA O N lam (Pi.mulSingle τ g) • z) = blockSub k N
      (fun σ => ((((Pi.mulSingle τ g : ι → GL (Fin N) O) σ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (algebraMap O k)) (P z))
    (g : ι → GL (Fin N) O) (z : Gm) : P (grpA O N lam g • z) = blockSub k N
      (fun σ => (((g σ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (algebraMap O k)) (P z) := by
  let S : Submonoid (ι → GL (Fin N) O) :=
    { carrier := {g | ∀ z, P (grpA O N lam g • z) = blockSub k N
        (fun σ => (((g σ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (algebraMap O k)) (P z)}
      one_mem' := fun z => by
        have e : grpA O N lam 1 = 1 := Subtype.ext (map_one (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep O (fun _ => N) (fun _ => N) (fun τ => res N (lam τ))))
        have e' : blockSub k N (fun σ : ι => ((((1 : ι → GL (Fin N) O) σ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (algebraMap O k)) =
            AlgHom.id k _ := by
          apply MvPolynomial.algHom_ext
          intro v
          simp [blockSub, Matrix.one_apply, apply_ite (C : k →+* MvPolynomial (BVar N ι) k)]
        rw [e, e', one_smul]; rfl
      mul_mem' := fun {a b} ha hb z => by
        have e : grpA O N lam (a * b) = grpA O N lam a * grpA O N lam b :=
          Subtype.ext (map_mul (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep O (fun _ => N) (fun _ => N) (fun τ => res N (lam τ))) a b)
        rw [e, mul_smul, ha, hb, blockSub_blockSub]
        simp only [Pi.mul_apply, mul_inv_rev, Units.val_mul, Matrix.map_mul] }
  have key : ∀ s : Finset ι, (fun σ => if σ ∈ s then g σ else 1) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false]
      exact S.one_mem
    | insert τ s hτ ih =>
      have : (fun σ => if σ ∈ insert τ s then g σ else 1) = Pi.mulSingle τ (g τ) * fun σ => if σ ∈ s then g σ else 1 := by
        funext σ
        by_cases e : σ = τ
        · subst e; simp [hτ]
        · simp [e]
      rw [this]
      exact S.mul_mem (h τ (g τ)) ih
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  exact this z

end GlobalTheory.HighWtEmb

end Lemmas

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

theorem GlobalTheory.HighWtEmb.exists_coefPoly : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → ∀ (φ : Gm →+ O ⧸ Ideal.span {ϖ}) (z₀ : Gm), φ z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) → (∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0) → ∃ Pz : Gm →+ MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}), (∀ (c : O) (z : Gm), Pz (algebraMap O (alg O N lam) c • z) = C (Ideal.Quotient.mk (Ideal.span {ϖ}) c) * Pz z) ∧ (∀ (g : ι → GL (Fin N) O) (z : Gm), Pz (grpA O N lam g • z) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (Pz z)) ∧ (∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → ∀ z, Pz (a • z) = weightedHomogeneousComponent (blockW N τ) v (Pz z)) ∧ (∀ z τ, toBlock (O ⧸ Ideal.span {ϖ}) N τ (Pz z) ∈ dualWeyl (MvPolynomial (OVar N τ) (O ⧸ Ideal.span {ϖ})) N N (w τ)) ∧ Pz z₀ ≠ 0 := by
  intro O _ _ _ N ι _ _ lam ϖ _ _ hcoef Gm _ _ _ w hmax φ z₀ hz₀ _ hφ h0
  choose c hc' using hcoef
  have hc := fun τ m => eq_of_isCoef O N lam τ m _ (hc' τ m)
  let ψ : Gm →+ MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) := (C : _ →+* MvPolynomial (BVar N ι) _).toAddMonoidHom.comp φ
  have hψ : ∀ z, ψ z = C (φ z) := fun _ => rfl
  have hs : Semi O lam ψ := fun r z => by rw [hψ, hψ, hφ, map_mul]; rfl
  have h0' : ∀ τ v, v ≠ w τ → ∀ z, φ (projA O N lam τ v • z) = 0 := fun τ v hv => h0 τ v _ (isProj_projA O N lam τ v) hv
  have hg : ∀ τ, Good c τ (w τ) ψ := fun τ => ⟨hs, fun z => ⟨C (φ z), rename_C _ _⟩, fun m hm z => by
    rcases hm with hm | hm
    · rw [hψ, apply_coef_eq_zero_of_col c hc φ τ _ (h0' τ) m hm, map_zero]
    · rw [hψ, apply_coef_eq_zero_of_lt c hc φ hφ w hmax h0' τ m hm, map_zero]⟩
  obtain ⟨P, h1, h2, -, h4⟩ := exists_poly c hc w ψ hg hs Finset.univ
  refine ⟨P, h1, grp_of_single P fun τ g z => ?_, fun τ v a ha z => ?_, fun z τ => ?_, fun h => hz₀ ?_⟩
  · obtain ⟨ψ', h5, rfl⟩ := h4 τ (Finset.mem_univ _)
    exact stepT_grp_single c hc h5 g z
  · obtain ⟨ψ', h5, rfl⟩ := h4 τ (Finset.mem_univ _)
    rw [eq_projA O N lam ha]
    exact stepT_proj c hc h5 v z
  · obtain ⟨ψ', h5, rfl⟩ := h4 τ (Finset.mem_univ _)
    exact stepT_mem c hc h5 z
  · have := h2 z₀
    rwa [h, map_zero, hψ, eval_C, eq_comm] at this

end
