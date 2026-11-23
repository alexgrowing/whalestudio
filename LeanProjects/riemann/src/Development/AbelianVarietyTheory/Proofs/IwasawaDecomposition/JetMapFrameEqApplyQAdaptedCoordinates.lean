import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open Classical

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.JetChain

def fpair {σ K : Type} [CommRing K] (Q : MvPolynomial σ K) (F : MvPowerSeries σ K) : K :=
  ∑ α ∈ Q.support, MvPolynomial.coeff α Q * (α.prod fun _ n => (n.factorial : K)) * MvPowerSeries.coeff α F

section Pair

variable {σ K : Type} [CommRing K]

theorem fpair_eq_of_subset (Q : MvPolynomial σ K) (F : MvPowerSeries σ K) (s : Finset (σ →₀ ℕ)) (hs : Q.support ⊆ s) :
    fpair Q F = ∑ α ∈ s, MvPolynomial.coeff α Q * (α.prod fun _ n => (n.factorial : K)) * MvPowerSeries.coeff α F := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hα
  rw [hα, zero_mul, zero_mul]

theorem fpair_add_left (Q₁ Q₂ : MvPolynomial σ K) (F : MvPowerSeries σ K) :
    fpair (Q₁ + Q₂) F = fpair Q₁ F + fpair Q₂ F := by
  classical
  rw [fpair_eq_of_subset (Q₁ + Q₂) F _ MvPolynomial.support_add,
    fpair_eq_of_subset Q₁ F _ Finset.subset_union_left, fpair_eq_of_subset Q₂ F _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fpair_zero_left (F : MvPowerSeries σ K) : fpair (0 : MvPolynomial σ K) F = 0 := by
  simp [fpair]

theorem fpair_monomial (α : σ →₀ ℕ) (c : K) (F : MvPowerSeries σ K) :
    fpair (MvPolynomial.monomial α c) F = c * (α.prod fun _ n => (n.factorial : K)) * MvPowerSeries.coeff α F := by
  classical
  rw [fpair_eq_of_subset _ F {α} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem fpair_smul_left (r : K) (Q : MvPolynomial σ K) (F : MvPowerSeries σ K) :
    fpair (r • Q) F = r * fpair Q F := by
  induction Q using MvPolynomial.induction_on' with
  | monomial α c => rw [MvPolynomial.smul_monomial, fpair_monomial, fpair_monomial, smul_eq_mul]; ring
  | add p q hp hq => rw [smul_add, fpair_add_left, fpair_add_left, hp, hq, mul_add]

theorem fpair_C_mul (r : K) (Q : MvPolynomial σ K) (F : MvPowerSeries σ K) :
    fpair (MvPolynomial.C r * Q) F = r * fpair Q F := by
  rw [← MvPolynomial.smul_eq_C_mul, fpair_smul_left]

theorem fpair_sum_left {ι : Type} (s : Finset ι) (Q : ι → MvPolynomial σ K) (F : MvPowerSeries σ K) :
    fpair (∑ i ∈ s, Q i) F = ∑ i ∈ s, fpair (Q i) F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fpair_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fpair_add_left, ih]

theorem fpair_sum_right {ι : Type} (s : Finset ι) (Q : MvPolynomial σ K) (F : ι → MvPowerSeries σ K) :
    fpair Q (∑ i ∈ s, F i) = ∑ i ∈ s, fpair Q (F i) := by
  simp only [fpair, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem fpair_mul_C_right (Q : MvPolynomial σ K) (F : MvPowerSeries σ K) (r : K) :
    fpair Q (F * MvPowerSeries.C r) = fpair Q F * r := by
  simp only [fpair, MvPowerSeries.coeff_mul_C, Finset.sum_mul, mul_assoc]

theorem fpair_C (r : K) (F : MvPowerSeries σ K) :
    fpair (MvPolynomial.C r) F = r * MvPowerSeries.constantCoeff F := by
  rw [← MvPolynomial.monomial_zero', fpair_monomial]
  simp

theorem prod_factorial_add_single [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (j : σ) :
    ((α + Finsupp.single j 1).prod fun _ n => (n.factorial : K)) =
      (α.prod fun _ n => (n.factorial : K)) * ((α j : K) + 1) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h : ∀ i, ((((α + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : ℕ) : K) =
      ((α i).factorial : K) * (if i = j then (α j : K) + 1 else 1) := by
    intro i
    by_cases hi : i = j
    · subst hi
      simp [Nat.factorial_succ]
      ring
    · simp [Finsupp.single_apply, Ne.symm hi, hi]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem fpair_mul_X [Fintype σ] [DecidableEq σ] (Q : MvPolynomial σ K) (j : σ) (F : MvPowerSeries σ K) :
    fpair (Q * MvPolynomial.X j) F = fpair Q (MvPowerSeries.pderiv K j F) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, fpair_monomial, fpair_monomial,
      MvPowerSeries.coeff_pderiv, prod_factorial_add_single]
    ring
  | add p q hp hq => rw [add_mul, fpair_add_left, fpair_add_left, hp, hq]

end Pair

section Chain

variable {σ κ K : Type} [CommRing K] [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]

def linS (c : σ → κ → K) (k : σ) : MvPowerSeries κ K :=
  ∑ j : κ, algebraMap K (MvPowerSeries κ K) (c k j) * MvPowerSeries.X j

theorem constantCoeff_linS (c : σ → κ → K) (k : σ) : MvPowerSeries.constantCoeff (linS c k) = 0 := by
  simp [linS, map_sum]

theorem hasSubst_linS (c : σ → κ → K) : MvPowerSeries.HasSubst (linS c) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_linS c)

theorem pderiv_linS (c : σ → κ → K) (k : σ) (j : κ) :
    MvPowerSeries.pderiv K j (linS c k) = MvPowerSeries.C (c k j) := by
  unfold linS
  rw [map_sum, Finset.sum_eq_single j]
  · rw [Derivation.leibniz, MvPowerSeries.pderiv_X_self, Derivation.map_algebraMap, smul_zero, add_zero, smul_eq_mul,
      mul_one, MvPowerSeries.c_eq_algebraMap]
  · intro i _ hi
    rw [Derivation.leibniz, MvPowerSeries.pderiv_X_of_ne hi, Derivation.map_algebraMap, smul_zero, smul_zero,
      add_zero]
  · simp

theorem constantCoeff_subst_linS (c : σ → κ → K) (F : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst (linS c) F) = MvPowerSeries.constantCoeff F := by
  have hs := hasSubst_linS c
  have e : F = algebraMap K (MvPowerSeries σ K) (MvPowerSeries.constantCoeff F) +
      (F - algebraMap K (MvPowerSeries σ K) (MvPowerSeries.constantCoeff F)) := by ring
  have h0 : MvPowerSeries.constantCoeff (F - algebraMap K (MvPowerSeries σ K) (MvPowerSeries.constantCoeff F)) = 0 := by
    rw [← MvPowerSeries.c_eq_algebraMap, map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h1 := MvPowerSeries.constantCoeff_subst_eq_zero hs (constantCoeff_linS c) h0
  rw [← MvPowerSeries.coe_substAlgHom hs] at h1 ⊢
  conv_lhs => rw [e, map_add, AlgHom.commutes]
  rw [map_add, h1, add_zero, ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.constantCoeff_C]

theorem fpair_subst_linS (c : σ → κ → K) (Q : MvPolynomial κ K) (F : MvPowerSeries σ K) :
    fpair Q (MvPowerSeries.subst (linS c) F) =
      fpair (MvPolynomial.aeval (fun j : κ => ∑ k : σ, MvPolynomial.C (c k j) * MvPolynomial.X k) Q) F := by
  induction Q using MvPolynomial.induction_on generalizing F with
  | C r => rw [MvPolynomial.aeval_C, fpair_C, MvPolynomial.algebraMap_eq, fpair_C, constantCoeff_subst_linS]
  | add p q hp hq => rw [fpair_add_left, hp, hq, map_add, fpair_add_left]
  | mul_X p j ih =>
    rw [fpair_mul_X, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.pderiv_subst (hasSubst_linS c), fpair_sum_right]
    simp_rw [pderiv_linS, fpair_mul_C_right, ih, ← fpair_mul_X]
    rw [map_mul, MvPolynomial.aeval_X, Finset.mul_sum, fpair_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm _ (MvPolynomial.C _), mul_assoc, fpair_C_mul, mul_comm]

end Chain

end GlobalTheory.JetChain

namespace GlobalTheory.JetChain

section Jet

open Formalism.L2.Ker

theorem eval_jetLin {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {a b : ℕ}
    (y : ι × Fin b × Fin b → K) (sc : ι → K) (T : MvPowerSeries (DVar ι a b) K)
    (R : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    MvPolynomial.eval y (jetLin (fun m => (m.prod fun k n => sc k.1 ^ n) * (m.prod fun _ n => (n.factorial : K)) *
        MvPowerSeries.coeff m T) R) =
      fpair (MvPolynomial.aeval (Sum.elim (fun v => MvPolynomial.C (y v))
        (fun d => MvPolynomial.C (sc d.1) * MvPolynomial.X d)) R) T := by
  induction R using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, fpair_add_left]
  | monomial m c =>
    have hb : MvPolynomial.monomial m c = c • (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) m := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hX : (∏ d : DVar ι a b, (MvPolynomial.X d : MvPolynomial (DVar ι a b) K) ^ (m (Sum.inr d))) =
        MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1 := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_pow]
      rfl
    rw [hb, map_smul, jetLin, Module.Basis.constr_basis, MvPolynomial.smul_eval, MvPolynomial.eval_monomial, ← hb,
      MvPolynomial.aeval_monomial]
    simp only [Finsupp.prod_pow, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_pow, Finset.prod_mul_distrib,
      hX, ← map_pow, ← map_prod]
    rw [MvPolynomial.algebraMap_eq, fpair_C_mul, fpair_C_mul, fpair_C_mul, fpair_monomial]
    simp only [Finsupp.comapDomain_apply]
    ring

end Jet

end GlobalTheory.JetChain

namespace GlobalTheory.JetChain

theorem aeval_aeval' {R σ τ υ : Type} [CommSemiring R] (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (P : MvPolynomial σ R) :
    MvPolynomial.aeval g (MvPolynomial.aeval f P) = MvPolynomial.aeval (fun i => MvPolynomial.aeval g (f i)) P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]

theorem applyQ_eq {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) :
    GL3Columns.applyQ l N0 N1 Th Q y' = fpair (MvPolynomial.aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      MvPolynomial.C (y' v.1 b v.2.2) * MvPolynomial.X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q) Th := rfl

theorem atLin_eq {σ κ : Type} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ] {p : ℕ} [Fact p.Prime]
    (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    atLin c (fun j => MvPowerSeries.X j) F = MvPowerSeries.subst (linS c) F := rfl

theorem sum_sel {T K : Type} [Fintype T] [AddCommMonoid K] {N1 N0 : ℕ} (τ : T) (F : T × Fin N1 × Fin N0 → K) :
    ∑ k : T × Fin N1 × Fin N0, (if τ = k.1 then F k else 0) = ∑ β : Fin N1, ∑ α' : Fin N0, F (τ, β, α') := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · simp [Fintype.sum_prod_type]
  · intro t _ ht
    exact Finset.sum_eq_zero fun k _ => if_neg (Ne.symm ht)
  · simp

theorem sum4 {A B C E M : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] [AddCommMonoid M]
    (f : A → B → C → E → M) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ a, ∑ c, ∑ e, ∑ b, f a b c e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => Finset.sum_comm

theorem jetMap_frame_eq_applyQ : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1)
    (T : MvPowerSeries (D.what₂.Tau × Fin N1 × Fin N0) ℂ_[p]) (s : D.what₂.Tau → ℂ_[p])
    (B : D.what₂.Tau → Matrix (Fin N0) (Fin N0) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p])
    (hB : ∀ τ, (B τ).det ≠ 0) (P : MvPolynomial (GL3Theta.FrV D N0) ℂ_[p]) (y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p]), MvPolynomial.eval (fun k : GL3Theta.FrV D N1 => (B' k.1 * y' k.1) k.2.1 k.2.2)
      (jetMap (fun m => (m.prod fun k n => s k.1 ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m T)
        (fun _ => 0) P) =
    GL3Columns.applyQ p N0 N1
      (atLin (fun (k : D.what₂.Tau × Fin N1 × Fin N0) (j : (Bool × HH D) × Fin N0 × Fin N1) =>
          if tauPl D j.1 = k.1 then 1 * s k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0)
        (fun j => MvPowerSeries.X j) T)
      (MvPolynomial.aeval (fun k : GL3Theta.FrV D N0 => ∑ a : Fin N0,
          MvPolynomial.C (B k.1 k.2.1 a) * MvPolynomial.X ((Equiv.ofBijective (tauPl D) (tauPl_bij D)).symm k.1, a, (k.2.2 : ℕ))) P)
      (fun z => GL3Columns.colsOf (y' (tauPl D z))) := by
  intro D p _ N0 N1 hN T s B B' hB P y'
  have hJ : ∀ (J : (DVar D.what₂.Tau N0 N1 →₀ ℕ) → ℂ_[p]), jetMap J (fun _ => 0) P =
      jetLin J (subD ℂ_[p] D.what₂.Tau N0 N1 P) := by
    intro J
    simp only [jetMap, LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one,
      AlgHom.toLinearMap_apply]
  rw [hJ, eval_jetLin (y := fun k => (B' k.1 * y' k.1) k.2.1 k.2.2) (sc := s) (T := T), applyQ_eq, atLin_eq,
    fpair_subst_linS, subD, aeval_aeval', aeval_aeval', aeval_aeval']
  refine congrArg (fun Q => fpair Q T) (congrArg (fun f => MvPolynomial.aeval f P) (funext fun v => ?_))
  obtain ⟨τ, α, t⟩ := v
  have ht : (t : ℕ) < N1 := lt_of_lt_of_le t.2 hN
  have he : tauPl D ((Equiv.ofBijective (tauPl D) (tauPl_bij D)).symm τ) = τ :=
    (Equiv.ofBijective (tauPl D) (tauPl_bij D)).apply_symm_apply τ
  simp only [dif_pos ht, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    Sum.elim_inl, Sum.elim_inr, he, GL3Columns.colsOf]
  have hC : ∀ (c : Prop) [Decidable c] (x : ℂ_[p]) (k : D.what₂.Tau × Fin N1 × Fin N0),
      MvPolynomial.C (if c then x else 0) * MvPolynomial.X k = if c then MvPolynomial.C x * MvPolynomial.X k else 0 := by
    intros c _ x k
    split_ifs <;> simp
  have hBB : ∀ α' : Fin N0, ∑ a : Fin N0, B τ α a * (B τ)⁻¹ a α' = if α = α' then 1 else 0 := by
    intro α'
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hB τ)), Matrix.one_apply]
  simp only [hC, sum_sel, Finset.mul_sum]
  rw [sum4]
  refine Finset.sum_congr rfl fun β _ => ?_
  have key : ∀ α' : Fin N0, ∑ b : Fin N1, ∑ a : Fin N0, MvPolynomial.C (B τ α a) * (MvPolynomial.C (y' τ b ⟨t, ht⟩) *
      (MvPolynomial.C (1 * s τ * B' τ β b * (B τ)⁻¹ a α') * MvPolynomial.X (τ, β, α'))) =
      MvPolynomial.C (s τ * (B' τ * y' τ) β ⟨t, ht⟩ * (if α = α' then 1 else 0)) * MvPolynomial.X (τ, β, α') := by
    intro α'
    have e1 : ∀ (b : Fin N1) (a : Fin N0), MvPolynomial.C (B τ α a) * (MvPolynomial.C (y' τ b ⟨t, ht⟩) *
        (MvPolynomial.C (1 * s τ * B' τ β b * (B τ)⁻¹ a α') * MvPolynomial.X (τ, β, α'))) =
        MvPolynomial.C (B τ α a * (y' τ b ⟨t, ht⟩ * (1 * s τ * B' τ β b * (B τ)⁻¹ a α'))) *
          (MvPolynomial.X (τ, β, α') : MvPolynomial (D.what₂.Tau × Fin N1 × Fin N0) ℂ_[p]) := by
      intro b a
      simp only [map_mul]
      ring
    simp only [e1, ← Finset.sum_mul, ← map_sum]
    congr 2
    rw [Matrix.mul_apply, ← hBB α']
    simp only [Finset.mul_sum, Finset.sum_mul]
    first
      | exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
      | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring)
  simp only [key]
  simp only [mul_ite, mul_one, mul_zero, hC, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
  ring

end GlobalTheory.JetChain
