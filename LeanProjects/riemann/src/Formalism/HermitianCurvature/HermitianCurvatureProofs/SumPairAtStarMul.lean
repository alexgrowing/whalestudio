import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HsInnerAddSmulRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_last (μ : Measure (Mt k r)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ (Fin.last r) x y c = ∑ a, pairAt μ (x a) (y a) c := by
  have : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} := ⟨fun l => absurd l.2 (not_le.mpr l.1.isLt)⟩
  have hg : ∀ c' : Cf r (Fin.last r), glue (Fin.last r) c c' = c :=
    fun c' => funext fun l => dif_neg (not_le.mpr l.isLt)
  have hp : ∀ c' : Cf r (Fin.last r), ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) = 1 := fun c' => by
    rw [Fintype.prod_empty, Complex.ofReal_one]
  have h1 : (volume : Measure (Cf r (Fin.last r))) Set.univ = 1 := by
    rw [MeasureTheory.volume_pi, Measure.pi_univ, Fintype.prod_empty]
  unfold form
  simp only [hg, hp, one_mul]
  rw [integral_const]
  simp [measureReal_def, h1]

def IntOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) : Prop :=
  ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, Integrable (fun g : Mt k r =>
    B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ

def AdjOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (a : Pr (RadSp k r z z' π π')) : Prop :=
  (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ (∀ Φ ∈ U, a.2.unop Φ ∈ U) ∧
    ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, pairAt μ (a.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ) c

theorem hsInner_swap (A C : Wq →L[ℂ] Wp) : B.hsInner C A = conj (B.hsInner A C) := by
  simp only [B.hsInner]
  rw [inner_conj_symm]

private theorem hsVec_zero_hermitian_curvature : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  ext i
  simp [B.hsVec]

theorem hsInner_zero_left (C : Wq →L[ℂ] Wp) : B.hsInner 0 C = 0 := by
  simp only [B.hsInner, hsVec_zero_hermitian_curvature, inner_zero_right]

private theorem hsVec_smul_hermitian_curvature' (a : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (a • A) = a • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem hsInner_smul_left' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner (a • A) C = a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_right]

theorem hsInner_smul_right' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_left]

theorem pairAt_swap (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Ψ Φ c = conj (pairAt μ Φ Ψ c) := by
  simp only [pairAt]
  rw [← integral_conj]
  congr 1
  funext g
  exact hsInner_swap _ _

theorem pairAt_smul_left (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ (a • Φ) Ψ c = a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_left']
  exact integral_const_mul a _

theorem pairAt_smul_right (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ Φ (a • Ψ) c = conj a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_right']
  exact integral_const_mul _ _

variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}

private theorem hsInner_add_left' (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_right]

theorem pairAt_add_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Φ' Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΦ' : Φ' ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (Φ + Φ') Ψ c = pairAt μ Φ Ψ c + pairAt μ Φ' Ψ c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_left']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ' hΦ' Ψ hΨ)

private theorem hsInner_add_right' (A C C' : Wq →L[ℂ] Wp) :
    B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_left]

theorem pairAt_add_right (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Ψ Ψ' : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) (hΨ' : Ψ' ∈ U) :
    pairAt μ Φ (Ψ + Ψ') c = pairAt μ Φ Ψ c + pairAt μ Φ Ψ' c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_right']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ hΦ Ψ' hΨ')

private theorem pairAt_zero_left' (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairAt μ 0 Ψ c = 0 := by
  simp only [pairAt, Submodule.coe_zero, Pi.zero_apply, hsInner_zero_left, integral_zero]

theorem pairAt_sum_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    (Φ : ι → RadSp k r z z' π π') (hΦ : ∀ i, Φ i ∈ U) {Ψ : RadSp k r z z' π π'} (hΨ : Ψ ∈ U) :
    pairAt μ (∑ i ∈ s, Φ i) Ψ c = ∑ i ∈ s, pairAt μ (Φ i) Ψ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairAt_zero_left']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      pairAt_add_left hU hc (hΦ j) (U.sum_mem fun i _ => hΦ i) hΨ, ih]

private theorem pairAt_zero_right' (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairAt μ Φ 0 c = 0 := by
  rw [pairAt_swap, pairAt_zero_left', map_zero]

theorem pairAt_sum_right (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    {Φ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (Ψ : ι → RadSp k r z z' π π') (hΨ : ∀ i, Ψ i ∈ U) :
    pairAt μ Φ (∑ i ∈ s, Ψ i) c = ∑ i ∈ s, pairAt μ Φ (Ψ i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairAt_zero_right']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      pairAt_add_right hU hc hΦ (hΨ j) (U.sum_mem fun i _ => hΨ i), ih]

theorem pr_alg_fst (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).1 = algebraMap ℂ _ a := rfl

theorem pr_alg_snd (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).2.unop = algebraMap ℂ _ (conj a) := rfl

def adjAlg (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (hU : IntOn μ U) :
    StarSubalgebra ℂ (Pr (RadSp k r z z' π π')) where
  carrier := {a | AdjOn μ U a}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ), fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 (b.1 Φ)) Ψ c = pairAt μ Φ (b.2.unop (a.2.unop Ψ)) c
    rw [ha c hc _ (hb1 Φ hΦ) Ψ hΨ, hb c hc Φ hΦ _ (ha2 Ψ hΨ)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ),
      fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 Φ + b.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ + b.2.unop Ψ) c
    rw [pairAt_add_left hU hc (ha1 Φ hΦ) (hb1 Φ hΦ) hΨ, pairAt_add_right hU hc hΦ (ha2 Ψ hΨ) (hb2 Ψ hΨ),
      ha c hc Φ hΦ Ψ hΨ, hb c hc Φ hΦ Ψ hΨ]
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    · rw [pr_alg_fst, Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · rw [pr_alg_snd, Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
    · rw [pr_alg_fst, pr_alg_snd, Module.algebraMap_end_apply, Module.algebraMap_end_apply, pairAt_smul_left,
        pairAt_smul_right, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c
    rw [pairAt_swap μ Ψ, ← ha c hc Ψ hΨ Φ hΦ, ← pairAt_swap]

theorem mem_adjAlg {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} : a ∈ adjAlg μ U hU ↔ AdjOn μ U a := by
  exact Iff.rfl

theorem pairAt_snd_left {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} (ha : a ∈ adjAlg μ U hU) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {Φ Ψ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c := by
  have h := (mem_adjAlg.mp ha).2.2 c hc Ψ hΨ Φ hΦ
  rw [pairAt_swap μ Ψ (a.2.unop Φ) c, ← h]
  exact (pairAt_swap μ (a.1 Ψ) Φ c).symm

theorem act_mem {hU : IntOn μ U} (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := by
  show (∑ b, (M a b).1 (x b)) ∈ U
  exact U.sum_mem fun b _ => (mem_adjAlg.mp (hM a b)).1 _ (hx b)

theorem mul_mem_entries {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (hN : ∀ a b, N a b ∈ adjAlg μ U hU) (a b : Ix S) : (M * N) a b ∈ adjAlg μ U hU := by
  rw [Matrix.mul_apply]
  exact sum_mem fun e _ => mul_mem (hM a e) (hN e b)

theorem sum_pairAt_star_mul {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')))
    (hM : ∀ a b, M a b ∈ adjAlg μ U hU) (hN : ∀ a b, N a b ∈ adjAlg μ U hU)
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (hy : ∀ a, y a ∈ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∑ a, pairAt μ (act (star M * N) x a) (y a) c = ∑ e, pairAt μ (act N x e) (act M y e) c := by
  have hu : ∀ e, act N x e ∈ U := act_mem N hN x hx
  have hL : ∀ a, act (star M * N) x a = ∑ e, (M e a).2.unop (act N x e) := by
    intro a
    rw [act_mul]
    rfl
  calc ∑ a, pairAt μ (act (star M * N) x a) (y a) c
      = ∑ a, ∑ e, pairAt μ (act N x e) ((M e a).1 (y a)) c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hL a, pairAt_sum_left hU hc _ _ (fun e => (mem_adjAlg.mp (hM e a)).2.1 _ (hu e)) (hy a)]
        exact Finset.sum_congr rfl fun e _ => pairAt_snd_left (hM e a) hc (hu e) (hy a)
    _ = ∑ e, ∑ a, pairAt μ (act N x e) ((M e a).1 (y a)) c := Finset.sum_comm
    _ = ∑ e, pairAt μ (act N x e) (act M y e) c := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact (pairAt_sum_right hU hc _ (hu e) _ (fun a => (mem_adjAlg.mp (hM e a)).1 _ (hy a))).symm

end Gen

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_adjAlg (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hF : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ e e',
      (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU ∧ (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  intro w hw x y hx hy c hc
  have hFF : ∀ e e', (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').1
  have hFd : ∀ e e', (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').2
  have hxU : ∀ a, x a ∈ U := fun a => hK (hx a)
  have hyU : ∀ a, y a ∈ U := fun a => hK (hy a)
  have hDF := mul_mem_entries _ _ hFd hFF
  have hu := act_mem _ hDF x hxU
  have hv := act_mem _ hFF y hyU
  have hint := fun e => hU c hc _ (hu e) _ (hv e)
  refine ⟨?_, ?_⟩
  · simp only [topDens]
    exact integrable_finsetSum Finset.univ fun e _ => hint e
  · rw [form_last, mul_assoc, sum_pairAt_star_mul _ _ hFF hDF x y hxU hyU hc]
    simp only [topDens]
    rw [integral_finsetSum Finset.univ fun e _ => hint e]
    rfl

end Top

end Formalism.FourierDecayAlt.P5.HerA
