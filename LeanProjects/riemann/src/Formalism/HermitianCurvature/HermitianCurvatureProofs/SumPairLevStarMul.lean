import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

def pairLev (μ : Measure (Mt k r)) (i : Fin (r + 1)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c')

variable {μ : Measure (Mt k r)} {i : Fin (r + 1)} {U : Submodule ℂ (RadSp k r z z' π π')}

theorem pairLev_swap (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairLev μ i Ψ Φ c = conj (pairLev μ i Φ Ψ c) := by
  unfold pairLev
  rw [← integral_conj]
  congr 1
  funext c'
  rw [pairAt_swap, map_mul, Complex.conj_ofReal]

theorem pairLev_smul_left (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairLev μ i (a • Φ) Ψ c = a * pairLev μ i Φ Ψ c := by
  unfold pairLev
  rw [← integral_const_mul]
  congr 1
  funext c'
  rw [pairAt_smul_left]
  ring

theorem pairLev_smul_right (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairLev μ i Φ (a • Ψ) c = conj a * pairLev μ i Φ Ψ c := by
  unfold pairLev
  rw [← integral_const_mul]
  congr 1
  funext c'
  rw [pairAt_smul_right]
  ring

theorem pairLev_add_left (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Φ' Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΦ' : Φ' ∈ U) (hΨ : Ψ ∈ U) :
    pairLev μ i (Φ + Φ') Ψ c = pairLev μ i Φ Ψ c + pairLev μ i Φ' Ψ c := by
  unfold pairLev
  rw [← integral_add (hI c hc Φ hΦ Ψ hΨ).2 (hI c hc Φ' hΦ' Ψ hΨ).2]
  congr 1
  funext c'
  have := pairAt_add_smul_left μ Φ Φ' Ψ (glue i c c') 1 ((hI c hc Φ hΦ Ψ hΨ).1 c') ((hI c hc Φ' hΦ' Ψ hΨ).1 c')
  rw [one_smul, one_mul] at this
  rw [this, mul_add]

theorem pairLev_add_right (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Ψ Ψ' : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) (hΨ' : Ψ' ∈ U) :
    pairLev μ i Φ (Ψ + Ψ') c = pairLev μ i Φ Ψ c + pairLev μ i Φ Ψ' c := by
  rw [pairLev_swap, pairLev_add_left hI hc hΨ hΨ' hΦ, map_add, ← pairLev_swap, ← pairLev_swap]

theorem pairLev_zero_left (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairLev μ i 0 Ψ c = 0 := by
  unfold pairLev
  have h0 : ∀ c', pairAt μ (0 : RadSp k r z z' π π') Ψ c' = 0 := fun c' => by
    have := pairAt_smul_left μ (0 : RadSp k r z z' π π') Ψ c' 0
    rwa [zero_smul, zero_mul] at this
  simp [h0]

theorem pairLev_sum_left (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    (Φ : ι → RadSp k r z z' π π') (hΦ : ∀ j, Φ j ∈ U) {Ψ : RadSp k r z z' π π'} (hΨ : Ψ ∈ U) :
    pairLev μ i (∑ j ∈ s, Φ j) Ψ c = ∑ j ∈ s, pairLev μ i (Φ j) Ψ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact pairLev_zero_left Ψ c
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, pairLev_add_left hI hc (hΦ j) (U.sum_mem fun j' _ => hΦ j') hΨ,
      ih]

theorem pairLev_sum_right (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    {Φ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (Ψ : ι → RadSp k r z z' π π') (hΨ : ∀ j, Ψ j ∈ U) :
    pairLev μ i Φ (∑ j ∈ s, Ψ j) c = ∑ j ∈ s, pairLev μ i Φ (Ψ j) c := by
  rw [pairLev_swap, pairLev_sum_left hI hc s Ψ hΨ hΦ, map_sum]
  exact Finset.sum_congr rfl fun j _ => (pairLev_swap (μ := μ) (i := i) (Ψ j) Φ c).symm

def adjLev (μ : Measure (Mt k r)) (i : Fin (r + 1)) (U : Submodule ℂ (RadSp k r z z' π π')) (hI : IntLevOn μ i U)
    (c : Fin r → ℂ) (hc : c ∈ OmX r) : StarSubalgebra ℂ (Pr (RadSp k r z z' π π')) where
  carrier := {a | (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ (∀ Φ ∈ U, a.2.unop Φ ∈ U) ∧
    ∀ Φ ∈ U, ∀ Ψ ∈ U, pairLev μ i (a.1 Φ) Ψ c = pairLev μ i Φ (a.2.unop Ψ) c}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ), fun Φ hΦ Ψ hΨ => ?_⟩
    change pairLev μ i (a.1 (b.1 Φ)) Ψ c = pairLev μ i Φ (b.2.unop (a.2.unop Ψ)) c
    rw [ha _ (hb1 Φ hΦ) Ψ hΨ, hb Φ hΦ _ (ha2 Ψ hΨ)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ),
      fun Φ hΦ Ψ hΨ => ?_⟩
    change pairLev μ i (a.1 Φ + b.1 Φ) Ψ c = pairLev μ i Φ (a.2.unop Ψ + b.2.unop Ψ) c
    rw [pairLev_add_left hI hc (ha1 Φ hΦ) (hb1 Φ hΦ) hΨ, pairLev_add_right hI hc hΦ (ha2 Ψ hΨ) (hb2 Ψ hΨ),
      ha Φ hΦ Ψ hΨ, hb Φ hΦ Ψ hΨ]
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun Φ _ Ψ _ => ?_⟩
    · rw [pr_alg_fst, Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · rw [pr_alg_snd, Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
    · rw [pr_alg_fst, pr_alg_snd, Module.algebraMap_end_apply, Module.algebraMap_end_apply, pairLev_smul_left,
        pairLev_smul_right, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun Φ hΦ Ψ hΨ => ?_⟩
    change pairLev μ i (a.2.unop Φ) Ψ c = pairLev μ i Φ (a.1 Ψ) c
    rw [pairLev_swap (Φ := Ψ), ← ha Ψ hΨ Φ hΦ, ← pairLev_swap]

theorem adjLev_pres {hI : IntLevOn μ i U} {c : Fin r → ℂ} {hc : c ∈ OmX r} {a : Pr (RadSp k r z z' π π')}
    (ha : a ∈ adjLev μ i U hI c hc) : a ∈ presAlg U := ⟨ha.1, ha.2.1⟩

theorem act_mem_pres (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ presAlg U)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := U.sum_mem fun b _ => (hM a b).1 _ (hx b)

theorem mul_mem_pres (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ presAlg U)
    (hN : ∀ a b, N a b ∈ presAlg U) (a b : Ix S) : (M * N) a b ∈ presAlg U := by
  rw [Matrix.mul_apply]
  exact (presAlg U).sum_mem fun c _ => (presAlg U).mul_mem (hM a c) (hN c b)

theorem star_mem_pres (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ presAlg U) (a b : Ix S) :
    (star M) a b ∈ presAlg U := by
  rw [Matrix.star_apply]
  exact star_mem (hM b a)

theorem form_eq_sum (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ U) (hv : ∀ a, v a ∈ U) : form μ i u v c = ∑ a, pairLev μ i (u a) (v a) c := by
  unfold form pairLev
  simp only [Finset.mul_sum]
  exact integral_finsetSum _ fun a _ => (hI c hc _ (hu a) _ (hv a)).2

theorem form_int (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ U) (hv : ∀ a, v a ∈ U) :
    Integrable (fun c' : Cf r i => ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (u a) (v a) (glue i c c')) := by
  simp only [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => (hI c hc _ (hu a) _ (hv a)).2

theorem sum_pairLev_star_mul (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjLev μ i U hI c hc)
    (hN : ∀ a b, N a b ∈ presAlg U) (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (hy : ∀ a, y a ∈ U) :
    ∑ a, pairLev μ i (act (star M * N) x a) (y a) c = ∑ e, pairLev μ i (act N x e) (act M y e) c := by
  have hu : ∀ e, act N x e ∈ U := act_mem_pres N hN x hx
  rw [act_mul]
  have h1 : ∀ a, act (star M) (act N x) a = ∑ e, (M e a).2.unop (act N x e) := by
    intro a
    simp only [act, Matrix.star_apply]
    rfl
  simp only [h1]
  rw [Finset.sum_congr rfl fun a _ =>
    pairLev_sum_left hI hc Finset.univ _ (fun e => (hM e a).2.1 _ (hu e)) (hy a)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hs : ∀ a, pairLev μ i ((M e a).2.unop (act N x e)) (y a) c = pairLev μ i (act N x e) ((M e a).1 (y a)) c :=
    fun a => (star_mem (hM e a) : star (M e a) ∈ adjLev μ i U hI c hc).2.2 _ (hu e) _ (hy a)
  rw [Finset.sum_congr rfl fun a _ => hs a]
  rw [← pairLev_sum_right hI hc Finset.univ (hu e) _ fun a => (hM e a).1 _ (hy a)]
  rfl

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem stepDens_of (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Fin P.r → Submodule ℂ (RadSp P.k P.r z z' π π')) (hKU : ∀ l, K l.castSucc ≤ U l)
    (hI : ∀ l, IntLevOn μ l.castSucc (U l))
    (hSite : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ l : Fin P.r,
      star (bTl L l w) * RRi L st l.succ w * bTl L l w = RRi L st l.castSucc w)
    (hB : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r),
      ∀ a b, bTl L l w a b ∈ adjLev μ l.castSucc (U l) (hI l) c hc)
    (hR : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) a b,
      RRi L st l.succ w a b ∈ presAlg (U l))
    (hPh : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
      ∃ φ : ℂ → ℂ, Continuous φ ∧ (∀ t, t ≠ 0 → φ t = ph L st μ l w x y c t) ∧
        ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) :
    StepDens (S := S) P z z' π π' μ L st K l0 := by
  intro w hw l x y hx hy c hc
  obtain ⟨φ, hφc, hφe, hC⟩ := hPh w hw l x y hx hy c hc
  refine ⟨φ, hφc, hφe, hC, ?_⟩
  have h1 : ∫ t, φ t = ∫ t, ph L st μ l w x y c t := integral_congr_ae (ae_complex_ne_zero.mono fun t ht => hφe t ht)
  rw [h1]
  have hxU : ∀ a, x a ∈ U l := fun a => hKU l (hx a)
  have hyU : ∀ a, y a ∈ U l := fun a => hKU l (hy a)
  have hBm : ∀ a b, bTl L l w a b ∈ adjLev μ l.castSucc (U l) (hI l) c hc := hB w hw l c hc
  have hBp : ∀ a b, bTl L l w a b ∈ presAlg (U l) := fun a b => adjLev_pres (hBm a b)
  have hN : ∀ a b, (RRi L st l.succ w * bTl L l w) a b ∈ presAlg (U l) := mul_mem_pres _ _ (hR w hw l) hBp
  have hRR : RRi L st l.castSucc w = star (bTl L l w) * (RRi L st l.succ w * bTl L l w) := by
    rw [← hSite w hw l, mul_assoc]
  have hu : ∀ e, act (RRi L st l.succ w * bTl L l w) x e ∈ U l := act_mem_pres _ hN x hxU
  have hv : ∀ e, act (bTl L l w) y e ∈ U l := act_mem_pres _ hBp y hyU
  have hu0 : ∀ a, act (RRi L st l.castSucc w) x a ∈ U l := by
    rw [hRR]; exact act_mem_pres _ (mul_mem_pres _ _ (star_mem_pres _ hBp) hN) x hxU
  symm
  show form μ l.castSucc (act (RRi L st l.castSucc w) x) y c = _
  rw [form_eq_sum (hI l) hc _ _ hu0 hyU]
  simp only [hRR]
  rw [sum_pairLev_star_mul (hI l) hc _ _ hBm hN x y hxU hyU, ← form_eq_sum (hI l) hc _ _ hu hv,
    form_split μ l _ _ c (form_int (hI l) hc _ _ hu hv)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ (act (RRi L st l.succ w) (act (bTl L l w) x))
    (act (bTl L l w) y) (Function.update c l t)
  rw [act_mul]

end Top

end Formalism.FourierDecayAlt.P5.HerA
