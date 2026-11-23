import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def orderZeroDifferentialOperator (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (c ca : Coef S v)
    (hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) :
    B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) :=
  [⟨c, ca, [], fun X hX => by simp at hX, hadj⟩]

variable {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {c ca : Coef S v}
  {hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')}

theorem order_zero_operator_apply (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opApply (orderZeroDifferentialOperator S v c ca hadj) J = fun g => c g (J g) := by
  funext g
  simp only [B.opApply, orderZeroDifferentialOperator, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  first
    | rfl
    | simp [B.Rw]

theorem order_zero_operator_adjoint (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opAdj (orderZeroDifferentialOperator S v c ca hadj) J = fun g => ca g (J g) := by
  funext g
  first
    | (simp [B.opAdj, orderZeroDifferentialOperator]; done)
    | (simp [B.opAdj, orderZeroDifferentialOperator]; rfl)
    | rfl

theorem order_zero_operator_order : B.opOrder (orderZeroDifferentialOperator S v c ca hadj) = 0 := by
  first
    | rfl
    | simp [B.opOrder, orderZeroDifferentialOperator]

end gen

section eqv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}

theorem eqv_left {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (n * g) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm n⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) :=
    ⟨by simpa using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa using WeylGroupFacts.mem_n_inv hn,
      by simpa using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa using WeylGroupFacts.mem_n_one⟩
  have h := he _ hp g hg X
  have hu : IsUnit n.det := WeylGroupFacts.isUnit_of_uh hn.1
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.nonsing_inv_nonsing_inv n hu, Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_right {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (g * n) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm n)) :=
    ⟨by simpa using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa using WeylGroupFacts.mem_n_one,
      by simpa using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa using hn⟩
  have h := he _ hp g hg X
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_uw {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {h h' : B.Mat S.G.k S.G.r} (hh : h ∈ UWset S.G.k S.G.r (T v).base.z) (hh' : h' ∈ UWset S.G.k S.G.r (T v).base.z')
    (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (h * g * h') (((T v).base.π h).comp (X.comp ((T v).base.π' h'))) =
      ((T v).base.π h).comp ((c g X).comp ((T v).base.π' h')) := by
  have hp : (T v).base.inSS ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) :=
    ⟨by simpa using hh, by simpa using WeylGroupFacts.mem_n_one,
      by simpa using P.BigCellInversePair.uw_inv hh', by simpa using WeylGroupFacts.mem_n_one⟩
  have hg' : h * g * h' ∈ B.GV S.G.k S.G.r := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hh.1 hg) hh'.1
  have e := he _ hp (h * g * h') hg' X
  have hu' : IsUnit h'.det := WeylGroupFacts.isUnit_of_uh hh'.1
  have hs : B.sgs ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) (h * g * h') = g := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, Matrix.mul_one]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.one_mul]
  rw [hs] at e
  simpa only [Equiv.apply_symm_apply, Matrix.nonsing_inv_nonsing_inv h' hu'] using e

theorem equivariant_coefficient_preserves_forms {c : Coef S v} (hc : B.CkOn ⊤ (B.GPos (T v).base) c) (he : EqvC S T v c)
    {J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} (hJ : J ∈ smoothFormsPositiveCone S T v) :
    (fun g => c g (J g)) ∈ smoothFormsPositiveCone S T v := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U1, J', hU1, hg1, hJ', hJeq⟩ := hS g₀ hg₀
    obtain ⟨U2, c', hU2, hg2, hc', hceq⟩ := hc g₀ ⟨hg₀.1.1, hg₀.2.1⟩
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g => ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ (c' g)) (U1 ∩ U2) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ).contDiff.comp_contDiffOn (hc'.mono Set.inter_subset_right)
    refine ⟨U1 ∩ U2, fun g => c' g (J' g), hU1.inter hU2, ⟨hg1, hg2⟩,
      h2.clm_apply (hJ'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgl
    simp only
    rw [hJeq g hg.1 hgl, hceq g hg.2 hgl.1]
  · intro g hg n hn
    simp only
    rw [hL g hg n hn, ContinuousLinearMap.map_smul, eqv_left he hg.1.1 hn.1]
  · intro g hg n hn
    simp only
    rw [hR g hg n hn, ContinuousLinearMap.map_smul, eqv_right he hg.1.1 hn.1]
  · intro g hg h hh h' hh'
    simp only
    rw [hU g hg h hh h' hh', eqv_uw he hg.1.1 hh hh']

end eqv

section transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem trJ_of_fibMat (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (c : Coef S v)
    (V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)
    (hV : FibMat S T v e c V) (b : A (D.parOf S v) (DQ (D.parOf S v)))
    (β : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → (DQ (D.parOf S v)).R)
    (hβ : ∀ ρ π, b ρ π = (DQ (D.parOf S v)).fnP (β ρ π) (cjD (D.parOf S v) (β ρ π)))
    (hβV : ∀ ρ π q, evD (D.parOf S v) q (β ρ π) = V ρ π q)
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hJ : J ∈ smoothFormsPositiveCone S T v) :
    actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (fun g => c g (J g)) := by
  funext ρ
  set X := actA (D.parOf S v) b (trJ S T v e J) ρ with hXdef
  have hsm : ∀ π (q : Qp (D.parOf S v).r (D.parOf S v).TT), evQ (D.parOf S v) (trJ S T v e J π) q =
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) := fun π q =>
    congrFun (En.toSm_val_of_mem (D.parOf S v) (En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ π)) q
  have hw : (fun q : Qp (D.parOf S v).r (D.parOf S v).TT =>
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1))))) =
      (X : Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) := by
    funext q
    have hX := actA_fm_apply (D.parOf S v) hβ (trJ S T v e J) ρ q
    change _ = evQ (D.parOf S v) X q
    rw [hX]
    simp only [hsm, hβV]
    have hfib := En.fibre_membership_holds E Wp Wq S T v hPl J hJ q.1 q.2
    have hspan := (hFr.2 q.1.2 q.2.2).2.2 _ hfib
    have hcJ : c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1)) =
        ∑ π, inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) •
          c (B.gq (T v).base q.1) (e π q.1.2) := by
      conv_lhs => rw [hspan]
      rw [map_sum]
      simp only [ContinuousLinearMap.map_smul]
    rw [hcJ, En.hsVec_sum_smul, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [inner_smul_right, hV q.1 q.2 ρ π]
    ring
  unfold trJ
  beta_reduce
  rw [hw]
  unfold MA.toSm
  rw [dif_pos X.2]

theorem real_to_bounded_holds : RealToBdd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hPl e Cb c ca V b hFr hR hb
  obtain ⟨hadj, hc, hca, he, hea, hbc, hbca, hV⟩ := hR
  choose β hβ hβV using hb
  refine ⟨orderZeroDifferentialOperator S v c ca hadj, order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f _ g hg
    rw [order_zero_operator_apply, order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [order_zero_operator_apply]; exact equivariant_coefficient_preserves_forms hc he hJ
  · rw [order_zero_operator_adjoint]; exact equivariant_coefficient_preserves_forms hca hea hJ
  · rw [order_zero_operator_apply]
    exact trJ_of_fibMat S T v hPl e hFr c V hV b β hβ hβV J hJ

end transfer

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
