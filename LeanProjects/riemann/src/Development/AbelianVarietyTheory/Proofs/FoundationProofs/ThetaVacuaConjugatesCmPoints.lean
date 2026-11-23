import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTorsionTranslatesOddThetaProductStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisTaylorSeriesCanonicalOddThetaAllStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateIStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntireStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerPairEqSumCorrespondingRepresentaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeEqClosureIndependentPairStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslateMemThetaPullbackSpanStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalisedThetaPullbackMemTorsionTranslatesSpanAStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionMapCarriesTorusLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslatesSpanTaylorCoeffsAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

variable {D : D7} {N N' r : ℕ}

theorem CjF.fnConj_eq {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {F F' : VC D N N' → ℂ}
    (h : CjF D M ρ F F') : fnConj D M ρ F = F' := by
  funext z
  rw [← (GlobalTheory.T.hasSum_taylor_coordinateSpace_entire D N N' F' h.2.1 z).tsum_eq]
  unfold fnConj
  refine tsum_congr fun α => ?_
  rw [(h.2.2 α).2]; rfl

theorem CjF.unique {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {F F₁ F₂ : VC D N N' → ℂ}
    (h : CjF D M ρ F F₁) (h' : CjF D M ρ F F₂) : F₁ = F₂ := by
  rw [← h.fnConj_eq, h'.fnConj_eq]

theorem CjF.eq_zero {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {F : VC D N N' → ℂ}
    (h : CjF D M ρ F 0) : F = 0 := by
  funext z
  rw [← (GlobalTheory.T.hasSum_taylor_coordinateSpace_entire D N N' F h.1 z).tsum_eq]
  have : ∀ α, TaylorLogMetric.taylor D F α = 0 := fun α => by
    have h1 := (h.2.2 α).2
    rw [taylor_zero, cj_mem ρ (h.2.2 α).1] at h1
    have h2 := (map_eq_zero ρ).1 h1.symm
    exact congrArg Subtype.val h2
  simp [this]

theorem cjF_of {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {F F' : VC D N N' → ℂ}
    (hF : Differentiable ℂ F) (hc : CoefIn D F M) (he : fnConj D M ρ F = F')
    (hF' : Differentiable ℂ F') (h0 : F' = 0 → F = 0) : CjF D M ρ F F' := by
  by_cases hz : F' = 0
  · rw [h0 hz, hz]; exact CjF.zero D M ρ
  · subst he
    exact ⟨hF, hF', fun α => ⟨hc α, (GlobalTheory.T.taylorCoeff_conjugateSeries D N N' M ρ F hF' hz).1 α⟩⟩

theorem U_eq_zero {T : Tor D} {x : VC D N N'} {F : VC D N N' → ℂ} (h : U D T x F = 0) : F = 0 := by
  funext z
  have := congrFun h (z - x)
  simpa [U] using this

theorem U_of_zero (T : Tor D) (x : VC D N N') : U D T x (0 : VC D N N' → ℂ) = 0 := by
  funext z; simp [U]

theorem pull_cjF (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {M : IntermediateField ℚ ℂ} (ρ : M →ₐ[ℚ] ℂ)
    (hD : DataIn D (tor0 D cc δ) M) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) {g g' : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hg' : Differentiable ℂ g')
    (h : ∀ n, coef1 g n ∈ M ∧ coef1 g' n = cj M ρ (coef1 g n)) :
    CjF D M ρ (pullB D (tor0 D cc δ) b g) (pullB D (torConj D (tor0 D cc δ) M ρ) b g') := by
  have hM : ∀ τ x, embT D τ x ∈ M := hD.1
  refine GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj D N N' r M ρ (fun _ => g) (fun _ => g')
    (fun j τ a c => (starRingEnd ℂ) (embT D τ (b j a c)))
    (fun j τ a c => (starRingEnd ℂ) (cj M ρ (embT D τ (b j a c)))) (fun _ => hg) (fun _ => hg')
    (fun _ => h) (fun j τ a c => ?_)
  rw [← emb_conj, ← cjEmb_apply D M ρ hM, ← cjEmb_apply D M ρ hM]
  exact ⟨hM _ _, (emb_conj D _ _).symm⟩

theorem smul_mem_LaS {T : Tor D} {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {c : ℂ}
    (hc : ∀ w ∈ T.abelian₂, c * w ∈ T.abelian₂) {x : VC D N N'} (hx : x ∈ LaS D T Y) : c • x ∈ LaS D T Y := by
  unfold LaS at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨c * w, hc w hw, A, hA, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem nsmul_mem_LaB {T : Tor D} (hT : Good D T)
    (hst : ∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂)
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} {k : ℕ} {Y : Set (Matrix (Fin N') (Fin N) D.host.E)}
    (hC : Comm D b k Y) {x : VC D N N'} (hx : x ∈ LaS D T Y) : k • x ∈ LaB D T b := by
  unfold LaS at hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    obtain ⟨a, ha⟩ := hC.1 A hA
    have h1 : k • embV D T A = ∑ j, D.host.φ₀ (((a j : D.host.K) : D.host.E)) • embV D T (b j) := by
      have h2 := congrArg (hT.embHom N N') ha
      rw [map_nsmul, map_sum] at h2
      refine h2.trans (Finset.sum_congr rfl fun j _ => ?_)
      exact hT.embV_smul _ _
    rw [smul_comm, h1, Finset.smul_sum]
    refine sum_mem fun j _ => AddSubgroup.subset_closure ⟨_, hst (a j) w hw, j, ?_⟩
    rw [smul_smul, mul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem nsmul_mem_LaS {T : Tor D} (hT : Good D T)
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} {k : ℕ} {Y : Set (Matrix (Fin N') (Fin N) D.host.E)}
    (hC : Comm D b k Y) {x : VC D N N'} (hx : x ∈ LaB D T b) : k • x ∈ LaS D T Y := by
  have key : ∀ w ∈ T.abelian₂, ∀ y ∈ AddSubgroup.closure Y, w • hT.embHom N N' y ∈ LaS D T Y := by
    intro w hw y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz => exact AddSubgroup.subset_closure ⟨w, hw, z, hz, rfl⟩
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, smul_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, smul_neg]; exact neg_mem hy
  unfold LaB at hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, j, rfl⟩ := hz
    have := key w hw _ (hC.2 j)
    rw [map_nsmul, smul_comm] at this
    exact this
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem finiteIndex_of {V : Type*} [AddCommGroup V] {A₁ A₂ : AddSubgroup V} (hf : A₂.FG) {m : ℕ}
    (hm : 0 < m) (h : ∀ x ∈ A₂, m • x ∈ A₁) : (A₁.addSubgroupOf A₂).FiniteIndex := by
  haveI : AddGroup.FG A₂ := (AddGroup.fg_iff_addSubgroup_fg A₂).2 hf
  haveI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A₂ hm.ne'
  refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom m : A₂ →+ A₂).range) ?_
  rintro _ ⟨x, rfl⟩
  exact h x x.2

theorem tr_comb {T : Tor D} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} {F : VC D N N' → ℂ}
    (hF : F ∈ Tr D T b) : ∃ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (m : ℕ), 0 < m ∧
      (∀ i, m • t i ∈ LaB D T b) ∧ F = comb D T c t (pullB D T b (sgStar T.abelian₂)) := by
  obtain ⟨k, f, g, rfl⟩ := Submodule.mem_span_set'.1 hF
  choose t ht hg using fun i => (g i).2
  choose m hm hmt using ht
  refine ⟨k, fun i => (f i : ℂ), t, ∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    rw [hq, mul_nsmul]
    exact AddSubgroup.nsmul_mem _ (hmt i) q
  · funext z
    simp only [comb, Finset.sum_apply, hg]
    rfl

theorem ee_half_int (m : ℤ) : ee ((m : ℝ) / 2) = (-1 : ℂ) ^ m := by
  unfold ee
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast; ring

theorem al_eq {T : Tor D} {x : VC D N N'} {m : ℤ} (h : qH D T x = m) :
    al D T x = (-1 : ℂ) ^ m ∧ wdPh D T x = (-1 : ℂ) ^ m := by
  constructor
  · unfold al
    have : Real.sqrt D.host.d / 2 * (Hf D T x x).re = m := h
    rw [this, round_intCast]
  · unfold wdPh
    rw [h, ee_half_int]

theorem al_eq_wdPh {T : Tor D} {x : VC D N N'} (h : wdPh D T x ^ 2 = 1) : al D T x = wdPh D T x := by
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (qH D T x : ℂ)) = 1 := by
    rw [← h]
    unfold wdPh ee
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
  have h2 : (qH D T x : ℂ) = m := by
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h3
    rw [hm]; ring
  have h4 : qH D T x = m := by exact_mod_cast h2
  rw [(al_eq h4).1, (al_eq h4).2]

def GalRel (D : D7) (T T' : Tor D) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : ℕ) (F F' : VC D N N' → ℂ) : Prop :=
  ∃ R : VC D N N' → VC D N N' → Prop, (∀ x x' y y', R x x' → R y y' → R (x - y) (x' - y')) ∧
    ∀ Y, Comm D b k Y → KLat D T (LaS D T Y) →
      (∀ x ∈ LaS D T Y, ∃ x' ∈ LaS D T' Y, R x x') ∧ (∀ x' ∈ LaS D T' Y, ∃ x ∈ LaS D T Y, R x x') ∧
      (∀ x x', R x x' → (x ∈ LaS D T Y ↔ x' ∈ LaS D T' Y)) ∧
      ∀ x x', R x x' → x ∈ LaS D T Y → CjF D M ρ (aU D T x F) (aU D T' x' F')

section Fix

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {ρ : Qbar →ₐ[ℚ] ℂ}
  {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
include hc

theorem dataIn : DataIn D (tor0 D cc δ) Qbar := ((GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc).1

theorem sg_diff : Differentiable ℂ (sgStar (lamOf D cc δ)) :=
  (GlobalTheory.T.oddThetaFunction_existence_uniqueness _ (GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc).1).1.1

theorem sg_diff' (ρ : Qbar →ₐ[ℚ] ℂ) : Differentiable ℂ (sgStar (lamConj Qbar ρ (lamOf D cc δ))) :=
  (GlobalTheory.T.oddThetaFunction_existence_uniqueness _ (GlobalTheory.T.conjugateLattice_eq_closure_independent_pair D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc Qbar ρ (dataIn hc).2.1 (dataIn hc).2.2)).1.1

include hb

theorem step (hK : FixK D Qbar ρ) {F F' : VC D N N' → ℂ} (hF : F ∈ Tr D (tor0 D cc δ) b)
    {k : ℕ} {c : Fin k → ℂ} {t : Fin k → VC D N N'} {m : ℕ} (hm : 0 < m)
    (ht : ∀ i, m • t i ∈ LaB D (tor0 D cc δ) b)
    (he : F = comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))))
    (hFF : CjF D Qbar ρ F F') {x x' : VC D N N'} (hx : m • x ∈ LaB D (tor0 D cc δ) b)
    (ha : AdpB D (tor0 D cc δ) Qbar ρ b (2 * m) x x') :
    CjF D Qbar ρ (U D (tor0 D cc δ) x F) (U D (torConj D (tor0 D cc δ) Qbar ρ) x' F') ∧
      (wdPh D (tor0 D cc δ) x ∈ Qbar →
        cj Qbar ρ (wdPh D (tor0 D cc δ) x) = wdPh D (torConj D (tor0 D cc δ) Qbar ρ) x') := by
  have hU := GlobalTheory.T.torsionTranslatesSpan_taylorCoeffs_algebraic D cc δ hc N N' r b hb _ (GlobalTheory.T.torsionTranslate_mem_thetaPullbackSpan D cc δ hc N N' r b hb F hF x m hm hx)
  have h := GlobalTheory.T.galois_conj_torsionTranslates_oddThetaProduct D cc δ hc Qbar ρ hK (dataIn hc) N N' r b hb k c t x x' m hm hx ht ha
    (he ▸ (GlobalTheory.T.torsionTranslatesSpan_taylorCoeffs_algebraic D cc δ hc N N' r b hb F hF).2) (he ▸ hU.2)
  rw [← he, hFF.fnConj_eq] at h
  refine ⟨cjF_of hU.1 hU.2 h.1 (differentiable_U D _ _ hFF.2.1) fun h0 => ?_, fun hw => (h.2 hw).1⟩
  have h1 := U_eq_zero h0
  subst h1
  rw [hFF.eq_zero, U_of_zero]

theorem exists_conj_fix (hK : FixK D Qbar ρ) {F : VC D N N' → ℂ} (hF : F ∈ Tr D (tor0 D cc δ) b) :
    ∃ F', CjF D Qbar ρ F F' := by
  have hD := dataIn hc
  have hcoef : ∀ n, coef1 (sgStar (lamOf D cc δ)) n ∈ Qbar := fun n => by
    have h := (GlobalTheory.T.forall_use1 D cc δ hc).1 0 ⟨1, one_pos, by simpa using zero_mem _⟩ n
    have e : U1 (lamOf D cc δ) 0 (sgStar (lamOf D cc δ)) = sgStar (lamOf D cc δ) := by
      funext z; simp [U1]
    rwa [e] at h
  have hS := pull_cjF cc δ ρ hD b (sg_diff hc) (sg_diff' hc ρ) fun n =>
    ⟨hcoef n, (GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all D cc δ hc Qbar ρ hK hD.2.1 hD.2.2 hcoef n).symm⟩
  have hSm : pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)) ∈ Tr D (tor0 D cc δ) b :=
    Submodule.subset_span ⟨0, ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩, (U_zero D _ _).symm⟩
  unfold Tr at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨t, ⟨m, hm, ht⟩, rfl⟩ := hF
    obtain ⟨t', ht'⟩ := (GlobalTheory.T.torsionMap_carries_torus_lattices D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 (GlobalTheory.T.galStar_complexMultiplication_points D) cc δ hc Qbar ρ hK hD
      ((GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc).2 N N' r b hb (2 * m) (by omega)).2.1 t m hm ht
    refine ⟨_, (step hc hb hK hSm (k := 1) (c := fun _ => 1) (t := fun _ => 0) hm
      (fun _ => by rw [smul_zero]; exact zero_mem _) ?_ hS ht ht').1⟩
    funext z
    simp [comb, U_zero]
  | zero => exact ⟨0, CjF.zero D _ ρ⟩
  | add F G _ _ hF hG =>
    obtain ⟨F', hF⟩ := hF
    obtain ⟨G', hG⟩ := hG
    exact ⟨_, hF.add hG⟩
  | smul a F _ hF =>
    obtain ⟨F', hF⟩ := hF
    exact ⟨_, hF.mul a.2⟩

theorem galRel_fix (hK : FixK D Qbar ρ) {F F' : VC D N N' → ℂ} (hF : F ∈ Tr D (tor0 D cc δ) b)
    (hFF : CjF D Qbar ρ F F') {k : ℕ} (hk : 0 < k) :
    GalRel D (tor0 D cc δ) (torConj D (tor0 D cc δ) Qbar ρ) Qbar ρ b k F F' := by
  have hG := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨s, c, t, m, hm, ht, he⟩ := tr_comb hF
  have hmk : 0 < m * k := Nat.mul_pos hm hk
  obtain ⟨h1, -, h2⟩ := GlobalTheory.T.torsionMap_carries_torus_lattices D hG (GlobalTheory.T.galStar_complexMultiplication_points D) cc δ hc Qbar ρ hK (dataIn hc)
      ((GlobalTheory.T.admJ_and_torsion_data_algebraic D hG).2 cc δ hc).2 N N' r b hb (2 * (m * k)) (by omega)
  refine ⟨AdpB D (tor0 D cc δ) Qbar ρ b (2 * (m * k)), h1, fun Y hY hKL => ?_⟩
  obtain ⟨h3, h4, h5⟩ := h2 k Y hk ⟨2 * m, by ring⟩ hY
  refine ⟨h3, h4, h5, fun x x' hR hx => ?_⟩
  have hx1 : (m * k) • x ∈ LaB D (tor0 D cc δ) b :=
    nsmul_mem_LaB (isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ) (GlobalTheory.T.idealPeriodLattice_of_curveDatum D hG cc δ hc).2.2.2.2 (hY.mul m) hx
  obtain ⟨h6, h7⟩ := step hc hb hK hF hmk (fun i => by
    rw [mul_nsmul]; exact AddSubgroup.nsmul_mem _ (ht i) k) he hFF hx1 hR
  obtain ⟨q, hq⟩ := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hc N N' _ hKL).2.2.2.2.2.2 x hx
  obtain ⟨e1, e2⟩ := al_eq hq
  have hpm : (-1 : ℂ) ^ q = 1 ∨ (-1 : ℂ) ^ q = -1 := by
    rcases Int.even_or_odd q with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  have hmem : (-1 : ℂ) ^ q ∈ Qbar := zpow_mem (neg_mem (one_mem _)) q
  have h8 := h7 (e2 ▸ hmem)
  rw [e2] at h8
  have h9 : al D (torConj D (tor0 D cc δ) Qbar ρ) x' = cj Qbar ρ ((-1 : ℂ) ^ q) := by
    rw [al_eq_wdPh, h8]
    rw [← h8]
    rcases hpm with h | h
    · rw [h, cj_one]; norm_num
    · rw [h, cj_neg_one]; norm_num
  unfold aU
  rw [h9, e1]
  exact h6.mul hmem

end Fix

theorem vBar_invol (x : VC D N N') : vBar D (vBar D x) = x := by
  funext τ i j; simp [vBar]

theorem vBar_sub (x y : VC D N N') : vBar D (x - y) = vBar D x - vBar D y := by
  funext τ i j; simp [vBar]

theorem torBar_torBar (T : Tor D) : torBar D (torBar D T) = T := by
  obtain ⟨e, Λ⟩ := T
  unfold torBar
  congr 1
  · funext τ x; simp
  · ext z; simp

theorem vBar_mem {T : Tor D} {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {x : VC D N N'}
    (hx : x ∈ LaS D T Y) : vBar D x ∈ LaS D (torBar D T) Y := by
  unfold LaS at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨(starRingEnd ℂ) w, ⟨w, hw, rfl⟩, A, hA, ?_⟩
    funext τ i j; simp [vBar, embV, torBar]
  | zero =>
    have : vBar D (0 : VC D N N') = 0 := by funext τ i j; simp [vBar]
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz =>
    have : vBar D (y + z) = vBar D y + vBar D z := by funext τ i j; simp [vBar]
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : vBar D (-y) = -vBar D y := by funext τ i j; simp [vBar]
    rw [this]; exact neg_mem hy

theorem vBar_mem_iff {T : Tor D} {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {x : VC D N N'} :
    vBar D x ∈ LaS D T Y ↔ x ∈ LaS D (torBar D T) Y := by
  constructor
  · intro h; have := vBar_mem h; rwa [vBar_invol] at this
  · intro h; have := vBar_mem h; rwa [torBar_torBar] at this

theorem area_bar (T : Tor D) : area (torBar D T).abelian₂ = area T.abelian₂ := by
  unfold area
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨_, ⟨w₁, h1, rfl⟩, _, ⟨w₂, h2, rfl⟩, rfl⟩
    refine ⟨w₁, h1, w₂, h2, ?_⟩
    rw [← abs_neg]; congr 1; simp; ring
  · rintro ⟨w₁, h1, w₂, h2, rfl⟩
    refine ⟨_, ⟨w₁, h1, rfl⟩, _, ⟨w₂, h2, rfl⟩, ?_⟩
    rw [← abs_neg]; congr 1; simp; ring

theorem Hf_torBar (T : Tor D) (x y : VC D N N') :
    Hf D (torBar D T) (vBar D x) (vBar D y) = (starRingEnd ℂ) (Hf D T x y) := by
  simp [Hf, area_bar, vBar]

theorem cBar_aU (T : Tor D) (x : VC D N N') (F : VC D N N' → ℂ) :
    cBar D (aU D T (vBar D x) F) = aU D (torBar D T) x (cBar D F) := by
  funext z
  have h1 := Hf_torBar T (vBar D z) (vBar D x)
  have h2 := Hf_torBar T (vBar D x) (vBar D x)
  rw [vBar_invol] at h1 h2
  rw [vBar_invol] at h1
  have h3 : vBar D (z + x) = vBar D z + vBar D x := by funext τ i j; simp [vBar]
  simp only [cBar, aU, U, al, h1, h2, h3, map_mul, ← Complex.exp_conj, map_zpow₀, Complex.conj_re]
  simp [map_ofNat]

theorem entire_cBar {F : VC D N N' → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (cBar D F) := by
  intro z
  have h := (hF (star z)).star_star
  rw [star_star] at h
  exact h

theorem cBar_cBar (F : VC D N N' → ℂ) : cBar D (cBar D F) = F := by
  funext z; simp [cBar, vBar_invol]

theorem rhoBar_rhoBar (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : rhoBar M (rhoBar M ρ) = ρ := by
  ext x; simp [rhoBar]

theorem CjF.bar {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {F F' : VC D N N' → ℂ}
    (h : CjF D M ρ F F') (he : fnConj D M (rhoBar M ρ) F = cBar D (fnConj D M ρ F)) :
    CjF D M (rhoBar M ρ) F (cBar D F') := by
  rw [h.fnConj_eq] at he
  refine cjF_of h.1 (fun α => (h.2.2 α).1) he (entire_cBar h.2.1) fun h0 => ?_
  have : F' = 0 := by
    rw [← cBar_cBar F', h0]; funext z; simp [cBar]
  subst this
  exact h.eq_zero

theorem GalRel.bar {T T' : Tor D} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} {k : ℕ} {F F' : VC D N N' → ℂ}
    (h : GalRel D T T' M ρ b k F F')
    (he : ∀ G : VC D N N' → ℂ, fnConj D M (rhoBar M ρ) G = cBar D (fnConj D M ρ G)) :
    GalRel D T (torBar D T') M (rhoBar M ρ) b k F (cBar D F') := by
  obtain ⟨R, h1, h2⟩ := h
  refine ⟨fun x x' => R x (vBar D x'), fun x x' y y' hx hy => ?_, fun Y hY hK => ?_⟩
  · beta_reduce; rw [vBar_sub]; exact h1 _ _ _ _ hx hy
  obtain ⟨h3, h4, h5, h6⟩ := h2 Y hY hK
  refine ⟨fun x hx => ?_, fun x' hx' => h4 _ (vBar_mem_iff.2 hx'), fun x x' hR => ?_, fun x x' hR hx => ?_⟩
  · obtain ⟨x', hx', hR⟩ := h3 x hx
    exact ⟨vBar D x', vBar_mem hx', by beta_reduce; rwa [vBar_invol]⟩
  · rw [h5 _ _ hR, vBar_mem_iff]
  · rw [← cBar_aU]
    exact (h6 _ _ hR hx).bar (he _)

theorem galRel_all {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) (ρ : Qbar →ₐ[ℚ] ℂ)
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) {F : VC D N N' → ℂ}
    (hF : F ∈ Tr D (tor0 D cc δ) b) {k : ℕ} (hk : 0 < k) :
    ∃ F', CjF D Qbar ρ F F' ∧
      GalRel D (tor0 D cc δ) (torConj D (tor0 D cc δ) Qbar ρ) Qbar ρ b k F F' := by
  rcases (GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc Qbar ρ (dataIn hc)).1 with hK | hK
  · obtain ⟨F', h⟩ := exists_conj_fix hc hb hK hF
    exact ⟨F', h, galRel_fix hc hb hK hF h hk⟩
  · obtain ⟨F', h⟩ := exists_conj_fix hc hb hK hF
    obtain ⟨-, h1, h2⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc Qbar (rhoBar Qbar ρ) (dataIn hc)
    have h3 := fun G => (h2 N N' ⊥ ⊥ G).1
    have h4 := (galRel_fix hc hb hK hF h hk).bar h3
    have h5 := h.bar (h3 F)
    rw [← h1] at h4
    rw [rhoBar_rhoBar] at h4 h5
    exact ⟨_, h5, h4⟩

theorem conj_iop {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) (ρ : Qbar →ₐ[ℚ] ℂ)
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) {F : VC D N N' → ℂ}
    (hF : F ∈ Tr D (tor0 D cc δ) b) {k : ℕ} (hk : 0 < k)
    {Y₁ Y₂ : Set (Matrix (Fin N') (Fin N) D.host.E)} (h₁ : Comm D b k Y₁) (h₂ : Comm D b k Y₂)
    (k₁ : KLat D (tor0 D cc δ) (LaS D (tor0 D cc δ) Y₁))
    (k₂ : KLat D (tor0 D cc δ) (LaS D (tor0 D cc δ) Y₂))
    (hth : F ∈ ThSp D (tor0 D cc δ) (LaS D (tor0 D cc δ) Y₁)) :
    Iop D (tor0 D cc δ) (LaS D (tor0 D cc δ) Y₁) (LaS D (tor0 D cc δ) Y₂) F ∈ Tr D (tor0 D cc δ) b ∧
    ∃ F', CjF D Qbar ρ F F' ∧
      F' ∈ ThSp D (torConj D (tor0 D cc δ) Qbar ρ) (LaS D (torConj D (tor0 D cc δ) Qbar ρ) Y₁) ∧
      ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧
        CjF D Qbar ρ (Iop D (tor0 D cc δ) (LaS D (tor0 D cc δ) Y₁) (LaS D (tor0 D cc δ) Y₂) F)
          fun z => sg * Iop D (torConj D (tor0 D cc δ) Qbar ρ) (LaS D (torConj D (tor0 D cc δ) Qbar ρ) Y₁)
            (LaS D (torConj D (tor0 D cc δ) Qbar ρ) Y₂) F' z := by
  have hG := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  have hT := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  have hst := (GlobalTheory.T.idealPeriodLattice_of_curveDatum D hG cc δ hc).2.2.2.2
  obtain ⟨F', hFF, R, hsub, hR⟩ := galRel_all hc ρ hb hF hk
  obtain ⟨-, a2, a3, a4⟩ := hR Y₁ h₁ k₁
  obtain ⟨b1, b2, -, b4⟩ := hR Y₂ h₂ k₂
  obtain ⟨-, -, l1, -, l2, -, l3⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hc N N' _ k₂
  have hB : ∀ x ∈ LaS D (tor0 D cc δ) Y₂, k • x ∈ LaB D (tor0 D cc δ) b := fun x hx =>
    nsmul_mem_LaB hT hst h₂ hx
  have hfin := finiteIndex_of (A₁ := LaS D (tor0 D cc δ) Y₁) l2 (Nat.mul_pos hk hk) fun x hx => by
    rw [mul_nsmul]; exact nsmul_mem_LaS hT h₁ (hB x hx)
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_integer_map_eq_halfOneAddSqrt D
  have hri := GlobalTheory.T.twistedTranslateClassInvariant_of_mem_thetaSpace D _ N N' _ _ F l3
    (fun x hx y hy => l1 _ (smul_mem_LaS (fun w hw => ha ▸ hst a w hw) hx) y hy) hth
  have hiff : ∀ x x' y y', R x x' → R y y' → (x - y ∈ LaS D (tor0 D cc δ) Y₁ ↔
      x' - y' ∈ LaS D (torConj D (tor0 D cc δ) Qbar ρ) Y₁) := fun x x' y y' hx hy =>
    a3 _ _ (hsub _ _ _ _ hx hy)
  have hri' : RepInd D (torConj D (tor0 D cc δ) Qbar ρ) (LaS D (torConj D (tor0 D cc δ) Qbar ρ) Y₁)
      (LaS D (torConj D (tor0 D cc δ) Qbar ρ) Y₂) F' := by
    intro x' hx' y' hy' hd
    obtain ⟨x, hx, rx⟩ := b2 x' hx'
    obtain ⟨y, hy, ry⟩ := b2 y' hy'
    have e := hri x hx y hy ((hiff _ _ _ _ rx ry).2 hd)
    exact (b4 _ _ rx hx).unique (e ▸ b4 _ _ ry hy)
  obtain ⟨n, x, x', hx, e1, e2⟩ := GlobalTheory.T.thetaIntertwiner_pair_eq_sum_corresponding_representatives D _ _ N N' _ _ _ _ F F' R hfin hri hri' b1 b2 hiff
  have hsq : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n : ℝ) : ℝ) : ℂ) = n := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]; simp
  have hsm : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow two_pos ?_
    rw [sq, hsq]
    exact isAlgebraic_nat n
  have him := inv_mem hsm
  refine ⟨?_, F', hFF, ⟨hFF.2.1, fun y' hy' => ?_⟩, ?_⟩
  · rw [e1]
    have hal : ∀ i, al D (tor0 D cc δ) (x i) ∈ Qbar := fun i => zpow_mem (neg_mem (one_mem _)) _
    have := Submodule.smul_mem _ (⟨_, him⟩ : Qbar) (Submodule.sum_mem _ (t := Finset.univ) fun i _ =>
      Submodule.smul_mem _ (⟨_, hal i⟩ : Qbar)
        (GlobalTheory.T.torsionTranslate_mem_thetaPullbackSpan D cc δ hc N N' r b hb F hF (x i) k hk (hB _ (hx i).1)))
    convert this using 1
    funext z
    simp only [Pi.smul_apply, Finset.sum_apply]
    rfl
  · obtain ⟨y, hy, ry⟩ := a2 y' hy'
    have h := a4 _ _ ry hy
    have e : aU D (tor0 D cc δ) y F = F := funext (hth.2 y hy)
    rw [e] at h
    exact congrFun (h.unique hFF)
  · have h := (CjF.sum Finset.univ fun i _ => b4 _ _ (hx i).2.2 (hx i).1).mul him
    have hs : cj Qbar ρ ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ ^ 2 = ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ ^ 2 := by
      rw [sq, sq, ← cj_mul ρ him him, ← mul_inv, hsq, cj_mem ρ (inv_mem (natCast_mem _ n))]
      have : (⟨(n : ℂ)⁻¹, inv_mem (natCast_mem _ n)⟩ : Qbar) = (n : Qbar)⁻¹ := rfl
      rw [this, map_inv₀, map_natCast]
    rw [e1, e2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with hs | hs
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hs] at h
      simpa only [one_mul] using h
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [hs] at h
      simpa only [neg_mul, one_mul] using h

theorem mod1All_cj (ρ : Qbar →ₐ[ℚ] ℂ) {κ sg : ℂ} (h : Mod1All κ) (hs : sg = 1 ∨ sg = -1) :
    Mod1All (cj Qbar ρ κ * sg) := by
  obtain ⟨hκ, h⟩ := h
  have hm : ∀ x : Qbar, ρ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    have hx : IsAlgebraic ℚ (Qbar.val x) := (mem_algebraicClosure_iff).1 x.2
    exact ((isAlgebraic_algHom_iff Qbar.val Subtype.val_injective).1 hx).algHom ρ
  have h1 := fun σ : Qbar →+* ℂ => h (σ.comp ((ρ : Qbar →+* ℂ).codRestrict Qbar.toSubfield hm))
  rw [cj_mem ρ hκ]
  rcases hs with rfl | rfl
  · rw [mul_one]; exact ⟨hm _, h1⟩
  · rw [mul_neg_one]
    refine ⟨neg_mem (hm _), fun σ => ?_⟩
    have : (⟨-ρ ⟨κ, hκ⟩, neg_mem (hm _)⟩ : Qbar) = -⟨ρ ⟨κ, hκ⟩, hm _⟩ := rfl
    rw [this, map_neg, norm_neg]
    exact h1 σ

theorem differentiable_thetaTorsionTranslate {Λ : AddSubgroup ℂ} (h : Differentiable ℂ (sgStar Λ)) (t : ℂ) :
    Differentiable ℂ (GL3Theta.th0 Λ t) := by
  unfold GL3Theta.th0 U1
  fun_prop

theorem useConj_all : ∀ D : D7, useConj D := by
  intro D cc δ hc t0 ht0 N N' L L' hL hL' _ G hE M ρ₀ hD₀ hcG
  have hG := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  have hD := dataIn hc
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_algClosure_embedding_extending_on_algebraic M ρ₀
  have hlam : lamConj M ρ₀ (lamOf D cc δ) = lamConj Qbar ρ (lamOf D cc δ) := by
    have h2 := hρ _ hD.2.1 hD₀.2.1
    have h3 := hρ _ hD.2.2 hD₀.2.2
    unfold lamConj
    congr 1
    funext Λ'
    exact congrArg₂ (fun a b => g2 Λ' = a ∧ g3 Λ' = b) h2 h3
  have htor : torConj D (tor0 D cc δ) M ρ₀ = torConj D (tor0 D cc δ) Qbar ρ := by
    unfold torConj
    congr 1
    funext τ x
    exact hρ _ (hD.1 τ x) (hD₀.1 τ x)
  have hfn : ∀ F : VC D N N' → ℂ, CoefIn D F Qbar → CoefIn D F M →
      fnConj D M ρ₀ F = fnConj D Qbar ρ F := fun F h1 h2 => by
    funext z
    exact tsum_congr fun α => congrArg (· * mono D α z) (hρ _ (h1 α) (h2 α))
  obtain ⟨b, κ, hb, hκ, rfl⟩ := hE
  obtain ⟨k, hk, hC⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b L L' hb hL hL'
  have kB : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := Or.inl ⟨_, b, hb, rfl⟩
  have kL : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨L, L', hL, hL', rfl⟩
  obtain ⟨-, -, c1, c2, -⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' _ b hb
  obtain ⟨d1, d2⟩ := GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant D hG cc δ hc t0 ht0
  have hth0 := GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice D (tor0 D cc δ) N N' _ b _ c1 c2 d1 d2
  have hI := (GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ kB kL _ hth0).2.1
  have hCb : Comm D b k (Set.range b) := by simpa using (comm_range D b).mul k
  obtain ⟨m1, F₀', m2, -, sg, hsg, m3⟩ := conj_iop hc ρ hb (GlobalTheory.T.pullB_th0_mem_tr D cc δ hc t0 ht0 N N' _ b hb) hk
    hCb hC (LaB_eq D _ b ▸ kB) kL (LaB_eq D _ b ▸ hth0)
  rw [← LaB_eq, ← La_eq] at m1
  rw [← LaB_eq, ← La_eq, ← LaB_eq, ← La_eq] at m3
  have m4 := m3.mul hκ.1
  have hGm := Submodule.smul_mem _ (⟨κ, hκ.1⟩ : Qbar) m1
  set G : VC D N N' → ℂ := fun z => κ * Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b)
    (La D (tor0 D cc δ) L L') (pullB D (tor0 D cc δ) b (GL3Theta.th0 (tor0 D cc δ).abelian₂ t0)) z with hGd
  change G ∈ _ at hGm
  change CjF D Qbar ρ G _ at m4
  have hGth : G ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := by
    refine ⟨m4.1, fun x hx z => ?_⟩
    have := hI.2 x hx z
    exact Eq.trans (by simp only [hGd, U]; rw [mul_left_comm κ, mul_assoc κ]; rfl)
      (congrArg (κ * ·) this)
  rw [htor, hlam, hfn G (fun α => (m4.2.2 α).1) hcG]
  refine ⟨?_, fun t0' ht0' => ⟨b, cj Qbar ρ κ * sg, hb, mod1All_cj ρ hκ hsg, ?_⟩, fun L₁ L₁' hL₁ hL₁' hcI => ?_⟩
  · obtain ⟨-, G', n1, n2, -⟩ := conj_iop hc ρ hb hGm hk hC hC kL kL hGth
    rw [n1.fnConj_eq]; exact n2
  · obtain ⟨-, u1, u2⟩ := GlobalTheory.T.forall_use1 D cc δ hc
    have e := m2.unique (pull_cjF cc δ ρ hD b d1 (differentiable_thetaTorsionTranslate (sg_diff' hc ρ) t0') fun n =>
      ⟨u1 t0 ht0 n, (u2 Qbar ρ hD.2.1 hD.2.2 t0 t0' ht0 ht0' (u1 t0 ht0) n).symm⟩)
    rw [m4.fnConj_eq, e]
    funext z
    exact (mul_assoc _ _ _).symm
  · obtain ⟨k₁, hk₁, hC₁⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b L₁ L₁' hb hL₁ hL₁'
    have hC₂ := hC₁.mul k
    rw [mul_comm k k₁] at hC₂
    obtain ⟨-, G', n1, -, s, hs, n2⟩ := conj_iop hc ρ hb hGm (Nat.mul_pos hk₁ hk) (hC.mul k₁) hC₂ kL
      (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) hGth
    refine ⟨s, hs, ?_⟩
    rw [n1.fnConj_eq]
    exact (hfn _ (fun α => (n2.2.2 α).1) hcI).trans n2.fnConj_eq

end GlobalTheory.ThetaConj
