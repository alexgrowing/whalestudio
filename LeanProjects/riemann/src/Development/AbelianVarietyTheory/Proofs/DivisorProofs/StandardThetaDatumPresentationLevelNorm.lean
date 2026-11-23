import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorIntegralPointVacuumRootOfUnitySmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeTranslateUnitVectorVacuumExpansioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewIdealLatticePointRationalNormKillsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPrincipalCongruenceTransversalLeAbsNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombinationStatement

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

theorem pres_stdSum : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → Pres D ⊤ δ (Ideal.absNorm 𝔪) e0 (stdSum W 𝔪 0 R) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hco hb _hchar R hR huniq _hfix
  have he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) := hv.1
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hidx := GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow D δ hc 𝔪 h𝔪 hco a d
  haveI hfin : Finite (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) :=
    AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) := Fintype.ofFinite _
  have wsm : ∀ (x : VC D a d) (c : ℂ) (G : VC D a d → ℂ), Wd D (tor0 D ⊤ δ) x (c • G) = c • Wd D (tor0 D ⊤ δ) x G := by
    intro x c G; funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  have hr : ∀ i : R, ∃ (c : ℂ) (x : Matrix (Fin d) (Fin a) D.host.E), (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧
      pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d ∧
      (∀ i' j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) *
        ((((i : GA D a)⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i' j ∈ hatId D 𝔪) ∧
      W.Om i 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x)
          (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
    intro i
    obtain ⟨c, hcm, hce⟩ := GlobalTheory.T.weilOperator_integral_point_vacuum_rootOfUnity_smul D δ hc e0 he W i (hR i i.2)
    obtain ⟨x, hx, hxc, hom⟩ := GlobalTheory.T.weilAction_cosetVector_eq_translate_unitVector D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2)
    refine ⟨c, x, hcm, hx, hxc, ?_⟩
    rw [hom, GlobalTheory.T.weil_integralPoint_skewLatticeUnitVector_same_eigen D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2) c hce, wsm]
  choose c x hcm hx hxc hom using hr
  choose χ hχ using fun i : R => GlobalTheory.T.exists_addChar_thetaCommutatorPhase_skewLattice D δ hc 𝔪 (pt D (tor0 D ⊤ δ) δ (x i)) (hx i)
  have hone : ∀ k : GA D a, CongOne D 𝔪 (k⁻¹ * k) := by
    intro k i' j
    rw [inv_mul_cancel]
    simp
  have hinj : Function.Injective χ := by
    intro i j hij
    have hk : ∀ y ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d),
        Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i)) y =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x j)) y := by
      intro y hy
      rw [← hχ i ⟨y, hy⟩, ← hχ j ⟨y, hy⟩, hij]
    have h1 := GlobalTheory.T.stabilizer_congruent_of_commutatorPhase_eq D δ hc 𝔪 h𝔪 hco hb had i j (hR i i.2) (hR j j.2) (x i) (x j) (hx i) (hx j) (hxc i) (hxc j) hk
    exact Subtype.ext ((huniq j (hR j j.2)).unique ⟨i.2, h1⟩ ⟨j.2, hone j⟩)
  have hcard : Fintype.card R ≤ Ideal.absNorm 𝔪 ^ (a * d) := by
    rw [Fintype.card_coe]
    refine (GlobalTheory.T.card_principalCongruence_transversal_le_absNorm_pow D 𝔪 h𝔪 a R hR huniq).trans (Nat.pow_le_pow_right hN0 ?_)
    rw [pow_two]; exact Nat.mul_le_mul_left a had
  obtain ⟨rr, hrr, hint, hρ⟩ := GlobalTheory.T.sum_norm_sq_le_of_rootOfUnity_addChar_combination (Ideal.absNorm 𝔪) (a * d) c χ hN0 hcm hinj
    (by rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]) hcard
  choose z hz hzN using fun q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) =>
    GlobalTheory.T.skewIdealLattice_point_rational_normKills D δ hc 𝔪 h𝔪 _ (Quotient.out q).2
  set e := Fintype.equivFin (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)))
  refine ⟨_, fun i => rr (e.symm i), fun i => z (e.symm i), fun i => hzN _, fun i => hint _, fun ρ => ?_, ?_⟩
  · rw [e.symm.sum_comp (fun q => ‖ρ (rr q)‖)]; exact hρ ρ
  funext y
  rw [e.symm.sum_comp (fun q => ((rr q : Qbar) : ℂ) * Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) e0 y)]
  simp only [stdSum, Finset.sum_apply]
  rw [← Finset.sum_coe_sort R]
  simp only [hom, Pi.smul_apply, smul_eq_mul, GlobalTheory.T.standardLattice_translate_unitVector_vacuum_expansion D δ hc 𝔪 h𝔪 e0 he _ (hx _), hidx,
    finsum_eq_sum_of_fintype, hrr, ← hz]
  have hs : ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) : ℂ))⁻¹ = (((Ideal.absNorm 𝔪 : ℂ)) ^ (a * d))⁻¹ := by
    have h1 : (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) = (Ideal.absNorm 𝔪 : ℝ) ^ (a * d) := by push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  have hχq : ∀ (i : R) q, χ i q = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i))
      ((Quotient.out q : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) : VC D a d) := by
    intro i q
    rw [← hχ i, QuotientAddGroup.out_eq']
  simp only [hχq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← hs]; ring

end GlobalTheory.FunObj.StdDatum

end
