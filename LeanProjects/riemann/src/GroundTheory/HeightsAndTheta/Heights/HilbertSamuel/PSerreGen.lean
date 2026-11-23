import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SerreGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {V : Ideal (MRingOver S ι)}

def chartExp (c : ∀ k, ι k) (d : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then d q.1 else 0

theorem generated_nonneg (d : K → ℕ) : KH.GeneratedV S V (fun k => (d k : ℤ)) := by
  classical
  intro I
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  let p : MRingOver S ι := monomial (chartExp c d) 1
  have hph : IsMultiHomog p d := by
    refine GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => ?_
    simp [chartExp]
  have hpm : p ∈ KH.cellMon S I.1 := by
    change monomial (chartExp c d) 1 ∈ _
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
    refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
    have hq' : q.2 = c q.1 := by
      by_contra h
      simp [chartExp, h] at hq
    obtain ⟨k, i⟩ := q
    simp only at hq'
    subst hq'
    exact ⟨k, c k, hc k, rfl⟩
  have hpq : Ideal.Quotient.mk V p ∈ KH.quotPart S V (fun k => (d k : ℤ)) :=
    Submodule.subset_span ⟨p, ⟨fun k => Int.natCast_nonneg (d k), by simpa using hph⟩, rfl⟩
  have h1q : (1 : MRingOver S ι ⧸ V) ∈ KH.quotPart S V 0 :=
    Submodule.subset_span ⟨1, ⟨fun _ => le_rfl, GenTwistGenerated.isMultiHomog_one _ fun _ => rfl⟩, map_one _⟩
  refine ⟨1, fun _ _ => LocalizedModule.mk (Ideal.Quotient.mk V p) 1,
    fun _ => LocalizedModule.mk 1 ⟨p, hpm⟩,
    fun _ => GenTwistGenerated.mem_cechZc_zero (fun J => ?_) (GenTwistGenerated.cechD_const _),
    fun _ => ?_, ?_⟩
  · refine GenTwistGenerated.mk_mem_locPart _ _ 0 (GenTwistGenerated.isMultiHomog_one _ fun _ => rfl) ?_
    convert hpq using 2
    funext k
    simp
  · refine GenTwistGenerated.mk_mem_locPart _ _ d hph ?_
    convert h1q using 2
    funext k
    simp
  · have e : Ideal.Quotient.mk V p = (⟨p, hpm⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V) :=
      ((Algebra.smul_def p (1 : MRingOver S ι ⧸ V)).trans (mul_one _)).symm
    refine (Fin.sum_univ_one _).trans ?_
    refine LocalizedModule.mk_mul_mk.trans ?_
    calc LocalizedModule.mk (1 * Ideal.Quotient.mk V p) (⟨p, hpm⟩ * 1)
        = LocalizedModule.mk ((⟨p, hpm⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V)) ⟨p, hpm⟩ := by
          rw [one_mul, mul_one, e]
      _ = LocalizedModule.mk 1 1 := LocalizedModule.mk_cancel _ _
      _ = 1 := OreLocalization.one_def.symm

end SerreGen

theorem SerreGen.proof : KH.SerreGenStatement := by
  intro S _ K _ _ ι _ _ V e _ _
  refine ⟨∑ k, (e k).natAbs, fun c hc => ?_⟩
  have h : (e + fun _ => (c : ℤ)) = fun k => (((e k + c).toNat : ℕ) : ℤ) := by
    funext k
    have h₁ : (e k).natAbs ≤ ∑ k, (e k).natAbs :=
      Finset.single_le_sum (f := fun k => (e k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h₂ : -(e k) ≤ ((e k).natAbs : ℤ) := by
      rw [← Int.natAbs_neg]; exact Int.le_natAbs
    have h₃ : 0 ≤ e k + c := by omega
    simp only [Pi.add_apply]
    exact (Int.toNat_of_nonneg h₃).symm
  rw [h]
  exact SerreGen.generated_nonneg _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
