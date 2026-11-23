import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CosetSum

open GlobalTheory.AutMult

theorem mem_realLevSet_iff {D : D7} {W : HSp D} {K : Subgroup (GA D W)} (hK : K ≤ GfC W) (h : GA D W) :
    (∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k) ↔ toFin W h ∈ K.subgroupOf (GfC W) := by
  constructor
  · rintro ⟨u, hu, k, hk, rfl⟩
    have h1 : toFin W u = 1 := toFin_coe_inf (V := W) ⟨u, hu⟩
    have h2 : toFin W k = ⟨k, hK hk⟩ := toFin_coe (V := W) ⟨k, hK hk⟩
    rw [map_mul, h1, h2, one_mul, Subgroup.mem_subgroupOf]
    exact hk
  · intro h'
    exact ⟨toInf W h, (toInf W h).2, toFin W h, (Subgroup.mem_subgroupOf).1 h', (toInf_mul_toFin h).symm⟩

theorem integral_eq_sum_cosets : ∀ (D : D7) (W : HSp D) (ν : Measure (GA D W)) (K : Subgroup (GA D W)), ν.IsHaarMeasure → K ≤ GfC W → IsOpen {g : GfC W | (g : GA D W) ∈ K} → ∀ Φ : GA D W → ℂ, Integrable Φ ν → MeasurableSet {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} ∧ HasSum (fun q : GfC W ⧸ K.subgroupOf (GfC W) => ∫ h in {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k}, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) (∫ g, Φ g ∂ν) := by
  intro D W ν K hν hKf hKo Φ hΦ
  obtain ⟨i0, -, i2, -, i4, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D W
  haveI := i0; haveI := i2; haveI := i4
  set K' := K.subgroupOf (GfC W) with hK'
  set C : Set (GA D W) := {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} with hCdef
  have hK'o : IsOpen (K' : Set (GfC W)) := hKo
  have hC : C = toFin W ⁻¹' (K' : Set (GfC W)) := Set.ext fun h => mem_realLevSet_iff hKf h
  have hCo : IsOpen C := hC ▸ hK'o.preimage (continuous_toFin W)
  have hCm : MeasurableSet C := hCo.measurableSet
  refine ⟨hCm, ?_⟩

  let s : GfC W ⧸ K' → Set (GA D W) := fun q => (fun g => ((Quotient.out q : GfC W) : GA D W)⁻¹ * g) ⁻¹' C
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (toFin W g) := by
    intro q g
    show _ ∈ C ↔ _
    rw [hC, Set.mem_preimage, map_mul, map_inv, toFin_coe, SetLike.mem_coe]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hCm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  haveI : Countable (GfC W ⧸ K') := by
    have hpd : (Set.univ : Set (GfC W ⧸ K')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (K' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hK'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [K'.one_mem]⟩))
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hΦ.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  refine (funext fun q => ?_ : (fun q : GfC W ⧸ K' => ∫ h in C, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) =
    fun q => ∫ x in s q, Φ x ∂ν) ▸ hsum
  have hpre : (fun h => ((Quotient.out q : GfC W) : GA D W) * h) ⁻¹' s q = C := by
    ext h; simp [s]
  rw [← hpre]
  exact ((measurePreserving_mul_left ν _).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft _) Φ (s q))

end GlobalTheory.CosetSum

end
