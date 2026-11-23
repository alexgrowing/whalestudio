import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AvgRestr

theorem apply_out_mk {G : Type} [Group G] (u : G → ℂ) (x : G) :
    u ((QuotientGroup.mk x : G ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  exact k.2 x

theorem avg_pi_comp {H : Type} [Group H] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (π : H →* ∀ i, G i) (hπ : Function.Surjective π) (u : ∀ i, G i → ℂ) (hu : ∀ i, (rStab (u i)).index ≠ 0) :
    avg (fun k => ∏ i, u i (π k i)) = ∏ i, avg (u i) := by
  set P : Subgroup (∀ i, G i) := Subgroup.pi Set.univ fun i => rStab (u i) with hP
  set R : Subgroup H := P.comap π with hRdef
  have hPi : P.index = ∏ i, (rStab (u i)).index := by
    simp_rw [hP, Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  have hRi : R.index = ∏ i, (rStab (u i)).index := by
    rw [hRdef, Subgroup.index_comap_of_surjective _ hπ, hPi]
  have hR0 : R.index ≠ 0 := by rw [hRi]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i
  have hRle : R ≤ rStab (fun k => ∏ i, u i (π k i)) := by
    intro k hk x
    have hk' : ∀ i, π k i ∈ rStab (u i) := fun i => ((Subgroup.mem_pi _).1 hk) i (Set.mem_univ i)
    simp only [map_mul, Pi.mul_apply]
    exact Finset.prod_congr rfl fun i _ => hk' i (π x i)
  rw [avg_eq_of_le_rStab H _ R hRle hR0]
  haveI : R.FiniteIndex := ⟨hR0⟩
  haveI : ∀ i, (rStab (u i)).FiniteIndex := fun i => ⟨hu i⟩
  haveI : Fintype (H ⧸ R) := Fintype.ofFinite _
  haveI : ∀ i, Fintype (G i ⧸ rStab (u i)) := fun i => Fintype.ofFinite _
  let e : H ⧸ R → ∀ i, G i ⧸ rStab (u i) := fun q i => QuotientGroup.mk (π q.out i)
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      apply QuotientGroup.eq.2
      show π (q.out⁻¹ * q'.out) ∈ P
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      have := QuotientGroup.eq.1 (congrFun hq i)
      simpa [map_mul, map_inv] using this
    · intro x
      obtain ⟨k, hk⟩ := hπ fun i => (x i).out
      refine ⟨QuotientGroup.mk k, funext fun i => ?_⟩
      obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul R k
      have hr' : π r ∈ P := r.2
      show (QuotientGroup.mk (π (QuotientGroup.mk k : H ⧸ R).out i) : G i ⧸ rStab (u i)) = x i
      rw [hr, map_mul, Pi.mul_apply, hk]
      conv_rhs => rw [← QuotientGroup.out_eq' (x i)]
      apply QuotientGroup.eq.2
      simpa using ((Subgroup.mem_pi _).1 hr') i (Set.mem_univ i)
  have hsum : ∑ᶠ q : H ⧸ R, ∏ i, u i (π q.out i) = ∏ i, ∑ᶠ q : G i ⧸ rStab (u i), u i q.out := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [finsum_eq_sum_of_fintype]
    rw [Fintype.prod_sum]
    exact Fintype.sum_bijective e he _ _ fun q => Finset.prod_congr rfl fun i _ => (apply_out_mk (u i) _).symm
  rw [hsum, hRi]
  simp only [avg]
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_inv_distrib]

end GlobalTheory.AvgRestr

namespace GlobalTheory.AvgRestr

theorem avg_restr_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)),
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ),
    (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) →
    avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      ∏ᶠ v, avg (u v) := by
  intro X V Y _ _ _ _ pf K hX u hu hev
  obtain ⟨S, hS⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually hev
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  let π : Kg →* ∀ v : S, K v.1 := MonoidHom.pi fun v =>
    ((pf v.1).comp Kg.subtype).codRestrict (K v.1) fun k => Subgroup.mem_iInf.1 k.2 v.1
  have hπ : Function.Surjective π := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    have hz : ∀ v, z v ∈ K v := fun v => by
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z (Eventually.of_forall hz)
    have hxK : x ∈ Kg := Subgroup.mem_iInf.2 fun v => by
      show pf v x ∈ K v
      rw [hx v]; exact hz v
    refine ⟨⟨x, hxK⟩, funext fun v => Subtype.ext ?_⟩
    show pf v.1 x = (y v : Y v.1)
    rw [hx v.1]
    simp [z, v.2]
  have hF : (fun k : Kg => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      fun k => ∏ v : S, u v.1 (π k v) := by
    funext k
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv (hS v h _),
      ← Finset.prod_coe_sort S]
    rfl
  have hA : ∏ᶠ v, avg (u v) = ∏ v : S, avg (u v.1) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv ?_,
      ← Finset.prod_coe_sort S]
    have hc : u v = fun _ => 1 := funext (hS v h)
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (fun _ : K v => (1 : ℂ)) (fun _ => 1) 1 1
      (by rw [← hc]; exact hu v) (by rw [← hc]; exact hu v)).2.2.2
  rw [hF, hA]
  exact avg_pi_comp π hπ (fun v : S => u v.1) fun v => hu v.1

end GlobalTheory.AvgRestr
