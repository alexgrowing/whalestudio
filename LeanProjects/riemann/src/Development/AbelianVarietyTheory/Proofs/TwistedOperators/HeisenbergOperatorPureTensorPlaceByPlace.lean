import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAwayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLatticeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorHeis

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p]

theorem wAt_wAt_ne {p q : Place D} (h : p ≠ q) (w : WO S T) : wAt p (wAt q w) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h, zero_smul]

theorem wAt_off {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∉ P) :
    wAt p w = wAt p r := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [e, Finset.sum_eq_zero, zero_add]
  intro q hq
  rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (fun hpq => hp (hpq ▸ hq)), zero_smul]

theorem wAt_on {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∈ P) :
    wAt p r = 0 := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [Finset.sum_eq_single p (fun q _ hqp => by rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (Ne.symm hqp), zero_smul])
    (fun hn => absurd hp hn), (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p] at e
  exact add_left_cancel (e.symm.trans (add_zero _).symm)

theorem symplO_wAt (p : Place D) (x y : WO S T) : symplO S T (wAt p x) y = symplO S T x (wAt p y) := by
  rw [wAt_eq_smul, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p]

private theorem symplO_sum_wAt_left (P : Finset (Place D)) (x y : WO S T) :
    symplO S T (∑ q ∈ P, wAt q x) y = ∑ q ∈ P, symplO S T (wAt q x) (wAt q y) := by
  induction P using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.SplitScalar.symplO_zero_left]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, GlobalTheory.LatVac.symplO_add_left, ih, ← symplO_wAt, wAt_wAt]

private theorem wAt_add' (p : Place D) (x y : WO S T) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem symplO_split {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplO S T w w' = ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') + symplO S T r r' := by
  have hr : ∀ q ∈ P, wAt q r = 0 := fun q hq => wAt_on h hq
  have hr' : ∀ q ∈ P, wAt q r' = 0 := fun q hq => wAt_on h' hq
  have hB : ∀ q ∈ P, wAt q (∑ q' ∈ P, wAt q' w') = wAt q w' := by
    intro q hq
    have e : wAt q w' = wAt q (∑ q' ∈ P, wAt q' w' + r') := by rw [← h']
    rw [wAt_add', hr' q hq, add_zero] at e
    exact e.symm
  have s1 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q (∑ q' ∈ P, wAt q' w')) =
      ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') :=
    Finset.sum_congr rfl fun q hq => by rw [hB q hq]
  have s2 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q r') = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr' q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  have s3 : ∑ q ∈ P, symplO S T (wAt q w') (wAt q r) = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  conv_lhs => rw [h, h']
  rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right,
    symplO_sum_wAt_left, symplO_sum_wAt_left, GlobalTheory.SplitScalar.symplO_skew S T (∑ q ∈ P, wAt q w') r,
    symplO_sum_wAt_left, s1, s2, s3, add_zero, neg_zero, zero_add]

variable {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem cocycle_two (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {u u' : WO S T}
    (hu : u ∈ latO S T ΛS ΛT fun _ => True) (hu' : u' ∈ latO S T ΛS ΛT fun _ => True) :
    ψ (symplOH S T (2 • u) (2 • u')) = 1 := by
  have hd : ψ (symplO S T u u') = 1 :=
    ((GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1 u (GlobalTheory.SplitScalar.latO_fin hu)).mp hu u' hu'
  rw [two_nsmul, two_nsmul, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_right,
    GlobalTheory.SplitScalar.symplOH_add_self, AddChar.map_add_eq_mul, hd, one_mul]

theorem wAt_mem {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) (p : Place D) :
    wAt p u ∈ latO S T ΛS ΛT fun _ => True :=
  latO_mono (fun _ _ => trivial) (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).1

theorem wAt_two (p : Place D) (u : WO S T) : wAt p (2 • u) = 2 • wAt p u := by
  rw [two_nsmul, two_nsmul, wAt_eq_smul, wAt_eq_smul, smul_add]

private theorem eq_zero_of_add_self_eq_zero_AF {a : AF D.host.F} (h : a + a = 0) : a = 0 := by
  have h2 : IsUnit (2 : AF D.host.F) := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  rw [← two_mul] at h
  exact h2.mul_right_eq_zero.mp h

private theorem symplOH_eq_sum_wAt_add_of_decomp {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplOH S T w w' = ∑ q ∈ P, symplOH S T (wAt q w) (wAt q w') + symplOH S T r r' := by
  apply sub_eq_zero.mp
  apply eq_zero_of_add_self_eq_zero_AF
  rw [sub_add_sub_comm, GlobalTheory.SplitScalar.symplOH_add_self, add_add_add_comm, ← Finset.sum_add_distrib]
  simp only [GlobalTheory.SplitScalar.symplOH_add_self]
  rw [symplO_split h h', sub_self]

private theorem addChar_sum_eq_prod' (ψ : AddChar (AF D.host.F) ℂ) (s : Finset (Place D)) (g : Place D → AF D.host.F) :
    ψ (∑ p ∈ s, g p) = ∏ p ∈ s, ψ (g p) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

theorem cocycle_prod (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (w w' : WO S T) :
    ∃ P : Finset (Place D), (∀ p ∉ P, ψ (symplOH S T (wAt p w) (wAt p w')) = 1) ∧
      ψ (symplOH S T w w') = ∏ p ∈ P, ψ (symplOH S T (wAt p w) (wAt p w')) := by
  classical
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w'
  obtain ⟨u, hu, hw⟩ := hP₀ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_left _ hx)
  obtain ⟨u', hu', hw'⟩ := hP₁ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_right _ hx)
  refine ⟨P₀ ∪ P₁, fun p hp => ?_, ?_⟩
  · rw [wAt_off hw hp, wAt_off hw' hp, wAt_two, wAt_two]
    exact cocycle_two hψ hS hT (wAt_mem hu p) (wAt_mem hu' p)
  · rw [symplOH_eq_sum_wAt_add_of_decomp hw hw', AddChar.map_add_eq_mul, cocycle_two hψ hS hT hu hu', mul_one,
      addChar_sum_eq_prod']

theorem isPure_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w
  classical
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hB' := hB
  unfold IsBase at hB'
  have hS : IsSelfDualC S ΛS := hB'.2.2.1
  have hT : IsSelfDualC T ΛT := hB'.2.2.2.1
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  unfold IsPure IsRestricted at hx ⊢
  obtain ⟨⟨hloc, hfin⟩, hf, hprod⟩ := hx
  have hxθ : ∀ p, IsThetaFunO ψ S T (x p) := fun p => by
    have hl := hloc p
    unfold IsLocal at hl
    exact hl.1
  have hneg : ∀ (p : Place D) (a : WO S T), wAt p (-a) = -wAt p a := fun p a => by
    rw [wAt_eq_smul, wAt_eq_smul, smul_neg]
  have hadd : ∀ (p : Place D) (a b : WO S T), wAt p (a + b) = wAt p a + wAt p b := fun p a b => by
    rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨u, hu, hwu⟩ := hP₀ P₀ (Finset.Subset.refl _)
  have hvac : ∀ p, p ∉ P₀ → (∀ τ, p ≠ .inr τ) → heisO ψ S T (wAt p w) f₀ = f₀ := by
    intro p hp hτ
    rcases p with v | τ
    · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt hB (.inl v)
      rw [wAt_off hwu hp, wAt_two]
      refine hv.1 _ (latO_mono ?_ (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inl v)).1)
      rintro v' ⟨-, hv'⟩
      exact Sum.inl_injective hv'
    · exact absurd rfl (hτ τ)
  have hfinV : {p : Place D | heisO ψ S T (wAt p w) f₀ ≠ f₀}.Finite := by
    refine ((P₀.finite_toSet).union (Set.finite_range (Sum.inr : D.what₂.Tau → Place D))).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_range, not_or, not_exists] at hc
    exact hp (hvac p hc.1 fun τ h => hc.2 τ h.symm)
  refine ⟨⟨fun p => ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x p) (hxθ p)).2 p (hloc p)).1 w, ?_⟩,
    laws.1 w f hf, fun w' => ?_⟩
  · refine (hfin.union hfinV).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hp
    show heisO ψ S T (wAt p w) (x p) = f₀
    rw [hc.1, hc.2]

  have hfac : ∀ p, ipO μ 𝓕 (heisO ψ S T (wAt p w) (x p)) (heisO ψ S T (wAt p w') f₀) =
      (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w'))) *
        ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (-w + w')) f₀) := by
    intro p
    have I := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p (-w + w')) f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    have J := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p w') f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    rw [(J.2.2.2.2.2.2.1 (wAt p w)).2, laws.2.1, ← hneg, ← hadd, (I.2.2.1 _).2]
  obtain ⟨P, hP1, hP2⟩ := cocycle_prod hψ hS hT (-w) w'
  have hcfin : (Function.mulSupport fun p => (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w')))) ⊆ ↑P := by
    intro p hp
    by_contra hc
    simp only [Function.mem_mulSupport] at hp
    exact hp (by rw [hP1 p (fun h => hc (Finset.mem_coe.mpr h)), map_one])
  have hgfin := (hprod (-w + w')).1
  beta_reduce
  simp only [hfac]
  refine ⟨((P.finite_toSet.subset hcfin).union hgfin).subset (Function.mulSupport_mul _ _), ?_⟩
  have K0 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w' f₀) hf (laws.1 _ _ hf₀)
  have K1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T (-w + w') f₀) hf (laws.1 _ _ hf₀)
  rw [(K0.2.2.2.2.2.2.1 w).2, laws.2.1, (K1.2.2.1 _).2, (hprod (-w + w')).2, hP2, map_prod,
    finprod_mul_distrib (P.finite_toSet.subset hcfin) hgfin, finprod_eq_prod_of_mulSupport_subset _ hcfin]

end GlobalTheory.PlaceTensorHeis
