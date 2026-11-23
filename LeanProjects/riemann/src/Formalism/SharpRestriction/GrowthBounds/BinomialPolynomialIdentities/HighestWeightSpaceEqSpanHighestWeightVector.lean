import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DualWeightVectorApplyEqZeroOfNeNeg
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem dualOperators_commutator_relation (E : GLOps n K V)
    (hR : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b c d : Fin n) :
    dualOps E a b * dualOps E c d - dualOps E c d * dualOps E a b =
      (if b = c then dualOps E a d else 0) - (if d = a then dualOps E c b else 0) := by
  have hm : ∀ f g : Module.End K V, f.dualMap * g.dualMap = (g * f).dualMap :=
    fun f g => LinearMap.ext fun φ => LinearMap.ext fun x => rfl
  have hs : ∀ f g : Module.End K V, (f - g).dualMap = f.dualMap - g.dualMap :=
    fun f g => LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]
  have hn : ∀ f : Module.End K V, (-f).dualMap = -f.dualMap :=
    fun f => LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]
  have h0 : (0 : Module.End K V).dualMap = 0 :=
    LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]
  simp only [Formalism.MainNotions.CovariantDegrees.dualOps, neg_mul_neg, hm]
  rw [← hs, show E c d * E a b - E a b * E c d = -(E a b * E c d - E c d * E a b) from (neg_sub _ _).symm,
    hR a b c d]
  split_ifs <;> simp only [hn, hs, h0] <;> abel

theorem dualOperators_iSup_weightSpace_eq_top [CharZero K] [FiniteDimensional K V] (E : GLOps n K V)
    (hE : (⨆ nu : Fin n → ℤ, weightSp E nu) = ⊤) : (⨆ nu : Fin n → ℤ, weightSp (dualOps E) nu) = ⊤ := by
  classical
  have hspan : Submodule.span K (⋃ ν : Fin n → ℤ, (weightSp E ν : Set V)) = ⊤ := by
    rw [Submodule.span_iUnion]
    simpa only [Submodule.span_eq] using hE
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (⋃ ν : Fin n → ℤ, (weightSp E ν : Set V))
  have hbtop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B : Module.Basis b K V := Module.Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis B
  have hwt : ∀ (x : V) (ν : Fin n → ℤ), x ∈ weightSp E ν → ∀ a, E a a x = ((ν a : ℤ) : K) • x := by
    intro x ν hx a
    unfold Formalism.MainNotions.G.weightSp at hx
    have hx' := (Submodule.mem_iInf _).1 hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx'
    simpa using hx'
  rw [eq_top_iff, ← B.dualBasis.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨ν, hν⟩ := Set.mem_iUnion.1 (hbs i.2)
  refine Submodule.mem_iSup_of_mem (-ν) ?_
  unfold Formalism.MainNotions.G.weightSp
  refine (Submodule.mem_iInf _).2 fun a => ?_
  rw [LinearMap.mem_ker]
  refine B.ext fun j => ?_
  obtain ⟨ν', hν'⟩ := Set.mem_iUnion.1 (hbs j.2)
  have hBj : (B j : V) = j := Module.Basis.mk_apply hbli hbtop j
  have hj : (B j : V) ∈ weightSp E ν' := by rw [hBj]; exact hν'
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.MainNotions.CovariantDegrees.dualOps,
    LinearMap.neg_apply, LinearMap.dualMap_apply, LinearMap.zero_apply]
  rw [hwt _ _ hj a, map_smul, B.dualBasis_apply_self]
  by_cases hij : j = i
  · have h1 : E a a (B j) = ((ν' a : ℤ) : K) • B j := hwt _ _ hj a
    have h2 : E a a (B j) = ((ν a : ℤ) : K) • B j := hwt _ _ (by rw [hBj, hij]; exact hν) a
    have hK : ((ν' a : ℤ) : K) = ν a := smul_left_injective K (B.ne_zero j) (h1.symm.trans h2)
    rw [if_pos hij, hK]
    simp
  · rw [if_neg hij]
    simp

theorem dualOperators_isGLRep [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) : IsGLRep (dualOps E) := ⟨dualOperators_commutator_relation E hE.1, fun _ => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩,
    dualOperators_iSup_weightSpace_eq_top E hE.2.2⟩

theorem dominant_dualWeight {mu : Fin n → ℤ} (h : Dominant mu) : Dominant (dualWt mu) := by
  have h' : Antitone mu := h
  intro a b hab
  show -mu (Fin.rev b) ≤ -mu (Fin.rev a)
  exact neg_le_neg (h' (Fin.rev_le_rev.2 hab))

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem highestWeightSpace_eq_span_highestWeightVector [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) {x : V}
    (hx : x ∈ weightSp E lam) : ∃ c : KK O, x = c • v := by
  obtain ⟨hR, -, ⟨hv0, hvl, hraise⟩, hspan⟩ := hI
  have rel := hR.1
  have hwt : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν ↔ ∀ a, E a a y = ((ν a : ℤ) : KK O) • y := by
    intro ν y
    unfold Formalism.MainNotions.G.weightSp
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hshift : ∀ (a b : Fin n) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
      E a b y ∈ weightSp E (ν + Pi.single a 1 - Pi.single b 1) := by
    intro a b ν y hy
    rw [hwt] at hy ⊢
    intro c
    have h := congrArg (fun T : Module.End (KK O) V => T y) (rel c c a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    rcases eq_or_ne c a with rfl | hca <;> rcases eq_or_ne b c with rfl | hbc
    · simp [Pi.single_apply]
    · simp only [eq_self_iff_true, if_true, if_neg hbc, LinearMap.zero_apply, sub_zero, Pi.add_apply,
        Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hbc.symm, Int.cast_add, Int.cast_one, add_smul,
        one_smul]
      abel
    · simp only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub, Pi.add_apply,
        Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hca, add_zero, Int.cast_sub, Int.cast_one, sub_smul,
        one_smul]
      abel
    · simp [Pi.single_apply, hca, hbc, hbc.symm]
  let L : Submonoid (Module.End (KK O) V) := Submonoid.closure {T | ∃ a b, b < a ∧ T = E a b}
  let U : Submodule (KK O) V := Submodule.span (KK O) {y | ∃ u ∈ L, y = u v}
  have hLU : ∀ u ∈ L, ∀ y ∈ U, u y ∈ U := by
    intro u hu y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      exact Submodule.subset_span ⟨u * w, L.mul_mem hu hw, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact U.add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul]
      exact U.smul_mem c hy
  have hv : v ∈ U := Submodule.subset_span ⟨1, L.one_mem, rfl⟩
  have base : ∀ c d, E c d v ∈ U := by
    intro c d
    rcases lt_trichotomy c d with h | rfl | h
    · rw [hraise c d h]
      exact U.zero_mem
    · rw [(hwt lam v).1 hvl c]
      exact U.smul_mem _ hv
    · exact Submodule.subset_span ⟨E c d, Submonoid.subset_closure ⟨c, d, h, rfl⟩, rfl⟩
  have key : ∀ u ∈ L, ∀ c d, E c d (u v) ∈ U := by
    intro u hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro c d
      exact base c d
    | mul_left x hx y hy ih =>
      intro c d
      obtain ⟨a, b, hab, rfl⟩ := hx
      rw [Module.End.mul_apply]
      have h := congrArg (fun T : Module.End (KK O) V => T (y v)) (rel c d a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      refine U.add_mem (U.sub_mem ?_ ?_) (hLU _ (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) _ (ih c d))
      · split_ifs
        · exact ih c b
        · simp
      · split_ifs
        · exact ih a d
        · simp
  have hEU : ∀ c d, ∀ y ∈ U, E c d y ∈ U := by
    intro c d y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      exact key u hu c d
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact U.add_mem hy hz
    | smul t y _ hy =>
      rw [map_smul]
      exact U.smul_mem t hy
  have hUtop : U = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    induction hu using Submonoid.closure_induction_left with
    | one => exact hv
    | mul_left x hx y _ ih =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      rw [Module.End.mul_apply]
      exact hEU a b _ ih
  have hLw : ∀ u ∈ L, (∃ t : KK O, u v = t • v) ∨ ∃ ν : Fin n → ℤ,
      ∑ c : Fin n, ((c : ℕ) : ℤ) * lam c < ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c ∧ u v ∈ weightSp E ν := by
    intro u hu
    induction hu using Submonoid.closure_induction_left with
    | one => exact Or.inl ⟨1, by simp⟩
    | mul_left x hx y _ ih =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      rw [Module.End.mul_apply]
      right
      have hsum : ∀ ν : Fin n → ℤ, ∑ c : Fin n, ((c : ℕ) : ℤ) * (ν + Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) c =
          ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) := by
        intro ν
        simp only [Pi.add_apply, Pi.sub_apply, mul_sub, mul_add, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      have hpos : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by
        have := Fin.lt_def.1 hab
        omega
      rcases ih with ⟨t, ht⟩ | ⟨ν, hν, hyν⟩
      · refine ⟨lam + Pi.single a 1 - Pi.single b 1, ?_, ?_⟩
        · rw [hsum]
          linarith
        · rw [ht, map_smul]
          exact Submodule.smul_mem _ _ (hshift a b lam v hvl)
      · refine ⟨ν + Pi.single a 1 - Pi.single b 1, ?_, hshift a b ν _ hyν⟩
        rw [hsum]
        linarith
  obtain ⟨H, hHdef⟩ : ∃ H : Module.End (KK O) V, H = ∑ c : Fin n, ((c : ℕ) : KK O) • E c c := ⟨_, rfl⟩
  have hH : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
      H y = ((∑ c : Fin n, ((c : ℕ) : ℤ) * ν c : ℤ) : KK O) • y := by
    intro ν y hy
    rw [hwt] at hy
    rw [hHdef, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hy, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    norm_cast
  obtain ⟨μ0, hμ0⟩ : ∃ μ0 : KK O, μ0 = ((∑ c : Fin n, ((c : ℕ) : ℤ) * lam c : ℤ) : KK O) := ⟨_, rfl⟩
  have hUle : U ≤ Submodule.span (KK O) {v} ⊔ ⨆ (j : KK O) (_ : j ≠ μ0), H.eigenspace j := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    rcases hLw u hu with ⟨t, ht⟩ | ⟨ν, hν, hyν⟩
    · rw [ht]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
    · apply Submodule.mem_sup_right
      have hne : ((∑ c : Fin n, ((c : ℕ) : ℤ) * ν c : ℤ) : KK O) ≠ μ0 := by
        intro heq
        rw [hμ0] at heq
        have := Int.cast_injective heq
        linarith
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne
        ((Module.End.mem_eigenspace_iff).2 (hH ν _ hyν)))
  have hx' : x ∈ Submodule.span (KK O) {v} ⊔ ⨆ (j : KK O) (_ : j ≠ μ0), H.eigenspace j :=
    hUle (hUtop ▸ Submodule.mem_top)
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.1 hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  have hw' : w = x - c • v := by
    rw [← hyw]
    abel
  have hin1 : w ∈ H.eigenspace μ0 := by
    rw [hw', Module.End.mem_eigenspace_iff, map_sub, map_smul, hH lam x hx, hH lam v hvl, ← hμ0, smul_sub, smul_comm c μ0 v]
  have h0 : w = 0 := (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep H) μ0)) w hin1 hw
  rw [h0] at hw'
  exact (sub_eq_zero.1 hw'.symm)

end lattice

section gen

variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem contragredient_span_highestWeight_eq_top (D : Formalism.BasicNotions.D7) [CharZero (KK O)] {E : GLOps n (KK O) V} {mu : Fin n → ℤ} {v : V}
    {v' : Module.Dual (KK O) V} (hI : IsIrrHW E mu v) (hv0 : v' ≠ 0) :
    Submodule.span (KK O) {x | ∃ u ∈ Umon (dualOps E), x = u v'} = ⊤ := by
  have hfd : FiniteDimensional (KK O) V := irreducible_highest_weight_findim hI
  set G' : Submodule (KK O) (Module.Dual (KK O) V) :=
    Submodule.span (KK O) {x | ∃ u ∈ Umon (dualOps E), x = u v'} with hG'
  have hG'st : ∀ a b, ∀ φ ∈ G', dualOps E a b φ ∈ G' := by
    intro a b φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      exact Submodule.subset_span ⟨dualOps E a b * u,
        Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hv'G : v' ∈ G' := Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩
  set Z : Submodule (KK O) V := G'.dualCoannihilator with hZ
  have hZst : ∀ a b, ∀ x ∈ Z, E a b x ∈ Z := by
    intro a b x hx
    rw [hZ, Submodule.mem_dualCoannihilator] at hx ⊢
    intro φ hφ
    have := hx _ (hG'st a b φ hφ)
    rw [dualOperators_apply, neg_eq_zero] at this
    exact this
  obtain ⟨Z', hc, hZ'st⟩ := weight_condition_from_integral_form D (KK O) V n E hI.1 Z hZst
  have hvtop : v ∈ Z ⊔ Z' := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨z, hz, z', hz', hsum⟩ := Submodule.mem_sup.1 hvtop
  have hzw : z ∈ weightSp E mu := by
    rw [mem_weightSpace_iff_diag_scalar]
    intro a
    have h1 : E a a z - (mu a : KK O) • z ∈ Z := Submodule.sub_mem _ (hZst a a z hz) (Submodule.smul_mem _ _ hz)
    have h2 : E a a z' - (mu a : KK O) • z' ∈ Z' :=
      Submodule.sub_mem _ (hZ'st a a z' hz') (Submodule.smul_mem _ _ hz')
    have h3 : (E a a z - (mu a : KK O) • z) + (E a a z' - (mu a : KK O) • z') = 0 := by
      have := mem_weightSpace_iff_diag_scalar.1 hI.2.2.1.2.1 a
      rw [← hsum, map_add, smul_add] at this
      rw [← sub_eq_zero] at this
      rw [← this]
      abel
    have h4 : E a a z - (mu a : KK O) • z = -(E a a z' - (mu a : KK O) • z') := eq_neg_of_add_eq_zero_left h3
    have h5 : E a a z - (mu a : KK O) • z ∈ Z ⊓ Z' := ⟨h1, h4 ▸ Submodule.neg_mem _ h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h5
    exact sub_eq_zero.1 h5
  obtain ⟨c, hcz⟩ := highestWeightSpace_eq_span_highestWeightVector hI hzw
  have hZbot : Z = ⊥ := by
    by_cases hc0 : c = 0
    · have hvZ' : v ∈ Z' := by
        rw [← hsum, hcz, hc0, zero_smul, zero_add]
        exact hz'
      have htop := irreducible_stable_contains_eq_top hI hZ'st hvZ'
      have := hc.inf_eq_bot
      rwa [htop, inf_top_eq] at this
    · exfalso
      have hvZ : v ∈ Z := by
        have : v = c⁻¹ • z := by rw [hcz, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ hz
      have htop := irreducible_stable_contains_eq_top hI hZst hvZ
      apply hv0
      ext x
      have hx : x ∈ Z := htop ▸ Submodule.mem_top
      rw [hZ, Submodule.mem_dualCoannihilator] at hx
      exact hx v' hv'G
  have h6 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := G')
  rw [← hZ, hZbot, Submodule.dualAnnihilator_bot] at h6
  exact h6.symm

end gen

theorem contragredientIrreducible_generated (D : Formalism.BasicNotions.D7) : ContragredientIrreducibleGeneratedByHighestWeight := by
  unfold Formalism.MainNotions.G.ColumnFamilies.ContragredientIrreducibleGeneratedByHighestWeight
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hH
  haveI : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨W, hWf, hvW, hWs⟩ := hI.1.2.1 v
  haveI : FiniteDimensional (KK O) V := by
    have hle : (⊤ : Submodule (KK O) V) ≤ W := by
      rw [← hI.2.2.2, Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      induction hu using Submonoid.closure_induction_left with
      | one => exact hvW
      | mul_left x hx y _ ih =>
        obtain ⟨⟨a, b⟩, rfl⟩ := hx
        exact hWs a b _ ih
    have hWt : W = ⊤ := top_le_iff.1 hle
    subst hWt
    exact Module.Finite.equiv (LinearEquiv.ofTop (⊤ : Submodule (KK O) V) rfl)
  exact ⟨dualOperators_isGLRep E hI.1, dominant_dualWeight hI.2.1, hH, contragredient_span_highestWeight_eq_top D hI hH.1⟩

theorem dualFunctional_lowestWeight_injective (D : Formalism.BasicNotions.D7) : DualFunctionalInjectiveOnLowestWeightSpace := by
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hv'
  have hcz : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  have hI' := contragredientIrreducible_generated D p O S n V E mu v v' hI hv'
  have hdw : dualWt mu = -lowWt mu := rfl
  constructor
  · intro x hx hvx
    rw [← Module.forall_dual_apply_eq_zero_iff (KK O) x]
    intro φ
    have hφ : φ ∈ ⨆ nu : Fin n → ℤ, weightSp (dualOps E) nu := hI'.1.2.2 ▸ Submodule.mem_top
    induction hφ using Submodule.iSup_induction' with
    | mem nu ψ hψ =>
      by_cases hnu : nu = dualWt mu
      · subst hnu
        obtain ⟨c, rfl⟩ := highestWeightSpace_eq_span_highestWeightVector hI' hψ
        rw [LinearMap.smul_apply, hvx, smul_zero]
      · exact dual_weightVector_apply_eq_zero_of_ne_neg E hψ hx (fun h => hnu (h.trans hdw.symm))
    | zero => rfl
    | add a b _ _ ha hb => rw [LinearMap.add_apply, ha, hb, add_zero]
  · intro nu hnu x hx
    refine dual_weightVector_apply_eq_zero_of_ne_neg E hv'.2.1 hx (fun h => hnu ?_)
    have : -lowWt mu = -nu := hdw.symm.trans h
    exact (neg_injective this).symm

end Formalism.MainNotions.G.ColumnFamilies
