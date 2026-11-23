import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section

variable {A G : Type} [CommRing A] [Group G] {I : Subgroup G}

private theorem unitHk_apply (hI : HeckePair I) (x : G) (v : fixd (permRep A I) I) :
    (hk (permRep A I) I x v : MonoidAlgebra A (G ⧸ I)) =
      ∑ᶠ q : MulAction.orbit I (x : G ⧸ I), permRep A I (q : G ⧸ I).out v := by
  have hx : FinOrb I I x := hI x
  have e := (hkApply A G _ (permRep A I) I I x hx).1 v
  change ((hk2 (permRep A I) I I x v : fixd (permRep A I) I) : MonoidAlgebra A (G ⧸ I)) = _
  rw [e]
  haveI : Fintype (MulAction.orbit I (x : G ⧸ I)) := Set.Finite.fintype hx
  unfold dc
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private noncomputable def unitHk_e (A : Type) {G : Type} [CommRing A] [Group G] (I : Subgroup G) :
    fixd (permRep A I) I :=
  ⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => by
    rw [Representation.ofMulAction_single]
    congr 1
    exact QuotientGroup.eq.2 (by simpa using hu)⟩

private noncomputable def unitHk_phi (v : fixd (permRep A I) I) :
    MonoidAlgebra A (G ⧸ I) →ₗ[A] MonoidAlgebra A (G ⧸ I) :=
  (MonoidAlgebra.basis (G ⧸ I) A).constr A fun q => permRep A I q.out v

private theorem unitHk_phi_single (v : fixd (permRep A I) I) (g : G) :
    unitHk_phi v (MonoidAlgebra.single (g : G ⧸ I) 1) = permRep A I g v := by
  unfold unitHk_phi
  have hb : MonoidAlgebra.single (g : G ⧸ I) (1 : A) = MonoidAlgebra.basis (G ⧸ I) A (g : G ⧸ I) := by simp
  rw [hb, Module.Basis.constr_basis]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I g
  rw [hh, map_mul, Module.End.mul_apply, v.2 h h.2]

private theorem unitHk_phi_comm (v : fixd (permRep A I) I) (g : G) (w : MonoidAlgebra A (G ⧸ I)) :
    unitHk_phi v (permRep A I g w) = permRep A I g (unitHk_phi v w) := by
  have key : unitHk_phi v ∘ₗ permRep A I g = permRep A I g ∘ₗ unitHk_phi v := by
    refine (MonoidAlgebra.basis (G ⧸ I) A).ext fun q => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hb : MonoidAlgebra.basis (G ⧸ I) A (h : G ⧸ I) = MonoidAlgebra.single (h : G ⧸ I) 1 := by simp
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hb]
    have hs : permRep A I g (MonoidAlgebra.single (h : G ⧸ I) 1) =
        MonoidAlgebra.single ((g * h : G) : G ⧸ I) 1 := Representation.ofMulAction_single _ _ _
    rw [hs, unitHk_phi_single, unitHk_phi_single, map_mul, Module.End.mul_apply]
  exact LinearMap.congr_fun key w

private theorem unitHk_alg_comm (hI : HeckePair I) (v : fixd (permRep A I) I) (T : Module.End A (fixd (permRep A I) I))
    (hT : T ∈ HkAlg A I) : ∀ w w' : fixd (permRep A I) I, unitHk_phi v w = w' → unitHk_phi v (T w) = T w' := by
  unfold HkAlg at hT
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨x, rfl⟩ := hT
    intro w w' hw
    haveI : Fintype (MulAction.orbit I (x : G ⧸ I)) := Set.Finite.fintype (hI x)
    rw [unitHk_apply hI, unitHk_apply hI, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, ← hw]
    simp only [unitHk_phi_comm]
  | algebraMap r =>
    intro w w' hw
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.one_apply, Submodule.coe_smul, Submodule.coe_smul, map_smul, hw]
  | add T1 T2 _ _ h1 h2 =>
    intro w w' hw
    rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, map_add, h1 w w' hw, h2 w w' hw]
  | mul T1 T2 _ _ h1 h2 =>
    intro w w' hw
    rw [Module.End.mul_apply, Module.End.mul_apply]
    exact h1 _ _ (h2 w w' hw)

private theorem unitHk_inj (hI : HeckePair I) (T : Module.End A (fixd (permRep A I) I))
    (hT : T ∈ HkAlg A I) (h : T (unitHk_e A I) = unitHk_e A I) : T = 1 := by
  apply LinearMap.ext
  intro v
  have he : unitHk_phi v (unitHk_e A I : MonoidAlgebra A (G ⧸ I)) = v := by
    show unitHk_phi v (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = v
    rw [unitHk_phi_single, map_one, Module.End.one_apply]
  have key := unitHk_alg_comm hI v T hT (unitHk_e A I) v he
  rw [h, he] at key
  rw [Module.End.one_apply]
  exact Subtype.ext key.symm

open Classical in
private theorem unitHk_coeff (hI : HeckePair I) (x : G) (p : G ⧸ I) :
    (hk (permRep A I) I x (unitHk_e A I) : MonoidAlgebra A (G ⧸ I)).coeff p =
      if p ∈ MulAction.orbit I (x : G ⧸ I) then 1 else 0 := by
  haveI : Fintype (MulAction.orbit I (x : G ⧸ I)) := Set.Finite.fintype (hI x)
  rw [unitHk_apply hI, finsum_eq_sum_of_fintype]
  have hs : ∀ q : MulAction.orbit I (x : G ⧸ I),
      permRep A I (q : G ⧸ I).out (unitHk_e A I : MonoidAlgebra A (G ⧸ I)) = MonoidAlgebra.single (q : G ⧸ I) 1 := by
    intro q
    have h1 : permRep A I (q : G ⧸ I).out (MonoidAlgebra.single ((1 : G) : G ⧸ I) (1 : A)) =
        MonoidAlgebra.single ((q : G ⧸ I).out • ((1 : G) : G ⧸ I)) 1 := Representation.ofMulAction_single _ _ _
    refine h1.trans ?_
    congr 1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.out_eq']
  simp only [hs, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply]
  by_cases hp : p ∈ MulAction.orbit I (x : G ⧸ I)
  · rw [if_pos hp, Finset.sum_eq_single ⟨p, hp⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro e
      exact hq (Subtype.ext e)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro e
    exact hp (e ▸ q.2)

private theorem unitHk_surj (hI : HeckePair I) (v : fixd (permRep A I) I) :
    ∃ T ∈ HkAlg A I, T (unitHk_e A I) = v := by
  classical
  suffices H : ∀ n (v : fixd (permRep A I) I),
      ((v : MonoidAlgebra A (G ⧸ I)).coeff.support.card = n) → ∃ T ∈ HkAlg A I, T (unitHk_e A I) = v from
    H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hv
  by_cases h0 : (v : MonoidAlgebra A (G ⧸ I)).coeff.support = ∅
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [LinearMap.zero_apply]
    apply Subtype.ext
    apply MonoidAlgebra.ext
    rw [Finsupp.support_eq_empty] at h0
    rw [h0, Submodule.coe_zero, MonoidAlgebra.coeff_zero]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 h0
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    set c := (v : MonoidAlgebra A (G ⧸ I)).coeff (x : G ⧸ I) with hc
    have hT1 : c • hk (permRep A I) I x ∈ HkAlg A I :=
      Subalgebra.smul_mem _
        (show hk (permRep A I) I x ∈ HkAlg A I from Algebra.subset_adjoin (Set.mem_range_self x)) c
    have inv : ∀ q ∈ MulAction.orbit I (x : G ⧸ I), (v : MonoidAlgebra A (G ⧸ I)).coeff q = c := by
      rintro q ⟨u, rfl⟩
      have hv' : permRep A I (u : G) (v : MonoidAlgebra A (G ⧸ I)) = v := v.2 u u.2
      show (v : MonoidAlgebra A (G ⧸ I)).coeff ((u : G) • (x : G ⧸ I)) = c
      calc (v : MonoidAlgebra A (G ⧸ I)).coeff ((u : G) • (x : G ⧸ I))
          = (permRep A I (u : G) (v : MonoidAlgebra A (G ⧸ I))).coeff ((u : G) • (x : G ⧸ I)) := by rw [hv']
        _ = (v : MonoidAlgebra A (G ⧸ I)).coeff ((u : G)⁻¹ • (u : G) • (x : G ⧸ I)) :=
          Representation.ofMulAction_apply _ _ _
        _ = c := by rw [inv_smul_smul]
    set v' : fixd (permRep A I) I := v - c • hk (permRep A I) I x (unitHk_e A I) with hv'
    have hco : ∀ q, (v' : MonoidAlgebra A (G ⧸ I)).coeff q =
        (v : MonoidAlgebra A (G ⧸ I)).coeff q - c * (if q ∈ MulAction.orbit I (x : G ⧸ I) then 1 else 0) := by
      intro q
      rw [← unitHk_coeff hI x q, hv']
      simp
    have hsub : (v' : MonoidAlgebra A (G ⧸ I)).coeff.support ⊂ (v : MonoidAlgebra A (G ⧸ I)).coeff.support := by
      refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨(x : G ⧸ I), hp, ?_⟩
      · intro q hq
        rw [Finsupp.mem_support_iff] at hq ⊢
        intro hq0
        apply hq
        rw [hco]
        by_cases ho : q ∈ MulAction.orbit I (x : G ⧸ I)
        · rw [inv q ho] at hq0
          exact absurd hq0 (Finsupp.mem_support_iff.1 hp)
        · rw [if_neg ho, hq0]
          simp
      · rw [Finsupp.mem_support_iff, not_not, hco, if_pos (MulAction.mem_orbit_self _)]
        simp [hc]
    obtain ⟨T', hT', hTe⟩ := ih _ (hv ▸ Finset.card_lt_card hsub) v' rfl
    refine ⟨T' + c • hk (permRep A I) I x, Subalgebra.add_mem _ hT' hT1, ?_⟩
    rw [LinearMap.add_apply, hTe, hv', LinearMap.smul_apply, sub_add_cancel]

private theorem unitHk_unit (hI : HeckePair I) (T : HkAlg A I)
    (h : IsUnit (T : Module.End A (fixd (permRep A I) I))) : IsUnit T := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨T', hT', hT'e⟩ := unitHk_surj hI (((U⁻¹ : (Module.End A (fixd (permRep A I) I))ˣ) :
    Module.End A (fixd (permRep A I) I)) (unitHk_e A I))
  have h1 : (T : Module.End A (fixd (permRep A I) I)) * T' = 1 := by
    refine unitHk_inj hI _ (Subalgebra.mul_mem _ T.2 hT') ?_
    rw [Module.End.mul_apply, hT'e, ← hU, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have h2 : T' = ((U⁻¹ : (Module.End A (fixd (permRep A I) I))ˣ) : Module.End A (fixd (permRep A I) I)) := by
    calc T' = ((U⁻¹ : (Module.End A (fixd (permRep A I) I))ˣ) : Module.End A (fixd (permRep A I) I)) *
          ((U : Module.End A (fixd (permRep A I) I)) * T') := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hU, h1, mul_one]
  refine ⟨⟨T, ⟨T', hT'⟩, Subtype.ext h1, Subtype.ext ?_⟩, rfl⟩
  show T' * (T : Module.End A (fixd (permRep A I) I)) = 1
  rw [h2, ← hU, Units.inv_mul]

end

theorem UpperTheory.V.AlgebraTools.unitHk :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A], IsUnit (resCard k : A) → (∀ w : Equiv.Perm (Fin n), IsUnit (hT A (iwC k n ⊤) (pm k n w))) ∧ ∀ t : Fin n → kˣ, Dom t → IsUnit (hT A (iwC k n ⊤) (diagT k (Fin n) t)) := by
  intro k _ _ _ _ n A _ hq
  have hI := (heckePairIwC k n ⊤).1
  exact ⟨fun w => unitHk_unit hI _ (permUnit k n ⊤ A _ _ w hq),
    fun t ht => unitHk_unit hI _ ((domMul k n ⊤ A _ _).2.1 hq t ht)⟩
