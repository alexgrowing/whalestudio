import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsAddBlock
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbAddBlock

variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}

def varSplit (ι : K → Type) (N : ℕ) : (Σ o, addBlock ι N o) ≃ Fin (N + 1) ⊕ (Σ k, ι k) where
  toFun v := match v with
    | ⟨none, j⟩ => Sum.inl j
    | ⟨some k, i⟩ => Sum.inr ⟨k, i⟩
  invFun w := match w with
    | Sum.inl j => ⟨none, j⟩
    | Sum.inr v => addBlockIncl ι N v
  left_inv := by rintro ⟨_ | k, i⟩ <;> rfl
  right_inv := by rintro (j | ⟨k, i⟩) <;> rfl

def newVar (ι : K → Type) (N : ℕ) : Fin (N + 1) → (Σ o, addBlock ι N o) := fun j => ⟨none, j⟩

omit [DecidableEq K] in
theorem addBlockIncl_injective : Function.Injective (addBlockIncl ι N) := by
  intro v w h
  simp only [addBlockIncl] at h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  exact Sigma.ext (Option.some.inj h1) h2

omit [DecidableEq K] in
theorem newVar_injective : Function.Injective (newVar ι N) := by
  intro i j h
  simp only [newVar] at h
  exact eq_of_heq (Sigma.mk.inj h).2

def splitEquiv (F : Type u) [Field F] (ι : K → Type) (N : ℕ) :
    MRing (addBlock ι N) F ≃ₐ[F] MvPolynomial (Fin (N + 1)) (MRing ι F) :=
  (renameEquiv F (varSplit ι N)).trans (sumAlgEquiv F (Fin (N + 1)) (Σ k, ι k))

variable {F : Type u} [Field F]

omit [DecidableEq K] in

theorem splitEquiv_rename_incl (p : MRing ι F) :
    splitEquiv F ι N (rename (addBlockIncl ι N) p) = C p := by
  have h : (splitEquiv F ι N).toAlgHom.comp (rename (addBlockIncl ι N)) =
      IsScalarTower.toAlgHom F (MRing ι F) (MvPolynomial (Fin (N + 1)) (MRing ι F)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨k, i⟩
    simp [splitEquiv, varSplit, addBlockIncl, sumAlgEquiv_X_inr, MvPolynomial.algebraMap_eq]
  simpa [MvPolynomial.algebraMap_eq] using DFunLike.congr_fun h p

omit [DecidableEq K] in

theorem splitEquiv_rename_newVar (q : MvPolynomial (Fin (N + 1)) F) :
    splitEquiv F ι N (rename (newVar ι N) q) = map C q := by
  have h : (splitEquiv F ι N).toRingHom.comp (rename (newVar ι N)).toRingHom =
      (map C : MvPolynomial (Fin (N + 1)) F →+* MvPolynomial (Fin (N + 1)) (MRing ι F)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [splitEquiv, MvPolynomial.algebraMap_eq]
    · intro j
      simp [splitEquiv, varSplit, newVar, sumAlgEquiv_X_inl]
  exact DFunLike.congr_fun h q

def comb (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) : (Σ o, addBlock ι N o) →₀ ℕ :=
  Finsupp.mapDomain (addBlockIncl ι N) d + Finsupp.mapDomain (newVar ι N) a

omit [DecidableEq K] in
theorem monomial_comb (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) (c : F) :
    monomial (comb d a) c =
      rename (addBlockIncl ι N) (monomial d c) * rename (newVar ι N) (monomial a 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul, mul_one]
  rfl

omit [DecidableEq K] in
theorem splitEquiv_monomial_comb (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) (c : F) :
    splitEquiv F ι N (monomial (comb d a) c) = monomial a (monomial d c) := by
  rw [monomial_comb, map_mul, splitEquiv_rename_incl, splitEquiv_rename_newVar, map_monomial,
    C_mul_monomial, map_one, mul_one]

omit [DecidableEq K] in

theorem map_splitEquiv (I : Ideal (MRing ι F)) :
    (addBlockPrime N I).map (splitEquiv F ι N) = I.map C := by
  have h : (splitEquiv F ι N).toRingEquiv.toRingHom.comp (rename (addBlockIncl ι N)).toRingHom =
      (C : MRing ι F →+* MvPolynomial (Fin (N + 1)) (MRing ι F)) :=
    RingHom.ext fun p => by simpa using splitEquiv_rename_incl (N := N) p
  change Ideal.map (splitEquiv F ι N).toRingEquiv.toRingHom
    (Ideal.map (rename (addBlockIncl ι N)).toRingHom I) = _
  rw [Ideal.map_map, h]

omit [DecidableEq K] in

theorem comb_decomp (μ : (Σ o, addBlock ι N o) →₀ ℕ) :
    comb (μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn)
      (μ.comapDomain (newVar ι N) newVar_injective.injOn) = μ := by
  have h1 : ∀ j : Fin (N + 1), comb (μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn)
      (μ.comapDomain (newVar ι N) newVar_injective.injOn) (newVar ι N j) = μ (newVar ι N j) := by
    intro j
    have hn : newVar ι N j ∉ Set.range (addBlockIncl ι N) := by
      rintro ⟨v, hv⟩
      simpa [addBlockIncl, newVar] using congrArg Sigma.fst hv
    rw [comb, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hn,
      Finsupp.mapDomain_apply newVar_injective, Finsupp.comapDomain_apply, zero_add]
  have h2 : ∀ v : (Σ k, ι k), comb (μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn)
      (μ.comapDomain (newVar ι N) newVar_injective.injOn) (addBlockIncl ι N v) =
        μ (addBlockIncl ι N v) := by
    intro v
    have hn : addBlockIncl ι N v ∉ Set.range (newVar ι N) := by
      rintro ⟨j, hj⟩
      simpa [addBlockIncl, newVar] using congrArg Sigma.fst hj
    rw [comb, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hn,
      Finsupp.mapDomain_apply addBlockIncl_injective, Finsupp.comapDomain_apply, add_zero]
  ext ⟨_ | k, i⟩
  · exact h1 i
  · exact h2 ⟨k, i⟩

theorem weight_comb (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (blockWeight (addBlock ι N)) (comb d a) =
      fun o => Option.elim o (∑ j, a j) (Finsupp.weight (blockWeight ι) d) := by
  have hw : ∀ {α : Type} (f : α → (Σ o, addBlock ι N o)) (x : α →₀ ℕ),
      Finsupp.weight (blockWeight (addBlock ι N)) (Finsupp.mapDomain f x) =
        Finsupp.weight (blockWeight (addBlock ι N) ∘ f) x := by
    intro α f x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy]
    | single v n => rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]; rfl
  rw [comb, map_add, hw, hw]
  ext o
  cases o with
  | none =>
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWeight, addBlockIncl, newVar]
    exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => Finsupp.notMem_support_iff.mp hj
  | some k =>
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWeight, Pi.single_apply,
      addBlockIncl, newVar]

variable [Fintype K] [∀ k, Fintype (ι k)]

theorem finrank_gradedPiece (I : Ideal (MRing ι F)) (M : Option K → ℕ) :
    Module.finrank F (gradedPiece (addBlockPrime N I) M) =
      Module.finrank F (gradedPiece I (fun k => M (some k))) * (M none + N).choose N := by
  classical
  set m' : K → ℕ := fun k => M (some k) with hm'
  set J := addBlockPrime N I with hJ
  set E := (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag (M none) with hEdef
  have hE : E.card = (M none + N).choose N := by
    rw [hEdef, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
      show N + 1 + M none - 1 = M none + N by omega, Nat.choose_symm_add]
  have hsfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m'}.Finite :=
    finite_monomials_of_multidegree m'
  obtain ⟨B, hBT, hBspan, hBind⟩ := exists_linearIndependent F
    ((fun d => Ideal.Quotient.mk I (monomial d (1 : F))) ''
      {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m'})
  have hBfin : B.Finite := (hsfin.image _).subset hBT
  let : Fintype B := hBfin.fintype
  have hlift : ∀ x : B, ∃ d, d ∈ {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m'} ∧
      Ideal.Quotient.mk I (monomial d (1 : F)) = x := fun x => hBT x.2
  choose lift hlift_s hlift_v using hlift
  have hF : Module.finrank F (gradedPiece I m') = Fintype.card B := by
    have h := finrank_span_eq_card hBind
    rw [Subtype.range_coe] at h
    rw [gradedPiece_eq_span, ← hBspan, h]
  let v : B × E → MRing (addBlock ι N) F ⧸ J :=
    fun p => Ideal.Quotient.mk J (monomial (comb (lift p.1) p.2.1) (1 : F))
  have hind : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hs := sum_smul_mk_monomial F J (fun q : B × E => comb (lift q.1) q.2.1) g
    have hg' : (∑ q : B × E, monomial (comb (lift q.1) q.2.1) (g q)) ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hs]
      exact hg
    have hmem := Ideal.mem_map_of_mem (splitEquiv F ι N) hg'
    rw [hJ, map_splitEquiv, map_sum] at hmem
    simp only [splitEquiv_monomial_comb] at hmem
    have hc := (mem_map_C_iff.mp hmem) p.2.1
    rw [coeff_sum, Fintype.sum_prod_type] at hc
    simp only [coeff_monomial] at hc
    have hx : ∀ x : B, (∑ a : E, if a.1 = p.2.1 then monomial (lift x) (g (x, a)) else 0) =
        monomial (lift x) (g (x, p.2)) := by
      intro x
      rw [Fintype.sum_eq_single p.2 fun a ha => if_neg fun h => ha (Subtype.ext h), if_pos rfl]
    simp only [hx] at hc
    have hs' := sum_smul_mk_monomial F I lift (fun x => g (x, p.2))
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hs'] at hc
    simp only [hlift_v] at hc
    exact Fintype.linearIndependent_iff.mp hBind (fun x => g (x, p.2)) hc p.1
  have hspan : Submodule.span F (Set.range v) = gradedPiece J M := by
    rw [gradedPiece_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      refine Submodule.subset_span ⟨comb (lift p.1) p.2.1, ?_, rfl⟩
      show Finsupp.weight _ _ = M
      rw [weight_comb]
      funext o
      cases o with
      | none => exact (Finset.mem_finsuppAntidiag.mp p.2.2).1
      | some k => exact congrFun (hlift_s p.1) k
    · rw [Submodule.span_le]
      rintro _ ⟨μ, hμ, rfl⟩
      set d := μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn with hd_def
      set a := μ.comapDomain (newVar ι N) newVar_injective.injOn with ha_def
      have hμ' : Finsupp.weight (blockWeight (addBlock ι N)) (comb d a) = M := by
        rw [comb_decomp]; exact hμ
      rw [weight_comb] at hμ'
      have hd : Finsupp.weight (blockWeight ι) d = m' := funext fun k => congrFun hμ' (some k)
      have ha : a ∈ E := Finset.mem_finsuppAntidiag.mpr ⟨congrFun hμ' none, Finset.subset_univ _⟩
      have hmem : Ideal.Quotient.mk I (monomial d (1 : F)) ∈
          Submodule.span F (Set.range ((↑) : B → MRing ι F ⧸ I)) := by
        rw [Subtype.range_coe, hBspan]
        exact Submodule.subset_span ⟨d, hd, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
      have hc' : ∑ x, c x • Ideal.Quotient.mk I (monomial (lift x) (1 : F)) =
          Ideal.Quotient.mk I (monomial d (1 : F)) := by
        simpa only [hlift_v] using hc
      rw [sum_smul_mk_monomial, Ideal.Quotient.eq] at hc'
      have h' : rename (addBlockIncl ι N) (∑ x, monomial (lift x) (c x) - monomial d 1) *
          rename (newVar ι N) (monomial a 1) ∈ J :=
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc')
      rw [map_sub, map_sum, sub_mul, Finset.sum_mul] at h'
      simp only [← monomial_comb] at h'
      rw [← Ideal.Quotient.eq] at h'
      have hs := sum_smul_mk_monomial F J (fun x : B => comb (lift x) a) c
      have hgoal : Ideal.Quotient.mk J (monomial μ (1 : F)) =
          Ideal.Quotient.mk J (monomial (comb d a) (1 : F)) := by
        rw [comb_decomp]
      show Ideal.Quotient.mk J (monomial μ (1 : F)) ∈ _
      rw [hgoal, ← h', ← hs]
      exact Submodule.sum_mem _ fun x _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(x, ⟨a, ha⟩), rfl⟩)
  rw [← hspan, finrank_span_eq_card hind, Fintype.card_prod, ← hF, Fintype.card_coe, hE]

end HilbAddBlock

theorem HilbAddBlock.proof : HilbAddBlock.Statement := by
  intro F _ K _ _ ι _ I N m
  unfold hilbFn projSpaceHilb
  by_cases h : ∀ o, 0 ≤ m o
  · rw [if_pos h, if_pos (fun k => h (some k)), if_pos (h none),
      HilbAddBlock.finrank_gradedPiece]
    push_cast
    rfl
  · rw [if_neg h]
    push Not at h
    obtain ⟨o, ho⟩ := h
    cases o with
    | none => rw [if_neg (not_le.mpr ho), mul_zero]
    | some k => rw [if_neg (fun h' => absurd (h' k) (not_le.mpr ho)), zero_mul]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
