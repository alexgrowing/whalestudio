import Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
import ReciprocityTheory.SemistableReduction.AlgAll
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerAeval

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

open IsLocalRing Cardinal

section Fld

variable {F : Type} [Field F]

def constField (K : Type) [Field K] [Algebra K F] {δ : F → F} (h : IsDer δ)
    (hK : ∀ c, δ (algebraMap K F c) = 0) : IntermediateField K F where
  carrier := {x | δ x = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [h.mul, ha, hb, mul_zero, mul_zero, add_zero]
  one_mem' := h.der_one
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [h.add, ha, hb, add_zero]
  zero_mem' := h.der_zero
  algebraMap_mem' c := hK c
  inv_mem' x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]; exact h.der_zero
    · have e := h.mul x x⁻¹
      rw [mul_inv_cancel₀ hx0, h.der_one, hx, mul_zero, add_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_left hx0

theorem kill_adjoin (K : Type) [Field K] [Algebra K F] {δ : F → F} (h : IsDer δ)
    (hK : ∀ c, δ (algebraMap K F c) = 0) (s : Set F) (hs : ∀ x ∈ s, δ x = 0) :
    ∀ x ∈ IntermediateField.adjoin K s, δ x = 0 := by
  intro x hx
  have hle : IntermediateField.adjoin K s ≤ constField K h hK :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => hs y hy)
  exact hle hx

theorem der_aeval {δ : F → F} (h : IsDer δ) {E : Type} [CommRing E] [Algebra E F]
    (hE : ∀ e, δ (algebraMap E F e) = 0) {σ : Type} [Fintype σ] [DecidableEq σ] (t : σ → F)
    (P : MvPolynomial σ E) :
    δ (MvPolynomial.aeval t P) = ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * δ (t i) := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp [hE]
  next p q hp hq =>
    simp only [map_add, h.add, hp, hq, add_mul, Finset.sum_add_distrib]
  next p n hp =>
    have hsingle : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPolynomial.X n : MvPolynomial σ E)) =
        if i = n then 1 else 0 := by
      intro i
      by_cases hi : i = n
      · subst hi
        simp
      · simp [MvPolynomial.pderiv_X, Pi.single_apply, hi, Ne.symm hi]
    simp only [map_mul, MvPolynomial.aeval_X, h.mul, hp, MvPolynomial.pderiv_mul, map_add, hsingle,
      add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem totalDegree_pderiv_lt {E : Type} [CommRing E] {σ : Type} (p : MvPolynomial σ E) (i : σ)
    (h : MvPolynomial.pderiv i p ≠ 0) : (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp h)
  have key : ∀ m ∈ (MvPolynomial.pderiv i p).support, (m.sum fun _ e => e) + 1 ≤ p.totalDegree := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hs : m + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have hle := MvPolynomial.le_totalDegree hs
    rwa [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at hle
  have h1 := key m hm
  have h2 : (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    apply Finset.sup_le
    intro s hs
    have := key s hs
    omega
  omega

theorem algIndep_of_der {E : Type} [Field E] [CharZero E] [Algebra E F] {N : ℕ} (t : Fin N → F)
    (δ : Fin N → F → F) (hδ : ∀ l, IsDer (δ l)) (hE : ∀ l e, δ l (algebraMap E F e) = 0)
    (ht : ∀ l k, δ l (t k) = if k = l then 1 else 0) : AlgebraicIndependent E t := by
  classical
  have main : ∀ n : ℕ, ∀ P : MvPolynomial (Fin N) E, P.totalDegree ≤ n →
      MvPolynomial.aeval t P = 0 → P = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih P hd hP
    have hder : ∀ l, MvPolynomial.pderiv l P = 0 := by
      intro l
      by_contra hne
      have hlt := totalDegree_pderiv_lt P l hne
      apply hne
      refine ih _ (lt_of_lt_of_le hlt hd) (MvPolynomial.pderiv l P) le_rfl ?_
      have hz := der_aeval (hδ l) (hE l) t P
      rw [hP, (hδ l).der_zero] at hz
      simpa [ht] using hz.symm
    have hdeg0 : P.totalDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro s hs
      by_contra hpos
      obtain ⟨l, hl⟩ : ∃ l, s l ≠ 0 := by
        by_contra hall
        push_neg at hall
        have h0 : s = 0 := Finsupp.ext fun a => by simp [hall a]
        simp [h0] at hpos
      have hs' : s - Finsupp.single l 1 + Finsupp.single l 1 = s := by
        ext j
        by_cases hj : j = l
        · subst hj
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same]
          omega
        · simp [Finsupp.single_apply, Ne.symm hj]
      have hc := MvPolynomial.coeff_pderiv (i := l) P (s - Finsupp.single l 1)
      rw [hder l, MvPolynomial.coeff_zero, hs'] at hc
      rw [MvPolynomial.mem_support_iff] at hs
      have h2 : (((s - Finsupp.single l 1 : Fin N →₀ ℕ) l : ℕ) : E) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
      exact hs ((mul_eq_zero.mp hc.symm).resolve_right h2)
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hdeg0
    rw [hdeg0, MvPolynomial.aeval_C] at hP
    have hc0 : MvPolynomial.coeff 0 P = 0 := (map_eq_zero (algebraMap E F)).mp hP
    rw [hdeg0, hc0, MvPolynomial.C_0]
  exact (injective_iff_map_eq_zero (MvPolynomial.aeval (R := E) t)).mpr fun P hP => main _ P le_rfl hP

end Fld

theorem gauss_indep {K Ω U τ : Type} [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U] [Algebra K U]
    [IsScalarTower K Ω U] (V : ValuationSubring U) (T : τ → U) (hT : ∀ q, T q ∈ V)
    (hG : ∀ Q : MvPolynomial τ K, (∀ α, V.valuation (algebraMap K U (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K U (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
    letI : Algebra (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V) :=
      ((algebraMap _ (ResidueField V)).comp (algebraMap _ (ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => residue V ⟨T j, hT j⟩) := by
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω U)
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
  letI _ia : Algebra (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V) :=
    ((algebraMap _ (ResidueField V)).comp
      (algebraMap _ (ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
  classical
  have f0def : ∀ x : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω),
      (((ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
        (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) x : V) : U) =
        algebraMap K U (x : K) := by
    intro x
    show algebraMap Ω U (algebraMap K Ω (x : K)) = _
    exact (IsScalarTower.algebraMap_apply K Ω U _).symm
  have hcomp : ∀ x : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω),
      algebraMap (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V)
        (residue _ x) =
      residue V ((ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
        (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) x) := by
    intro x
    simp only [_ia, _iW, _io, ReciprocityTheory.MultiplicativeHeights.residueAlgebra, RingHom.algebraMap_toAlgebra,
      RingHom.comp_apply, IsLocalRing.ResidueField.map_residue] <;> rfl
  set f0 := (ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
    (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) with hf0
  refine (injective_iff_map_eq_zero (MvPolynomial.aeval
    (R := ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
    (fun j => residue V ⟨T j, hT j⟩))).mpr ?_
  intro R hR
  by_contra hR0
  obtain ⟨Q', rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective R
  have hqU : ((MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q' : V) : U) =
      MvPolynomial.aeval T
        (MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q') := by
    have e1 := MvPolynomial.eval₂_comp_left V.subtype f0 (fun j => (⟨T j, hT j⟩ : V)) Q'
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e2 : V.subtype.comp f0 =
        (algebraMap K U).comp ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype :=
      RingHom.ext fun x => f0def x
    rw [← e2]
    exact e1
  have hres : residue V (MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q') =
      MvPolynomial.aeval (fun j => residue V ⟨T j, hT j⟩) (MvPolynomial.map (residue _) Q') := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e1 := MvPolynomial.eval₂_comp_left (residue V) f0 (fun j => (⟨T j, hT j⟩ : V)) Q'
    have e2 : (residue V).comp f0 =
        (algebraMap (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (ResidueField V)).comp (residue _) :=
      RingHom.ext fun x => (hcomp x).symm
    rw [← e2]
    exact e1
  have hlt : V.valuation ((MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q' : V) : U) < 1 := by
    rw [← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, hres]
    exact hR
  have hc : ∀ α, (MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α =
      ((Q'.coeff α : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω)) : K) := fun α =>
    MvPolynomial.coeff_map _ _ _
  have hle : ∀ α, V.valuation (algebraMap K U
      ((MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α)) ≤ 1 := by
    intro α
    rw [hc, ← f0def]
    exact V.valuation_le_one _
  have hex : ∃ α, V.valuation (algebraMap K U
      ((MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α)) = 1 := by
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hR0
    refine ⟨α, ?_⟩
    rw [MvPolynomial.coeff_map] at hα
    have hu : IsUnit (Q'.coeff α) := by
      by_contra hnu
      apply hα
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
    rw [hc, ← f0def]
    exact (V.valuation_eq_one_iff _).mp (hu.map f0)
  have h1 := hG _ hle hex
  rw [← hqU] at h1
  rw [h1] at hlt
  exact lt_irrefl _ hlt

theorem gauss_direct {F K : Type} [Field F] [Field K] [CharZero K] [Algebra K F] (D N : ℕ)
    (T : Fin (D + 1) × Fin N → F) (y : Fin N → F) (δ : Fin N → F → F) (hδ : ∀ l, IsDer (δ l))
    (hδK : ∀ l c, δ l (algebraMap K F c) = 0) (hδ0 : ∀ l k, δ l (T (0, k)) = if k = l then 1 else 0)
    (hδs : ∀ l (i : Fin D) k, δ l (T (i.succ, k)) = 0) (hδy : ∀ l k, δ l (y k) = -(y k * y l))
    (h1 : ∑ k, T (0, k) * y k = 1)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range T)) F)
    (V : ValuationSubring F)
    (hG : ∀ Q : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, V.valuation (algebraMap K F (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K F (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    ∀ k, y k ∈ V := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  have hT1 : ∀ q, V.valuation (T q) = 1 := by
    intro q
    have := hG (MvPolynomial.X q) (fun α => ?_) ⟨Finsupp.single q 1, ?_⟩
    · simpa using this
    · rw [MvPolynomial.coeff_X']
      split_ifs <;> simp
    · rw [MvPolynomial.coeff_X', if_pos rfl]
      simp
  have hTV : ∀ q, T q ∈ V := fun q => (V.valuation_le_one_iff _).1 (hT1 q).le

  have hTind : AlgebraicIndependent K T := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    by_contra hQ0
    have hne : Q.support.Nonempty := by
      obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hQ0
      exact ⟨β, MvPolynomial.mem_support_iff.mpr hβ⟩
    obtain ⟨α, hα, hmax⟩ := Q.support.exists_max_image (fun β => V.valuation (algebraMap K F (Q.coeff β))) hne
    have hc : Q.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    have hvc : V.valuation (algebraMap K F (Q.coeff α)) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]
      exact (map_ne_zero _).2 hc
    have key := hG (MvPolynomial.C (Q.coeff α)⁻¹ * Q) (fun β => ?_) ⟨α, ?_⟩
    · rw [map_mul, hQ, mul_zero, Valuation.map_zero] at key
      exact zero_ne_one key
    · rw [MvPolynomial.coeff_C_mul, map_mul, Valuation.map_mul, map_inv₀, Valuation.map_inv]
      by_cases hβ : β ∈ Q.support
      · calc (V.valuation (algebraMap K F (Q.coeff α)))⁻¹ * V.valuation (algebraMap K F (Q.coeff β))
            ≤ (V.valuation (algebraMap K F (Q.coeff α)))⁻¹ * V.valuation (algebraMap K F (Q.coeff α)) :=
              by gcongr; exact hmax β hβ
          _ = 1 := inv_mul_cancel₀ hvc
      · rw [MvPolynomial.notMem_support_iff.mp hβ, map_zero, Valuation.map_zero, mul_zero]
        exact zero_le'
    · rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, map_one, Valuation.map_one]

  have hN : ∃ k, y k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at h1
  obtain ⟨j0, -, hj0⟩ := Finset.univ.exists_max_image (fun k => V.valuation (y k))
    (by obtain ⟨k, -⟩ := hN; exact ⟨k, Finset.mem_univ _⟩)
  have hy0 : y j0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hN
    intro h0
    have := hj0 k (Finset.mem_univ _)
    rw [h0, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hk this
  let a : Fin N → F := fun k => y k / y j0
  have haV : ∀ k, V.valuation (a k) ≤ 1 := by
    intro k
    show V.valuation (y k / y j0) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ (hj0 k (Finset.mem_univ _)) zero_le'
  have ha0 : a j0 = 1 := div_self hy0
  have hay : ∀ k, a k * y j0 = y k := fun k => div_mul_cancel₀ _ hy0
  have hδa : ∀ l k, δ l (a k) = 0 := by
    intro l k
    have e := (hδ l).mul (a k) (y j0)
    rw [hay, hδy, hδy] at e
    have e2 : y j0 * δ l (a k) = 0 := by linear_combination (-1 : F) * e + y l * hay k
    exact (mul_eq_zero.mp e2).resolve_left hy0

  let sE : Set F := Set.range (fun q : Fin D × Fin N => T (q.1.succ, q.2)) ∪ Set.range a
  let E : IntermediateField K F := IntermediateField.adjoin K sE
  have hδE : ∀ l (e : E), δ l (algebraMap E F e) = 0 := by
    intro l e
    show δ l (e : F) = 0
    refine kill_adjoin K (hδ l) (hδK l) sE ?_ e e.2
    rintro x (⟨q, rfl⟩ | ⟨k, rfl⟩)
    · exact hδs l q.1 q.2
    · exact hδa l k
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hT0ind : AlgebraicIndependent E (fun k => T (0, k)) :=
    algIndep_of_der _ δ hδ hδE (fun l k => hδ0 l k)

  have hmemT : ∀ (i : Fin D) k, T (i.succ, k) ∈ E := fun i k =>
    IntermediateField.subset_adjoin K sE (Set.mem_union_left _ ⟨(i, k), rfl⟩)
  have hmema : ∀ k, a k ∈ E := fun k =>
    IntermediateField.subset_adjoin K sE (Set.mem_union_right _ ⟨k, rfl⟩)
  haveI : FaithfulSMul K E := (faithfulSMul_iff_algebraMap_injective K E).mpr (algebraMap K E).injective
  haveI : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr (algebraMap E F).injective
  have hadd : Algebra.trdeg K E + Algebra.trdeg E F ≤ Algebra.trdeg K F := trdeg_add_le
  have htF : Algebra.trdeg K F ≤ (((D + 1) * N : ℕ) : Cardinal) := by
    haveI := halg
    calc Algebra.trdeg K F ≤ #(Set.range T) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range T)
      _ ≤ #(Fin (D + 1) × Fin N) := Cardinal.mk_range_le
      _ = (((D + 1) * N : ℕ) : Cardinal) := by simp [Cardinal.mk_fintype]
  have hEF : ((N : ℕ) : Cardinal) ≤ Algebra.trdeg E F := by
    simpa using hT0ind.cardinalMk_le_trdeg
  let t' : Fin D × Fin N → E := fun q => ⟨T (q.1.succ, q.2), hmemT q.1 q.2⟩
  have ht' : AlgebraicIndependent K t' := by
    have hinj : Function.Injective (fun q : Fin D × Fin N => ((q.1.succ, q.2) : Fin (D + 1) × Fin N)) := by
      intro u v huv
      have h' : ((u.1.succ, u.2) : Fin (D + 1) × Fin N) = (v.1.succ, v.2) := huv
      obtain ⟨h1', h2'⟩ := Prod.mk.inj h'
      exact Prod.ext_iff.2 ⟨Fin.succ_injective _ h1', h2'⟩
    exact AlgebraicIndependent.of_comp E.val (hTind.comp _ hinj)
  have hlow : (((D * N : ℕ)) : Cardinal) ≤ Algebra.trdeg K E := by
    simpa using ht'.cardinalMk_le_trdeg
  have hfin : Algebra.trdeg K E < ℵ₀ :=
    lt_of_le_of_lt (le_self_add.trans ((add_le_add le_rfl hEF).trans (hadd.trans htF)))
      Cardinal.natCast_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 hfin
  have hle : n + N ≤ (D + 1) * N := by
    have := (add_le_add le_rfl hEF).trans (hadd.trans htF)
    rw [hn] at this
    exact_mod_cast this
  have hge : D * N ≤ n := by
    rw [hn] at hlow
    exact_mod_cast hlow
  have htr : Algebra.trdeg K E = ((D * N : ℕ) : Cardinal) := by
    rw [hn]
    congr 1
    have e : (D + 1) * N = D * N + N := by ring
    rw [e] at hle
    exact le_antisymm (Nat.le_of_add_le_add_right hle) hge

  let u : Fin (D + 1) × Fin N → V := fun q => ⟨T q, hTV q⟩
  let p : Fin (D + 1) × Fin N → MvPolynomial (Fin N) E := fun q =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin N) E) (MvPolynomial.X q.2)
      (fun i => MvPolynomial.C (⟨T (i.succ, q.2), hmemT i q.2⟩ : E)) q.1
  have hp : ∀ q α, (p q).coeff α ∈ V.comap (algebraMap E F) := by
    rintro ⟨i, k⟩ α
    induction i using Fin.cases with
    | zero =>
      show (MvPolynomial.X k : MvPolynomial (Fin N) E).coeff α ∈ V.comap (algebraMap E F)
      rw [MvPolynomial.coeff_X']
      split_ifs
      · exact (V.comap (algebraMap E F)).one_mem
      · exact (V.comap (algebraMap E F)).zero_mem
    | succ i =>
      show (MvPolynomial.C (⟨T (i.succ, k), hmemT i k⟩ : E)).coeff α ∈ V.comap (algebraMap E F)
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact hTV _
      · exact (V.comap (algebraMap E F)).zero_mem
  have hpu : ∀ q, MvPolynomial.aeval (fun s => T (0, s)) (p q) = (u q : F) := by
    rintro ⟨i, k⟩
    induction i using Fin.cases with
    | zero =>
      show MvPolynomial.aeval (fun s => T (0, s)) (MvPolynomial.X k : MvPolynomial (Fin N) E) = T (0, k)
      rw [MvPolynomial.aeval_X]
    | succ i =>
      show MvPolynomial.aeval (fun s => T (0, s)) (MvPolynomial.C (⟨T (i.succ, k), hmemT i k⟩ : E)) = T (i.succ, k)
      rw [MvPolynomial.aeval_C]
      rfl
  have hcard : Fintype.card (Fin (D + 1) × Fin N) = Fintype.card (Fin N) + D * N := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  have hind := gauss_indep (Ω := E) V T hTV hG
  have RT := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K E F (D * N) htr (Fin N) (fun s => T (0, s)) V
    (fun s => hTV _) (Fin (D + 1) × Fin N) u p hp hcard hpu hind
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap E F)
  have RT3 := RT.2.2

  have haW : ∀ k, (⟨a k, hmema k⟩ : E) ∈ V.comap (algebraMap E F) := fun k =>
    (V.valuation_le_one_iff _).1 (haV k)
  let abar : Fin N → ResidueField (V.comap (algebraMap E F)) := fun k => residue (V.comap (algebraMap E F)) ⟨⟨a k, hmema k⟩, haW k⟩
  let aV : Fin N → V := fun k => ⟨a k, (V.valuation_le_one_iff _).1 (haV k)⟩
  let tV : Fin N → V := fun k => ⟨T (0, k), hTV _⟩
  let Lp : MvPolynomial (Fin N) (ResidueField (V.comap (algebraMap E F))) :=
    ∑ k, MvPolynomial.C (abar k) * MvPolynomial.X k
  have hLp : Lp ≠ 0 := by
    intro h0
    have := congrArg (fun P => MvPolynomial.coeff (Finsupp.single j0 1) P) h0
    simp only [Lp, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
      MvPolynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j0] at this
    · rw [if_pos rfl, mul_one] at this
      have h1' : abar j0 = 1 := by
        show residue (V.comap (algebraMap E F)) ⟨⟨a j0, hmema j0⟩, haW j0⟩ = 1
        have : (⟨⟨a j0, hmema j0⟩, haW j0⟩ : ↥(V.comap (algebraMap E F))) = 1 := Subtype.ext (Subtype.ext ha0)
        rw [this, map_one]
      rw [h1'] at this
      exact one_ne_zero this
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hs
      exact hb ((Finsupp.single_left_inj one_ne_zero).mp hs)
    · simp
  have hev : MvPolynomial.aeval (fun s => residue V ⟨T (0, s), hTV _⟩) Lp = residue V (∑ k, aV k * tV k) := by
    simp only [Lp, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
  have hres : residue V (∑ k, aV k * tV k) ≠ 0 := by
    rw [← hev]
    intro h0
    exact hLp (RT3.eq_zero_of_aeval_eq_zero _ h0)
  have hunit : IsUnit (∑ k, aV k * tV k) := by
    by_contra hnu
    apply hres
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hL1 : V.valuation (∑ k, a k * T (0, k)) = 1 := by
    have := (V.valuation_eq_one_iff _).1 hunit
    simpa [aV, tV] using this

  have hprod : y j0 * ∑ k, a k * T (0, k) = 1 := by
    rw [Finset.mul_sum, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hay k]
    ring
  have hyv : V.valuation (y j0) = 1 := by
    have := congrArg V.valuation hprod
    rw [Valuation.map_mul, hL1, mul_one, Valuation.map_one] at this
    exact this
  intro k
  rw [← V.valuation_le_one_iff]
  exact (hj0 k (Finset.mem_univ _)).trans hyv.le

end Formalism.L2.Pj.GenericSectionMinimum
