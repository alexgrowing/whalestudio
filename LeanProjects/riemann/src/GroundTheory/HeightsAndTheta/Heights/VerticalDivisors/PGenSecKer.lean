import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenSecKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial Cardinal

noncomputable section

namespace GenSecKer

theorem genPar_algIndep (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

theorem coeff_mem_of_sum {k L : Type*} [Field k] [Field L] [Algebra k L] (K : IntermediateField k L)
    {n : ℕ} (x c : Fin n → L) (b : L) (j₀ : Fin n) (hx : ∀ j, x j ∈ K) (hx0 : x j₀ ≠ 0)
    (hsum : ∑ j, c j * x j = b) (hb : b ∈ K) (hc : ∀ j, j ≠ j₀ → c j ∈ K) : c j₀ ∈ K := by
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => c j * x j) (Finset.mem_univ j₀)
  have hval : c j₀ = (b - ∑ j ∈ Finset.univ.erase j₀, c j * x j) / x j₀ := by
    rw [eq_div_iff hx0, ← hsum, ← hsplit]
    ring
  rw [hval]
  exact div_mem (sub_mem hb (sum_mem fun j hj => mul_mem (hc j (Finset.ne_of_mem_erase hj)) (hx j)))
    (hx j₀)

theorem ker_eq {k L : Type} [Field k] [CommRing L] (hL : IsField L) [Algebra k L] {n e : ℕ}
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]
    (hdim : ringKrullDim (MvPolynomial (Fin n) k ⧸ Q) = ((e + 1 : ℕ) : WithBot ℕ∞)) (x : Fin n → L)
    (hgen : ∀ z : L, ∃ p : MvPolynomial (Fin n) (GenParField k e n), aeval x p = z)
    (hR1 : ∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0)
    (hR2 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1)
    (hQ : ∀ q ∈ Q, aeval x q = 0) :
    RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) = Q := by
  classical
  letI : Field L := hL.toField
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [h j, mul_zero]
    exact one_ne_zero (hR2.symm.trans h0)
  let y : Par e n → L := fun p => algebraMap (GenParField k e n) L (genPar k e n p)
  let col : Par e n → Fin n := fun p => Sum.elim Prod.snd id p
  let t : Set L := Set.range x ∪ y '' {p | col p = j₀}ᶜ
  have hxK : ∀ j, x j ∈ IntermediateField.adjoin k t :=
    fun j => IntermediateField.subset_adjoin k t (Or.inl ⟨j, rfl⟩)
  have hyK' : ∀ p, col p ≠ j₀ → y p ∈ IntermediateField.adjoin k t :=
    fun p hp => IntermediateField.subset_adjoin k t (Or.inr ⟨p, hp, rfl⟩)
  have hyK : ∀ p, y p ∈ IntermediateField.adjoin k t := by
    rintro (⟨i, j⟩ | j)
    · by_cases hj : j = j₀
      · rw [hj]
        exact coeff_mem_of_sum _ x (fun j => y (.inl (i, j))) 0 j₀ hxK hj₀ (hR1 i) (zero_mem _)
          (fun j' hj' => hyK' _ hj')
      · exact hyK' _ hj
    · by_cases hj : j = j₀
      · rw [hj]
        exact coeff_mem_of_sum _ x (fun j => y (.inr j)) 1 j₀ hxK hj₀ hR2 (one_mem _)
          (fun j' hj' => hyK' _ hj')
      · exact hyK' _ hj
  have hpoly : ∀ a : MvPolynomial (Par e n) k,
      algebraMap (GenParField k e n) L (algebraMap _ (GenParField k e n) a) ∈
        IntermediateField.adjoin k t := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k) (GenParField k e n),
        ← IsScalarTower.algebraMap_apply k (GenParField k e n) L]
      exact IntermediateField.algebraMap_mem _ c
    | add a b ha hb =>
      rw [map_add, map_add]
      exact add_mem ha hb
    | mul_X a p ha =>
      rw [map_mul, map_mul]
      exact mul_mem ha (hyK p)
  have hF : ∀ f, algebraMap (GenParField k e n) L f ∈ IntermediateField.adjoin k t := by
    intro f
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Par e n) k) f
    rw [map_div₀]
    exact div_mem (hpoly a) (hpoly b)
  have hall : ∀ p : MvPolynomial (Fin n) (GenParField k e n),
      aeval x p ∈ IntermediateField.adjoin k t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [aeval_C]
      exact hF c
    | add a b ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, aeval_X]
      exact mul_mem ha (hxK j)
  have htop : IntermediateField.adjoin k t = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨p, rfl⟩ := hgen z
    exact hall p
  have : Algebra.IsAlgebraic (Algebra.adjoin k t) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  have : FaithfulSMul k L :=
    (faithfulSMul_iff_algebraMap_injective k L).2 (algebraMap k L).injective
  obtain ⟨u, hut, hu⟩ := exists_isTranscendenceBasis_subset (R := k) t
  have hyind : AlgebraicIndependent k y :=
    (genPar_algIndep k e n).map' (f := IsScalarTower.toAlgHom k (GenParField k e n) L)
      (algebraMap (GenParField k e n) L).injective
  have hPar : #(Par e n) ≤ Algebra.trdeg k L := hyind.cardinalMk_le_trdeg
  have hucard : #u = Algebra.trdeg k L := hu.cardinalMk_eq_trdeg
  have hQP : Q ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) :=
    fun q hq => (RingHom.mem_ker).2 (hQ q hq)
  have : (RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L)).IsPrime := RingHom.ker_isPrime _
  refine le_antisymm ?_ hQP
  by_contra hle
  have hlt : Q < RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) := lt_of_le_not_ge hQP hle
  have hdrop := NumbersDVR.DimStrictDrop.proof _ Q _ hlt
  rw [hdim] at hdrop
  have : Algebra.FiniteType k
      (MvPolynomial (Fin n) k ⧸ RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L)) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _)
      (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨m, hm, htr⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg k
    (A := MvPolynomial (Fin n) k ⧸ RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L))
  rw [hm] at hdrop
  have hme : m ≤ e := by
    have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by
      push_cast
      exact hdrop
    have := (Nat.cast_le (α := WithBot ℕ∞)).1 h'
    omega

  have hu1 : AlgebraicIndependent k ((↑) : (u ∩ Set.range x : Set L) → L) :=
    hu.1.mono Set.inter_subset_left
  let v : (u ∩ Set.range x : Set L) → MvPolynomial (Fin n) k ⧸
      RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) :=
    fun z => Ideal.Quotient.mk _ (X z.2.2.choose)
  have hcomp : ⇑(Ideal.kerLiftAlg (aeval x : MvPolynomial (Fin n) k →ₐ[k] L)) ∘ v =
      ((↑) : (u ∩ Set.range x : Set L) → L) := by
    funext z
    simp only [Function.comp_apply, v, Ideal.kerLiftAlg_mk, aeval_X]
    exact z.2.2.choose_spec
  have hv : AlgebraicIndependent k v :=
    AlgebraicIndependent.of_comp (Ideal.kerLiftAlg _) (by rw [hcomp]; exact hu1)
  have hcard1 : #(u ∩ Set.range x : Set L) ≤ m := htr ▸ hv.cardinalMk_le_trdeg
  have hsub : u ⊆ (u ∩ Set.range x) ∪ y '' {p | col p = j₀}ᶜ := fun z hz =>
    (hut hz).elim (fun h => Or.inl ⟨hz, h⟩) Or.inr
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.1 (Cardinal.lt_aleph0_of_finite {p : Par e n | col p = j₀})
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.1
    (Cardinal.lt_aleph0_of_finite ({p : Par e n | col p = j₀}ᶜ : Set (Par e n)))
  have hE0 : #(Fin e ⊕ Unit) ≤ #{p : Par e n | col p = j₀} := by
    refine Cardinal.mk_le_of_injective (f := fun s => match s with
      | .inl i => ⟨.inl (i, j₀), rfl⟩
      | .inr _ => ⟨.inr j₀, rfl⟩) ?_
    rintro (i | u) (i' | u') h
    · have h' := congrArg Subtype.val h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h'
      exact congrArg Sum.inl h'.1
    · exact (Sum.inl_ne_inr (congrArg Subtype.val h)).elim
    · exact (Sum.inr_ne_inl (congrArg Subtype.val h)).elim
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  have hea : e + 1 ≤ a := by
    rw [ha, Cardinal.mk_fintype, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hE0
    exact_mod_cast hE0
  have hchain : ((a + b : ℕ) : Cardinal) ≤ ((m + b : ℕ) : Cardinal) := by
    push_cast
    calc (a : Cardinal) + b = #(Par e n) := by rw [← ha, ← hb]; exact Cardinal.mk_sum_compl _
      _ ≤ Algebra.trdeg k L := hPar
      _ = #u := hucard.symm
      _ ≤ #((u ∩ Set.range x) ∪ y '' {p | col p = j₀}ᶜ : Set L) := Cardinal.mk_le_mk_of_subset hsub
      _ ≤ #(u ∩ Set.range x : Set L) + #(y '' {p | col p = j₀}ᶜ : Set L) := Cardinal.mk_union_le _ _
      _ ≤ m + b := add_le_add hcard1 (Cardinal.mk_image_le.trans hb.le)
  have : a + b ≤ m + b := by exact_mod_cast hchain
  omega

end GenSecKer

theorem GenSecKer.proof (h₁ : SecAlgField.Statement) (h₂ : ConeDimOfChowForm.Statement) :
    GenSecKer.Statement := by
  intro k _ n e Q g hQ hg
  have : Q.IsPrime := hQ.isPrime
  set I := secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))))
      (genPar k e n) with hI
  have hfield : IsField (MvPolynomial (Fin n) (GenParField k e n) ⧸ I) := h₁ k n e Q g hQ hg
  have hsec : ∀ i, secForm (genPar k e n) i ∈ I := fun i => by
    rw [hI]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  have hchart : chartForm (genPar k e n) - 1 ∈ I := by
    rw [hI]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hQI : Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))) ≤ I := by
    rw [hI]
    exact le_sup_left.trans le_sup_left
  let x : Fin n → MvPolynomial (Fin n) (GenParField k e n) ⧸ I := fun j => Ideal.Quotient.mk I (X j)
  have hmk : (aeval x : MvPolynomial (Fin n) (GenParField k e n) →ₐ[GenParField k e n] _) =
      Ideal.Quotient.mkₐ (GenParField k e n) I :=
    MvPolynomial.algHom_ext fun j => by rw [aeval_X]; rfl
  have hlin : ∀ c : Fin n → GenParField k e n, Ideal.Quotient.mk I (linForm c) =
      ∑ j, algebraMap (GenParField k e n) (MvPolynomial (Fin n) (GenParField k e n) ⧸ I) (c j) * x j := by
    intro c
    show Ideal.Quotient.mkₐ (GenParField k e n) I (linForm c) = _
    rw [← hmk]
    simp [linForm, aeval_X]
  have hR1 : ∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) (MvPolynomial (Fin n) (GenParField k e n) ⧸ I)
      (genPar k e n (.inl (i, j))) * x j = 0 := by
    intro i
    rw [← hlin, Ideal.Quotient.eq_zero_iff_mem]
    exact hsec i
  have hR2 : ∑ j, algebraMap (GenParField k e n) (MvPolynomial (Fin n) (GenParField k e n) ⧸ I)
      (genPar k e n (.inr j)) * x j = 1 := by
    rw [← hlin, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hchart
  have hker : (Ideal.Quotient.mk I).comp (MvPolynomial.map (algebraMap k (GenParField k e n))) =
      ((aeval x : MvPolynomial (Fin n) k →ₐ[k] _) : MvPolynomial (Fin n) k →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.coe_comp, Function.comp_apply, map_C, RingHom.coe_coe, aeval_C]
      rw [IsScalarTower.algebraMap_apply k (GenParField k e n)
        (MvPolynomial (Fin n) (GenParField k e n) ⧸ I)]
      rfl
    · intro j
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, RingHom.coe_coe, aeval_X]
      rfl
  have hQ0 : ∀ q ∈ Q, (aeval x : MvPolynomial (Fin n) k →ₐ[k] _) q = 0 := by
    intro q hq
    have h1 := RingHom.congr_fun hker q
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h1
    rw [← h1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hQI (Ideal.mem_map_of_mem _ hq))
  have hgen : ∀ z : MvPolynomial (Fin n) (GenParField k e n) ⧸ I,
      ∃ p : MvPolynomial (Fin n) (GenParField k e n), aeval x p = z := fun z => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨p, by rw [hmk]; rfl⟩
  rw [hker]
  exact GenSecKer.ker_eq hfield Q (h₂ k n (e + 1) Q g hQ hg) x hgen hR1 hR2 hQ0

end

end GroundTheory.Heights₂.Heights.Vertical
