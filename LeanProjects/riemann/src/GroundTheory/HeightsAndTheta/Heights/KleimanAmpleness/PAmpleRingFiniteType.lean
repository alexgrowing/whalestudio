import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AmpleRingFiniteTypeSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace AmpleRingFiniteType

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem aeval_div_pow {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : Ω) :
    aeval (fun i => x i / c) f = aeval x f / c ^ e := by
  conv_lhs => rw [← f.support_sum_monomial_coeff]
  conv_rhs => rw [← f.support_sum_monomial_coeff]
  simp only [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hdeg := hf (mem_support_iff.mp hμ)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] at hdeg
  simp only [aeval_monomial, Finsupp.prod, div_pow, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg, mul_div_assoc]

def chartGens (J : Chart x) : Finset Ω := by
  classical exact (Finset.univ ×ˢ J.1).image fun p => x p.1 / x p.2

theorem mem_chartGens {J : Chart x} (i : Fin (N + 1)) {l : Fin (N + 1)} (hl : l ∈ J.1) :
    x i / x l ∈ chartGens J := by
  classical
  unfold chartGens
  convert Finset.mem_image.mpr ⟨(i, l), Finset.mem_product.mpr ⟨Finset.mem_univ _, hl⟩, rfl⟩

theorem chartGens_mem (J : Chart x) : ∀ y ∈ chartGens J, y ∈ chartRing S x J := by
  classical
  intro y hy
  unfold chartGens at hy
  obtain ⟨⟨i, l⟩, hp, rfl⟩ := Finset.mem_image.mp (by convert hy)
  exact ⟨X i, X l, 1, X_mem_monos (Finset.mem_product.mp hp).2, isHomogeneous_X S i,
    isHomogeneous_X S l, by simp⟩

theorem chartRing_le (J : Chart x) :
    chartRing S x J ≤ Algebra.adjoin S (chartGens J : Set Ω) := by
  rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
  obtain ⟨l, hl⟩ := J.2.1
  have hxl : x l ≠ 0 := (mem_support x).mp (J.2.2 hl)
  have hmon : ∀ s ∈ monos (S := S) J.1, ∃ e, s.IsHomogeneous e ∧
      x l ^ e / aeval x s ∈ Algebra.adjoin S (chartGens J : Set Ω) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      refine ⟨1, isHomogeneous_X S i, ?_⟩
      rw [pow_one, aeval_X]
      exact Algebra.subset_adjoin (Finset.mem_coe.mpr (mem_chartGens l hi))
    | one => exact ⟨0, isHomogeneous_one _ _, by rw [pow_zero, map_one, div_one]; exact one_mem _⟩
    | mul s s' _ _ h h' =>
      obtain ⟨e, he, hW⟩ := h
      obtain ⟨e', he', hW'⟩ := h'
      refine ⟨e + e', he.mul he', ?_⟩
      rw [pow_add, map_mul, mul_div_mul_comm]
      exact mul_mem hW hW'
  obtain ⟨e', he', hW⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos J hs
  have hee : e' = e := he'.inj_right hse (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  have hf' : aeval x f / x l ^ e' ∈ Algebra.adjoin S (chartGens J : Set Ω) := by
    rw [← aeval_div_pow hf (x l)]
    have h1 : aeval (fun i => x i / x l) f ∈ Algebra.adjoin S (Set.range fun i => x i / x l) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨f, rfl⟩
    exact Algebra.adjoin_le (Set.range_subset_iff.mpr fun i =>
      Algebra.subset_adjoin (Finset.mem_coe.mpr (mem_chartGens i hl))) h1
  have e1 : aeval x f / aeval x s = (aeval x f / x l ^ e') * (x l ^ e' / aeval x s) := by
    rw [div_mul_div_cancel₀ (pow_ne_zero _ hxl)]
  rw [e1]
  exact mul_mem hf' hW

theorem ampleChart_le (H : LineBundle S x) (D : AmpleData S x H) (j : Fin (D.r + 1))
    (h0 : D.h j ≠ 0) (J : Chart x) {a : Ω} (ha : a ∈ ampleChart H.toSubSystem D.m (D.h j) J) :
    a ∈ Algebra.adjoin S (Set.range (fun l => D.h l / D.h j) ∪ (chartGens J : Set Ω)) := by
  set L := Algebra.adjoin S (Set.range (fun l => D.h l / D.h j) ∪ (chartGens J : Set Ω))
  have hA : ∀ c ∈ chartRing S x J, c ∈ L := fun c hc =>
    Algebra.adjoin_mono Set.subset_union_right (chartRing_le J hc)
  have hP : ∀ q ∈ (H.pow D.m).sub J, q / D.h j ∈ L := by
    intro q hq
    rw [← D.generates J] at hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨l, rfl⟩ := hq
      exact Algebra.subset_adjoin (Or.inl ⟨l, rfl⟩)
    | zero => rw [zero_div]; exact zero_mem _
    | add q q' _ _ h1 h2 => rw [add_div]; exact add_mem h1 h2
    | smul c q _ h1 =>
      rw [chartRing_smul_def, mul_div_assoc]
      exact mul_mem (hA _ c.2) h1
  have hPn : ∀ n, ∀ y ∈ ((H.pow D.m).sub J) ^ n, y / D.h j ^ n ∈ L := by
    intro n
    induction n with
    | zero =>
      intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hy
      rw [pow_zero, div_one]
      exact hA _ c.2
    | succ n ih =>
      intro y hy
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy (fun p hp q hq => ?_) (fun y y' h1 h2 => ?_)
      · rw [pow_succ, mul_div_mul_comm]
        exact mul_mem (ih p hp) (hP q hq)
      · rw [add_div]; exact add_mem h1 h2
  obtain ⟨n, hn⟩ := ha
  have hn' : a * D.h j ^ n ∈ ((H.pow D.m).sub J) ^ n := by
    rw [SubSystem.pow_sub, ← pow_mul, ← SubSystem.pow_sub]
    exact hn
  have := hPn n _ hn'
  rwa [mul_div_cancel_right₀ _ (pow_ne_zero _ h0)] at this

theorem exists_pow_mul_mem_ampleRing (H : LineBundle S x) {m : ℕ} {h : Ω}
    (hh : ∀ I, h ∈ (H.pow m).sub I) {c : Ω} (hc : c ∈ ampleRing H.toSubSystem m h) (J : Chart x)
    (hrat : ∀ I : Chart x, ∃ e : ℕ,
      c ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem m h I)
    {y : Ω} (hy : y ∈ chartRing S x J) : ∃ M : ℕ, c ^ M * y ∈ ampleRing H.toSubSystem m h := by
  classical
  have hI : ∀ I : Chart x, ∃ M, c ^ M * y ∈ ampleChart H.toSubSystem m h I := by
    intro I
    have h1 : y ∈ ampleChart H.toSubSystem m h (AmpleAffineGen.unionChart I J) :=
      AmpleAffineGen.ampleChart_mono (AmpleAffineGen.subset_unionChart_right I J)
        (AmpleAffineGen.mem_ampleSubalg_of_mem_chartRing (hh J) hy)
    obtain ⟨D, hD⟩ := AmpleAffineGen.ampleChart_loc H I J h1
    obtain ⟨e, he⟩ := hrat I
    refine ⟨e * D, ?_⟩
    have := mul_mem
      (pow_mem (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from he) D)
      (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hD)
    rwa [show c ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) =
        c ^ e * AmpleAffineGen.chartRatio J I from rfl,
      AmpleAffineGen.pow_mul_cancel (AmpleAffineGen.chartRatio_mul_chartRatio I J)] at this
  choose M hM using hI
  refine ⟨Finset.univ.sup M, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : M I ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ I)
  have e1 : c ^ Finset.univ.sup M * y = c ^ (Finset.univ.sup M - M I) * (c ^ M I * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e1]
  exact mul_mem
    (pow_mem (show c ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from
      Set.mem_iInter.mp hc I) _)
    (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hM I)

end AmpleRingFiniteType

open AmpleRingFiniteType in

theorem AmpleRingFiniteType.proof : AmpleRingFiniteType.Statement := by
  intro S _ N Ω _ _ x H D j h0
  classical
  have hh : ∀ I : Chart x, D.h j ∈ (H.pow D.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (D.mem_secs j) I
  obtain ⟨n, a, c, J, ha, hc, hsum, hrat⟩ := D.affine j h0
  have hgen : ∀ k, ∀ y ∈ chartGens (J k),
      ∃ M : ℕ, c k ^ M * y ∈ ampleRing H.toSubSystem D.m (D.h j) := fun k y hy =>
    exists_pow_mul_mem_ampleRing H hh (hc k) (J k) (hrat k) (chartGens_mem (J k) y hy)
  choose! M hM using hgen
  set T : Finset Ω := Finset.univ.image a ∪ Finset.univ.image c ∪
    Finset.univ.biUnion (fun k => (chartGens (J k)).image fun y => c k ^ M k y * y) with hTdef
  have haT : ∀ k, a k ∈ T := fun k =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  have hcT : ∀ k, c k ∈ T := fun k =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  have hyT : ∀ k, ∀ y ∈ chartGens (J k), c k ^ M k y * y ∈ T := fun k y hy =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hy⟩)
  have hTR : ∀ t ∈ T, t ∈ ampleRing H.toSubSystem D.m (D.h j) := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht
        exact ha k
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht
        exact hc k
    · obtain ⟨k, -, ht⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
      exact hM k y hy
  refine ⟨T.card, fun t => (T.equivFin.symm t : Ω), fun t => hTR _ (T.equivFin.symm t).2, ?_⟩
  set K := Algebra.adjoin S (Set.range (fun l => D.h l / D.h j) ∪ (T : Set Ω)) with hKdef
  have hrange : Set.range (fun t => (T.equivFin.symm t : Ω)) = (T : Set Ω) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (T.equivFin.symm t).2
    · intro hz
      exact ⟨T.equivFin ⟨z, hz⟩, by simp⟩
  have hK : K ≤ (Algebra.adjoin (ampleBase (S := S) D.h j)
      (Set.range fun t => (T.equivFin.symm t : Ω))).restrictScalars S := by
    rw [hrange, Algebra.adjoin_le_iff]
    rintro z (⟨l, rfl⟩ | hz)
    · exact (Subalgebra.mem_restrictScalars _).mpr (Subalgebra.algebraMap_mem _
        (⟨_, Algebra.subset_adjoin ⟨l, rfl⟩⟩ : ampleBase (S := S) D.h j))
    · exact (Subalgebra.mem_restrictScalars _).mpr (Algebra.subset_adjoin hz)
  have hTK : ∀ t ∈ T, t ∈ K := fun t ht => Algebra.subset_adjoin (Or.inr (Finset.mem_coe.mpr ht))
  intro f hf
  apply hK

  have hk : ∀ k, ∃ E : ℕ, c k ^ E * f ∈ K := by
    intro k
    have hcK : c k ∈ K := hTK _ (hcT k)
    have hfJ := ampleChart_le H D j h0 (J k) (Set.mem_iInter.mp hf (J k))
    clear hf
    induction hfJ using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨l, rfl⟩ | hz
      · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin (Or.inl ⟨l, rfl⟩)⟩
      · exact ⟨M k z, hTK _ (hyT k z (Finset.mem_coe.mp hz))⟩
    | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem K r⟩
    | add z z' _ _ h1 h2 =>
      obtain ⟨E, hE⟩ := h1
      obtain ⟨E', hE'⟩ := h2
      refine ⟨E + E', ?_⟩
      have e1 : c k ^ (E + E') * (z + z') = c k ^ E' * (c k ^ E * z) + c k ^ E * (c k ^ E' * z') := by
        ring
      rw [e1]
      exact add_mem (mul_mem (pow_mem hcK _) hE) (mul_mem (pow_mem hcK _) hE')
    | mul z z' _ _ h1 h2 =>
      obtain ⟨E, hE⟩ := h1
      obtain ⟨E', hE'⟩ := h2
      refine ⟨E + E', ?_⟩
      have e1 : c k ^ (E + E') * (z * z') = (c k ^ E * z) * (c k ^ E' * z') := by ring
      rw [e1]
      exact mul_mem hE hE'
  choose E hE using hk
  set E₀ := Finset.univ.sup E with hE₀
  have hbig : ∀ k, c k ^ E₀ * f ∈ K := by
    intro k
    have hle : E k ≤ E₀ := Finset.le_sup (Finset.mem_univ k)
    have e1 : c k ^ E₀ * f = c k ^ (E₀ - E k) * (c k ^ E k * f) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [e1]
    exact mul_mem (pow_mem (hTK _ (hcT k)) _) (hE k)

  let cK : Fin n → K := fun k => ⟨c k, hTK _ (hcT k)⟩
  let aK : Fin n → K := fun k => ⟨a k, hTK _ (haT k)⟩
  have hspan : Ideal.span (Set.range cK) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : K) = ∑ k, aK k * cK k := Subtype.ext (by simp [aK, cK, hsum])
    rw [e1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  let Iid : Ideal K :=
    { carrier := {y | (y : Ω) * f ∈ K}
      add_mem' := fun {y y'} hy hy' => by
        simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul] at *
        exact add_mem hy hy'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]
        exact zero_mem K
      smul_mem' := fun b y hy => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul, mul_assoc] at *
        exact mul_mem b.2 hy }
  have hle : Ideal.span ((fun y : K => y ^ E₀) '' Set.range cK) ≤ Iid := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    show ((cK k ^ E₀ : K) : Ω) * f ∈ K
    simpa [cK] using hbig k
  rw [Ideal.span_pow_eq_top _ hspan E₀, top_le_iff] at hle
  have h1 : (1 : K) ∈ Iid := hle ▸ Submodule.mem_top
  simpa [Iid] using h1

end

end GroundTheory.Heights₂.Heights.Kleiman
