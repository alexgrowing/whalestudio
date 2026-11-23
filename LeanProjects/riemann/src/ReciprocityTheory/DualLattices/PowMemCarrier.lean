import ReciprocityTheory.DualLattices.ColengthCotangentBoundStatementOfClaim
import ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
import ReciprocityTheory.DualLattices.MemDualLat
import ReciprocityTheory.DualLattices.ImportsBis
import ReciprocityTheory.DualLattices.SqIdeal

noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section SlopeTestRemainingChoices

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

lemma sq_eq_mul {X : Type} (I : Submodule R (X → C)) : sqIdeal I = I * I := by
  rw [sqIdeal, Submodule.mul_eq_span_mul_set]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_mul]
  constructor
  · rintro ⟨f, hf, f', hf', rfl⟩
    exact ⟨f, hf, f', hf', rfl⟩
  · rintro ⟨f, hf, f', hf', rfl⟩
    exact ⟨f, hf, f', hf', rfl⟩

lemma mem_aug {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) (f : X → C) :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  simp [augIdeal, Submodule.mem_inf, LinearMap.mem_ker]

variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

lemma pow_mem_carrier (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) :
    ∀ k : ℕ, f ^ k ∈ AA.carrier := by
  intro k
  induction k with
  | zero => simpa using AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hf

variable (K : AddSubgroup N) [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]

lemma pullQ_aug (AA : HopfOrder (C := C) R N) (AQ : HopfOrder (C := C) R (N ⧸ K))
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) {b : N ⧸ K → C}
    (hb : b ∈ augIdeal AQ.carrier) : pullQ (R := R) K b ∈ augIdeal AA.carrier := by
  rw [mem_aug] at hb ⊢
  refine ⟨?_, ?_⟩
  · have h1 : b ∈ AA.carrier.comap (pullQ (R := R) K) := hAQ ▸ hb.1
    exact h1
  · simpa [pullQ, LinearMap.funLeft_apply] using hb.2

lemma pullQ_sq (AA : HopfOrder (C := C) R N) (AQ : HopfOrder (C := C) R (N ⧸ K))
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) {z : N ⧸ K → C}
    (hz : z ∈ sqIdeal (augIdeal AQ.carrier)) :
    pullQ (R := R) K z ∈ sqIdeal (augIdeal AA.carrier) := by
  have key : sqIdeal (augIdeal AQ.carrier) ≤
      (sqIdeal (augIdeal AA.carrier)).comap (pullQ (R := R) K) := by
    rw [sqIdeal, Submodule.span_le]
    rintro h ⟨f, hf, f', hf', rfl⟩
    apply Submodule.subset_span
    exact ⟨_, pullQ_aug K AA AQ hAQ hf, _, pullQ_aug K AA AQ hAQ hf', rfl⟩
  exact key hz

lemma IK_mul_le (AA : HopfOrder (C := C) R N) (AQ : HopfOrder (C := C) R (N ⧸ K))
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) :
    (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
  rw [Submodule.mul_le]
  intro m hm a ha
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hm
  rw [mem_aug] at hb
  obtain ⟨r, hr⟩ := AA.le_int ha 0
  have hpb : pullQ (R := R) K b ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    exact ⟨hb.1, by simpa [pullQ, LinearMap.funLeft_apply] using hb.2⟩
  have ha' : a - r • (1 : N → C) ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem), ?_⟩
    simp [Algebra.smul_def, hr]
  have hsplit : pullQ (R := R) K b * a =
      pullQ (R := R) K b * (a - r • (1 : N → C)) + r • pullQ (R := R) K b := by
    rw [mul_sub, mul_smul_comm, mul_one]
    abel
  rw [hsplit]
  refine Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul hpb ha')) ?_
  refine Submodule.mem_sup_left ?_
  exact Submodule.smul_mem _ r (Submodule.mem_map_of_mem (by rw [mem_aug]; exact hb))

end SlopeTestRemainingChoices

def zmodEquiv (p : ℕ) [Fact p.Prime] {N : Type} [AddCommGroup N] (x : N) (hx : p • x = 0)
    (hx0 : x ≠ 0) : ZMod p ≃+ AddSubgroup.zmultiples x := by
  let f0 : ℤ →+ AddSubgroup.zmultiples x := zmultiplesHom _ ⟨x, AddSubgroup.mem_zmultiples x⟩
  have hf0 : f0 p = 0 := by
    apply Subtype.ext
    simp [f0, hx]
  let f : ZMod p →+ AddSubgroup.zmultiples x := ZMod.lift p ⟨f0, hf0⟩
  have hord : addOrderOf x = p := addOrderOf_eq_prime hx hx0
  refine AddEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).2 fun k hk => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := ZMod.intCast_surjective k
    have h1 : f0 m = 0 := by rw [← ZMod.lift_coe p ⟨f0, hf0⟩ m]; exact hk
    have h2 : m • x = 0 := by
      have := congrArg Subtype.val h1
      simpa [f0] using this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.2 h2
  · rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
    refine ⟨(m : ZMod p), ?_⟩
    rw [ZMod.lift_coe]
    rfl

lemma hasColen_of_lat {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : ∃ c, HasColen R v M c := by
  obtain ⟨B, -, hB⟩ := h
  exact ⟨_, B, hB, rfl⟩

def ClaimBody (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) : Prop :=
  ∃ (n : ℕ) (g : Fin n → N → C) (δ : Fin n → R),
    (∀ i, g i ∈ augIdeal AA.carrier) ∧
    (∀ f ∈ augIdeal AA.carrier, ∃ r : Fin n → R,
      f - ∑ j, r j • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
    (∀ i, ∃ a : Fin n → R,
      δ i • g i - ∑ j, (if j < i then a j else 0) • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
    ∀ c, HasColen R v AA.carrier c →
      c ^ 2 = (∏ i, v (algebraMap R C (δ i))) ^ Fintype.card N

lemma claim_base {C : Type} [Field C] (v : Valuation C NNReal) {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N]
    (htriv : ∀ x : N, x = 0) (AA : HopfOrder (C := C) R N) : ClaimBody C v R N AA := by
  haveI : Unique N := ⟨⟨0⟩, htriv⟩
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, fun i => i.elim0, ?_⟩
  · intro f hf
    refine ⟨Fin.elim0, ?_⟩
    have hf0 : f = 0 := by
      funext x
      rw [htriv x]
      exact ((mem_aug _ f).1 hf).2
    simp [hf0]
  · rintro c ⟨B, hB, rfl⟩
    have hrange : (Set.range fun j x => B x j) = {fun x => B x 0} := by
      rw [Set.range_unique]
      congr 1
      funext x
      rw [htriv (default : N)]
    rw [hrange] at hB
    have h1 : (1 : N → C) ∈ Submodule.span R {fun x => B x 0} := by
      rw [← hB]; exact AA.one_mem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h1
    have hcolmem : (fun x => B x 0) ∈ AA.carrier := by
      rw [hB]; exact Submodule.subset_span rfl
    obtain ⟨s, hs⟩ := AA.le_int hcolmem 0
    have hs' : B 0 0 = algebraMap R C s := hs.symm
    have hdet : B.det = algebraMap R C s := by rw [Matrix.det_unique, htriv (default : N)]; exact hs'
    have hprod : algebraMap R C r * algebraMap R C s = 1 := by
      have h2 := congrFun hr 0
      simp only [Pi.smul_apply, Algebra.smul_def, Pi.one_apply] at h2
      rw [← hs']; exact h2
    have hvs := hv.map_le_one s
    have hv1 : v (algebraMap R C r) * v (algebraMap R C s) = 1 := by
      rw [← map_mul, hprod, map_one]
    have hs1 : v (algebraMap R C s) = 1 := by
      apply le_antisymm hvs
      calc (1 : NNReal) = v (algebraMap R C r) * v (algebraMap R C s) := hv1.symm
        _ ≤ 1 * v (algebraMap R C s) := by gcongr; exact hv.map_le_one r
        _ = _ := one_mul _
    rw [hdet, hs1]
    simp

theorem claim_all (p : ℕ) [hp : Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hvp : v (p : C) < 1) :
    ∀ (k : ℕ) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], Fintype.card N = k →
      (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ClaimBody C v R N AA := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro N _ _ _ hk hN AA
  by_cases htriv : ∀ x : N, x = 0
  · exact claim_base v hv N htriv AA
  push_neg at htriv
  obtain ⟨x, hx0⟩ := htriv
  set K : AddSubgroup N := AddSubgroup.zmultiples x with hKdef
  let e : ZMod p ≃+ K := zmodEquiv p x (hN x) hx0
  letI : DecidablePred (· ∈ K) := Classical.decPred _
  letI : DecidableEq (N ⧸ K) := Classical.decEq _
  letI : Fintype (N ⧸ K) :=
    Fintype.ofSurjective (QuotientAddGroup.mk : N → N ⧸ K) QuotientAddGroup.mk_surjective
  obtain ⟨⟨AK, hAK⟩, ⟨AQ, hAQ⟩, -, -⟩ := h2 C R v hv N K AA
  have hcardK : Fintype.card K = p := by
    rw [← Fintype.card_congr e.toEquiv, ZMod.card]
  have hcardN : Fintype.card N = Fintype.card (N ⧸ K) * p := by
    have h0 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
    simp only [Nat.card_eq_fintype_card] at h0
    rw [h0, hcardK]
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hlt : Fintype.card (N ⧸ K) < k := by
    rw [← hk, hcardN]
    have hpos : 0 < Fintype.card (N ⧸ K) := Fintype.card_pos
    nlinarith
  have hNQ : ∀ q : N ⧸ K, p • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H a => rw [← QuotientAddGroup.mk_nsmul, hN a, QuotientAddGroup.mk_zero]
  obtain ⟨n, g, δ, hg1, hg2, hg3, hg4⟩ := ih _ hlt (N ⧸ K) rfl hNQ AQ
  obtain ⟨xK, δK, x1, hxK, hxKp, hδK, hxKgen, hcK⟩ := primeHopfOrder_of_addEquiv u3 p C v R hv hvp e AK
  have hxKA : xK ∈ AA.carrier.map (resK (R := R) K) := by
    rw [← hAK]; exact ((mem_aug _ _).1 hxK).1
  obtain ⟨y0, hy0, hy0x⟩ := Submodule.mem_map.1 hxKA
  have hyx : ∀ a : K, y0 (a : N) = xK a := fun a => by rw [← hy0x]; rfl
  have hyaug : y0 ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨hy0, ?_⟩
    have h0 := hyx 0
    rw [((mem_aug _ _).1 hxK).2] at h0
    simpa using h0

  have hIK : ∀ z ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K),
      ∃ r : Fin n → R, z - ∑ j, r j • pullQ (R := R) K (g j) ∈ sqIdeal (augIdeal AA.carrier) := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hz
    rw [← hAQ] at hb
    obtain ⟨r, hr⟩ := hg2 b hb
    refine ⟨r, ?_⟩
    have h1 := pullQ_sq K AA AQ hAQ hr
    simpa [map_sub, map_sum, map_smul] using h1
  have hsup : ∀ z ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier,
      ∃ r : Fin n → R, z - ∑ j, r j • pullQ (R := R) K (g j) ∈ sqIdeal (augIdeal AA.carrier) := by
    intro z hz
    obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨r, hr⟩ := hIK z1 hz1
    refine ⟨r, ?_⟩
    have hz2' : z2 ∈ sqIdeal (augIdeal AA.carrier) := by rw [sq_eq_mul]; exact hz2
    have h1 := Submodule.add_mem _ hr hz2'
    convert h1 using 1
    abel
  refine ⟨n + 1, Fin.snoc (fun i => pullQ (R := R) K (g i)) y0, Fin.snoc δ δK, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hyaug
    | cast i0 =>
      simp only [Fin.snoc_castSucc]
      exact pullQ_aug K AA AQ hAQ (hg1 i0)
  · intro f hf
    have hrf : resK (R := R) K f ∈ augIdeal AK.carrier := by
      rw [mem_aug, hAK]
      refine ⟨Submodule.mem_map_of_mem ((mem_aug _ _).1 hf).1, ?_⟩
      have h0 := ((mem_aug _ _).1 hf).2
      simpa [resK, LinearMap.funLeft_apply] using h0
    obtain ⟨r0, hr0⟩ := hxKgen _ hrf
    have hgm : f - r0 • y0 ∈ augIdeal AA.carrier :=
      Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hyaug)
    have hres : resK (R := R) K (f - r0 • y0) ∈ augIdeal (AA.carrier.map (resK (R := R) K)) *
        augIdeal (AA.carrier.map (resK (R := R) K)) := by
      rw [← hAK, map_sub, map_smul, hy0x]; exact hr0
    obtain ⟨r, hr⟩ := hsup _ (mem_sup_of_restrictToSubgroup_mem_sq hv AA K _ hgm hres)
    refine ⟨Fin.snoc r r0, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    convert hr using 1
    abel
  · intro i
    induction i using Fin.lastCases with
    | last =>
      have hmemA : y0 ^ p - δK • y0 ∈ AA.carrier :=
        AA.carrier.sub_mem (pow_mem_carrier AA hy0 p) (AA.carrier.smul_mem δK hy0)
      have hres0 : resK (R := R) K (y0 ^ p - δK • y0) = 0 := by
        funext a
        have h2 := congrFun hxKp a
        simp only [Pi.pow_apply] at h2
        simp [resK, LinearMap.funLeft_apply, hyx, h2, Algebra.smul_def]
      have hIKA := mem_of_restrictToSubgroup_eq_zero hv AA K _ hmemA hres0
      obtain ⟨a, ha⟩ := hsup _ (IK_mul_le K AA AQ hAQ hIKA)
      have hpow : y0 ^ p ∈ sqIdeal (augIdeal AA.carrier) := by
        have hp0 : p = (p - 1) + 1 := by omega
        rw [hp0, pow_succ]
        apply Submodule.subset_span
        refine ⟨y0 ^ (p - 1), ?_, y0, hyaug, rfl⟩
        rw [mem_aug]
        refine ⟨pow_mem_carrier AA hy0 _, ?_⟩
        have h0 := ((mem_aug _ _).1 hyaug).2
        simp [h0, show p - 1 ≠ 0 by omega]
      refine ⟨Fin.snoc (fun j => -a j) 0, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_lt_last, if_true,
        lt_self_iff_false, if_false, zero_smul, add_zero]
      have h1 := Submodule.sub_mem _ hpow ha
      convert h1 using 1
      simp only [neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add]
      abel
    | cast i0 =>
      obtain ⟨a, ha⟩ := hg3 i0
      refine ⟨Fin.snoc a 0, ?_⟩
      have hnl : ¬ (Fin.last n < Fin.castSucc i0) := not_lt.2 (Fin.castSucc_lt_last i0).le
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_castSucc_iff, hnl, if_false,
        zero_smul, add_zero]
      have h1 := pullQ_sq K AA AQ hAQ ha
      simpa [map_sub, map_sum, map_smul, apply_ite (pullQ (R := R) K), map_zero] using h1
  · intro c hc
    obtain ⟨cB, hcB⟩ := hasColen_of_lat v AQ.lat
    have hB2 := hg4 cB hcB
    have hcB' : HasColen R v (AA.carrier.comap (pullQ (R := R) K)) cB := by
      rw [← hAQ]; exact hcB
    have hcK' : HasColen R v (AA.carrier.map (resK (R := R) K)) (v x1 ^ (p * (p - 1) / 2)) := by
      rw [← hAK]; exact hcK
    have hc_eq := hasColength_eq_pow_mul_pow hv AA K c cB _ hc hcB' hcK'
    have hK2 : (v x1 ^ (p * (p - 1) / 2)) ^ 2 = v (algebraMap R C δK) ^ p := by
      rw [hδK, ← pow_mul, ← pow_mul]
      congr 1
      have h2 : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
      rw [Nat.div_mul_cancel h2, mul_comm]
    rw [hc_eq, hcardK, Fin.prod_univ_castSucc, hcardN]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    calc (cB ^ p * (v x1 ^ (p * (p - 1) / 2)) ^ Fintype.card (N ⧸ K)) ^ 2
        = (cB ^ 2) ^ p * ((v x1 ^ (p * (p - 1) / 2)) ^ 2) ^ Fintype.card (N ⧸ K) := by ring
      _ = ((∏ i, v (algebraMap R C (δ i))) ^ Fintype.card (N ⧸ K)) ^ p *
          (v (algebraMap R C δK) ^ p) ^ Fintype.card (N ⧸ K) := by rw [hB2, hK2]
      _ = _ := by ring

theorem u4 : ColengthCotangentBoundStatement := by
  apply colengthCotangentBoundStatement_of_claim
  intro p _ C _ _ _ v R _ _ hv hvp N _ _ _ hN AA
  exact claim_all p C v R hv hvp (Fintype.card N) N rfl hN AA

end ReciprocityTheory.PGsh.Up
