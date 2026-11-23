import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCommensurableOfIsLatIn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenRBaseChangeSubquotient
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

noncomputable section

open Formalism.MainNotions.IntegralHeckeForms Formalism.MainNotions.BlochKatoReduction.Gen
open scoped TensorProduct

namespace GlobalTheory.TwistDet

theorem nonempty_monomialOrder (σ : Type) [Finite σ] : Nonempty (MonomialOrder.{0, 0} σ) := by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  exact ⟨MonomialOrder.degLex⟩

open MvPolynomial MonomialOrder in

theorem mem_span_of_aeval_eq_zero {O O' : Type} [CommRing O] [CommRing O'] [IsDomain O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) {n R : ℕ} (hn : 0 < n) {ζ : O'} (hζ : IsPrimitiveRoot ζ n)
    (h : MvPolynomial (Fin R ⊕ Fin R) O)
    (hh : ∀ u : Fin R ⊕ Fin R → O'ˣ, (∀ q, u q ^ n = 1) → (∀ a, u (.inr a) = 1) →
      aeval (fun q => (u q : O') - 1) h = 0) :
    h ∈ Ideal.span (Set.range (fun i : Fin R => (X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + X (Sum.inl i)) ^ n - 1)) := by
  classical
  have : IsDomain O := hinj.isDomain
  obtain ⟨m⟩ := nonempty_monomialOrder (Fin R ⊕ Fin R)
  let b : Fin R ⊕ Fin R → MvPolynomial (Fin R ⊕ Fin R) O :=
    Sum.elim (fun i => (1 + X (Sum.inl i)) ^ n - 1) (fun i => X (Sum.inr i))
  let e : Fin R ⊕ Fin R → ℕ := Sum.elim (fun _ => n) (fun _ => 1)
  have hb : ∀ q, m.Monic (b q) ∧ m.degree (b q) = Finsupp.single q (e q) := by
    rintro (i | i)
    · have e1 : (1 + X (Sum.inl i) : MvPolynomial (Fin R ⊕ Fin R) O) = X (Sum.inl i) - C (-1) := by
        simp [add_comm]
      have d1 : m.degree ((1 + X (Sum.inl i) : MvPolynomial (Fin R ⊕ Fin R) O) ^ n) = Finsupp.single (.inl i) n := by
        rw [m.degree_pow, e1, m.degree_X_sub_C]; simp
      have m1 : m.Monic ((1 + X (Sum.inl i) : MvPolynomial (Fin R ⊕ Fin R) O) ^ n) := by
        rw [e1]; exact (m.monic_X_sub_C _ _).pow
      have hlt : m.degree (C (-1) : MvPolynomial (Fin R ⊕ Fin R) O) ≺[m]
          m.degree ((1 + X (Sum.inl i) : MvPolynomial (Fin R ⊕ Fin R) O) ^ n) := by
        rw [d1, m.degree_C, map_zero]
        refine lt_of_le_of_ne bot_le fun h0 => hn.ne' ?_
        have := (map_eq_zero_iff _ m.toSyn.injective).1 h0.symm
        simpa using this
      have e2 : b (.inl i) = (1 + X (Sum.inl i)) ^ n + C (-1) := by simp [b, sub_eq_add_neg]
      rw [e2]
      exact ⟨m1.add_of_lt hlt, (m.degree_add_of_lt hlt).trans d1⟩
    · exact ⟨m.leadingCoeff_X, m.degree_X⟩
  obtain ⟨g, r, hf, -, hr⟩ := m.div (b := b) (fun q => by rw [(hb q).1.leadingCoeff_eq_one]; exact isUnit_one) h
  have hbI : ∀ q, b q ∈ Ideal.span (Set.range (fun i : Fin R => (X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + X (Sum.inl i)) ^ n - 1)) := by
    rintro (i | i)
    · exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)
    · exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)
  suffices r = 0 by
    rw [hf, this, add_zero, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (hbI q)
  apply map_injective _ hinj
  rw [map_zero]
  let S : Fin R ⊕ Fin R → Finset O' :=
    Sum.elim (fun _ => (Polynomial.nthRootsFinset n (1 : O')).image (· - 1)) (fun _ => {0})
  have hS : ∀ q, (S q).card = e q := by
    rintro (i | i)
    · exact (Finset.card_image_of_injective _ sub_left_injective).trans hζ.card_nthRootsFinset
    · rfl
  have he : ∀ q, 0 < e q := by rintro (i | i); exacts [hn, one_pos]
  apply eq_zero_of_eval_zero_at_prod_finset _ S
  · intro q
    rw [hS, degreeOf_lt_iff (he q)]
    intro c hc
    have := hr c (support_map_subset _ _ hc) q
    rw [(hb q).2, Finsupp.single_le_iff] at this
    omega
  · intro x hx
    have hx1 : ∀ q, (x q + 1) ^ n = 1 := by
      rintro (i | i)
      · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 (hx (.inl i))
        rw [← hxy, sub_add_cancel]
        exact (Polynomial.mem_nthRootsFinset hn _).1 hy
      · rw [Finset.mem_singleton.1 (hx (.inr i))]; simp
    let u : Fin R ⊕ Fin R → O'ˣ := fun q => Units.ofPowEqOne _ n (hx1 q) hn.ne'
    have hu : (fun q => (u q : O') - 1) = x := by ext q; simp [u]
    have h0 := hh u (fun q => Units.ext (by simpa [u] using hx1 q))
      (fun a => Units.ext (by simpa [u] using Finset.mem_singleton.1 (hx (.inr a))))
    rw [hu, hf, map_add, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finset.sum_eq_zero, zero_add] at h0
    · rw [eval_map, ← aeval_def, h0]
    · rintro (i | i) _
      · have := hx1 (.inl i)
        simp [b, add_comm (1 : O'), this]
      · simp [b, Finset.mem_singleton.1 (hx (.inr i))]

open Polynomial in

theorem det_eq_mul_X_pow {k ι : Type} [Field k] (n r e : ℕ) (t : ℕ → Matrix (Fin n) (Fin n) k) (q : ι)
    (he : (e : k) ≠ 0) :
    ∃ (w : MvPolynomial ι k) (ν : ℕ), w.coeff 0 ≠ 0 ∧ ν ≤ r * n ∧
      (1 + ∑ m ∈ Finset.Icc 1 r, ((1 + MvPolynomial.X q : MvPolynomial ι k) ^ e) ^ m •
        (t m).map MvPolynomial.C).det = w * MvPolynomial.X q ^ ν := by
  let A : Matrix (Fin n) (Fin n) k[X] := 1 + ∑ m ∈ Finset.Icc 1 r, (X : k[X]) ^ m • (t m).map C
  have hA : ∀ (S : Type) [CommRing S] [Algebra k S] (y : S), aeval y A.det =
      (1 + ∑ m ∈ Finset.Icc 1 r, y ^ m • (t m).map (algebraMap k S)).det := by
    intro S _ _ y
    rw [AlgHom.map_det]
    congr 1
    ext a c
    simp [A, Matrix.one_apply, Matrix.sum_apply, apply_ite]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h0 : A.det ≠ 0 := by
    intro h
    have := hA k 0
    rw [h, map_zero, Finset.sum_eq_zero (fun m hm => by
      rw [zero_pow (by have := (Finset.mem_Icc.1 hm).1; omega), zero_smul])] at this
    simp at this
  have hd : A.det.natDegree ≤ r * n := by
    have hent : ∀ a c, (A a c).natDegree ≤ r := by
      intro a c
      simp only [A, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · rw [Matrix.one_apply]; split_ifs <;> simp
      · refine natDegree_sum_le_of_forall_le _ _ fun m hm => (natDegree_mul_C_le _ _).trans ?_
        rw [natDegree_X_pow]; exact (Finset.mem_Icc.1 hm).2
    rw [Matrix.det_apply']
    refine natDegree_sum_le_of_forall_le _ _ fun σ _ => natDegree_mul_le.trans ?_
    rw [natDegree_intCast, zero_add]
    refine (natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun a _ => hent _ _).trans ?_)
    simp [mul_comm]
  obtain ⟨p, hp, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd A.det h0 1
  set ν := rootMultiplicity 1 A.det
  have hν : ν ≤ r * n := by
    refine le_trans ?_ hd
    have := natDegree_le_of_dvd (pow_rootMultiplicity_dvd A.det 1) h0
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at this
  let s : MvPolynomial ι k := ∑ i ∈ Finset.range e, (1 + MvPolynomial.X q) ^ i
  have hs : (1 + MvPolynomial.X q : MvPolynomial ι k) ^ e - 1 = s * MvPolynomial.X q := by
    rw [← geom_sum_mul]; simp [s]
  refine ⟨s ^ ν * aeval ((1 + MvPolynomial.X q : MvPolynomial ι k) ^ e) p, ν, ?_, hν, ?_⟩
  · rw [← MvPolynomial.constantCoeff_eq, map_mul, map_pow]
    refine mul_ne_zero (pow_ne_zero _ (by simpa [s] using he)) ?_
    have : MvPolynomial.constantCoeff (aeval ((1 + MvPolynomial.X q : MvPolynomial ι k) ^ e) p) = p.eval 1 := by
      have := aeval_algHom_apply (MvPolynomial.aeval (R := k) (fun _ : ι => (0 : k)))
        ((1 + MvPolynomial.X q : MvPolynomial ι k) ^ e) p
      simpa using this.symm
    rw [this]
    exact fun h => hnd (dvd_iff_isRoot.2 h)
  · have := hA _ ((1 + MvPolynomial.X q : MvPolynomial ι k) ^ e)
    rw [MvPolynomial.algebraMap_eq] at this
    rw [← this, hp, map_mul, map_pow, map_sub, aeval_X, aeval_C, map_one, hs]
    ring

open Module in

private theorem index_span_matrix_eq_val_det (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (W : Type) [AddCommGroup W] [Module O W] (l n : ℕ)
    (bs : Fin n → W) (m : Matrix (Fin n) (Fin n) O) (hbs : LinearIndependent O bs)
    (_hm : m.det ≠ 0) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (Submodule.span O (Set.range bs))
      (Submodule.span O (Set.range fun a => ∑ c, m c a • bs c)) =
        Formalism.MainNotions.BlochKatoReduction.Gen.nval O l m.det := by
  classical
  set M := Submodule.span O (Set.range bs) with hM
  set N := Submodule.span O (Set.range fun a => ∑ c, m c a • bs c) with hN
  let b : Basis (Fin n) O M := Basis.span hbs
  have hb : ∀ i, (b i : W) = bs i := fun i => Basis.coe_span_apply hbs i
  let th : Fin n → M := fun a => ∑ c, m c a • b c
  have hth : ∀ a, (th a : W) = ∑ c, m c a • bs c := by
    intro a
    simp [th, hb]
  have hmap : (Submodule.span O (Set.range th)).map M.subtype = N := by
    rw [Submodule.map_span, ← Set.range_comp, hN]
    congr 2
    funext a
    exact hth a
  have hcomap : N.comap M.subtype = Submodule.span O (Set.range th) := by
    rw [← hmap, Submodule.comap_map_eq_of_injective M.injective_subtype]
  have hle : N ≤ M := by
    rw [← hmap]
    exact Submodule.map_subtype_le _ _
  have htop : M.comap N.subtype = ⊤ := Submodule.comap_subtype_eq_top.2 hle
  have hdet : b.det th = m.det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, th, Finsupp.single_apply]
  have h1 : Module.length O (M ⧸ N.comap M.subtype) = IsDiscreteValuationRing.addVal O m.det := by
    rw [hcomap, length_quotient_span_eq_addVal_det b, hdet]
  have h2 : Module.length O (N ⧸ M.comap N.subtype) = 0 := by
    rw [Module.length_eq_zero_iff, htop]
    infer_instance
  unfold Formalism.MainNotions.IntegralHeckeForms.sIdx Formalism.MainNotions.IntegralHeckeForms.lenR Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [h1, h2]
  simp

theorem sIdx_span_of_smul_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {W : Type}
    [AddCommGroup W] [Module O W] (l : ℕ) {n : ℕ} {bs w : Fin n → W} {x : O} {m : Matrix (Fin n) (Fin n) O}
    {V : Submodule O W} (hx : x ≠ 0) (hbs : LinearIndependent O bs)
    (hV : IsLatIn (Submodule.span O (Set.range bs)) V) (hw : ∀ a, w a ∈ V)
    (hm : ∀ a, x • w a = ∑ c, m c a • bs c) (hd : m.det ≠ 0) :
    IsLatIn (Submodule.span O (Set.range w)) V ∧
      sIdx l (Submodule.span O (Set.range bs)) (Submodule.span O (Set.range w)) = nval O l m.det - nval O l (x ^ n) := by
  have hwi : LinearIndependent O w := by
    rw [Fintype.linearIndependent_iff] at hbs ⊢
    intro v hv
    have h1 : ∑ c, (m.mulVec v) c • bs c = 0 := by
      calc ∑ c, (m.mulVec v) c • bs c = ∑ a, v a • ∑ c, m c a • bs c := by
            simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
            rw [Finset.sum_comm]
            simp only [mul_comm]
        _ = x • ∑ a, v a • w a := by
            simp only [← hm, Finset.smul_sum, smul_comm x]
        _ = 0 := by rw [hv, smul_zero]
    have h2 : m.mulVec v = 0 := funext (hbs _ h1)
    by_contra hne
    exact hd (Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, fun h => hne (fun a => congrFun h a), h2⟩)
  have hle : Submodule.span O (Set.range fun a => x • w a) ≤ Submodule.span O (Set.range w) :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  have hwV : Submodule.span O (Set.range w) ≤ V := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hw a)
  have hdet : ∀ y ∈ Submodule.span O (Set.range bs), m.det • y ∈ Submodule.span O (Set.range fun a => x • w a) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      have : m.det • bs c = ∑ a, m.adjugate a c • x • w a := by
        simp only [hm, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have h3 : ∀ c', ∑ a, (m.adjugate a c * m c' a) • bs c' = (m * m.adjugate) c' c • bs c' := by
          intro c'
          rw [← Finset.sum_smul, Matrix.mul_apply]
          simp only [mul_comm]
        simp only [h3, Matrix.mul_adjugate]
        simp [Matrix.one_apply]
      rw [this]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
  have hL2 : IsLatIn (Submodule.span O (Set.range fun a => x • w a)) V := by
    refine ⟨Submodule.fg_span (Set.finite_range _), hle.trans hwV, fun y hy => ?_⟩
    obtain ⟨c, hc, hcy⟩ := hV.2.2 y hy
    exact ⟨m.det * c, mul_ne_zero hd hc, by rw [mul_smul]; exact hdet _ hcy⟩
  have hL1 : IsLatIn (Submodule.span O (Set.range w)) V := by
    refine ⟨Submodule.fg_span (Set.finite_range _), hwV, fun y hy => ?_⟩
    obtain ⟨c, hc, hcy⟩ := hL2.2.2 y hy
    exact ⟨c, hc, hle hcy⟩
  refine ⟨hL1, ?_⟩
  have e1 := index_span_matrix_eq_val_det O W l n bs m hbs hd
  have hxd : (x • (1 : Matrix (Fin n) (Fin n) O)).det = x ^ n := by simp
  have e2 := index_span_matrix_eq_val_det O W l n w (x • 1) hwi (by rw [hxd]; exact pow_ne_zero _ hx)
  have e3 : (fun a => ∑ c, (x • (1 : Matrix (Fin n) (Fin n) O)) c a • w c) = fun a => x • w a := by
    ext a; simp [Matrix.one_apply]
  rw [e3, hxd] at e2
  simp only [← hm] at e1
  have e4 := (GlobalTheory.sIdx_add_and_mono O W l V _ _ _ hV hL1 hL2).1
  linarith

theorem baseChange_span_range {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {W ι : Type}
    [AddCommGroup W] [Module O W] (v : ι → W) :
    (Submodule.span O (Set.range v)).baseChange O' = Submodule.span O' (Set.range fun a => (1 : O') ⊗ₜ[O] v a) := by
  rw [Submodule.baseChange_span, ← Set.range_comp]
  rfl

theorem linearIndependent_one_tmul {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [Algebra O O'] (hinj : Function.Injective (algebraMap O O')) {W ι : Type} [AddCommGroup W]
    [Module O W] {v : ι → W} (hv : LinearIndependent O v) : LinearIndependent O' fun a => (1 : O') ⊗ₜ[O] v a := by
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  exact Module.Flat.linearIndependent_one_tmul hv

theorem sIdx_le_of_coords {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    (hinj : Function.Injective (algebraMap O O')) {W : Type} [AddCommGroup W] [Module O W] (l : ℕ) {n : ℕ}
    {bs th : Fin n → W} {x : O} {m₀ : Matrix (Fin n) (Fin n) O} {m : Matrix (Fin n) (Fin n) O'}
    {w : Fin n → O' ⊗[O] W} {V : Submodule O W} {T : Submodule O' (O' ⊗[O] W)} (hx : x ≠ 0)
    (hbs : LinearIndependent O bs) (hV : IsLatIn (Submodule.span O (Set.range bs)) V) (hth : ∀ a, th a ∈ V)
    (hm₀ : ∀ a, x • th a = ∑ c, m₀ c a • bs c) (hd₀ : m₀.det ≠ 0)
    (hm : ∀ a, algebraMap O O' x • w a = ∑ c, m c a • (1 : O') ⊗ₜ[O] bs c) (hd : m.det ≠ 0)
    (hT : IsLatIn T (V.baseChange O')) (hw : ∀ a, w a ∈ T) :
    sIdx l ((Submodule.span O (Set.range bs)).baseChange O') T ≤
      sIdx l (Submodule.span O (Set.range bs)) (Submodule.span O (Set.range th)) +
        (nval O' l m.det - nval O l m₀.det) := by
  have hx' : algebraMap O O' x ≠ 0 := (map_ne_zero_iff _ hinj).2 hx
  have hbs' := linearIndependent_one_tmul hinj hbs
  have hV' := (GlobalTheory.sIdx_baseChange O O' hinj W l V _ _ hV hV).1
  have hV'' := hV'
  rw [baseChange_span_range] at hV''
  obtain ⟨-, e1⟩ := sIdx_span_of_smul_eq l hx hbs hV hth hm₀ hd₀
  obtain ⟨hL, e2⟩ := sIdx_span_of_smul_eq l hx' hbs' hV'' (fun a => hT.2.1 (hw a)) hm hd
  have e3 := (GlobalTheory.sIdx_add_and_mono O' _ l _ _ _ _ hV'' hT hL).2
    (Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hw a))
  have hxd : (x • (1 : Matrix (Fin n) (Fin n) O)).det = x ^ n := by simp
  have hbV : ∀ a, bs a ∈ V := fun a => hV.2.1 (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨hL2, e4⟩ := sIdx_span_of_smul_eq l (w := fun a => x • bs a) (m := x • 1) one_ne_zero hbs hV
    (fun a => V.smul_mem _ (hbV a)) (fun a => by simp [Matrix.one_apply]) (by rw [hxd]; exact pow_ne_zero _ hx)
  have hxd' : (algebraMap O O' x • (1 : Matrix (Fin n) (Fin n) O')).det = algebraMap O O' x ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have e5 := (GlobalTheory.sIdx_baseChange O O' hinj W l V _ _ hV hL2).2
  rw [baseChange_span_range, baseChange_span_range] at e5
  obtain ⟨-, e6⟩ := sIdx_span_of_smul_eq l (w := fun a => (1 : O') ⊗ₜ[O] (x • bs a)) (m := algebraMap O O' x • 1)
    one_ne_zero hbs' hV'' (fun a => Submodule.tmul_mem_baseChange_of_mem _ (V.smul_mem _ (hbV a)))
    (fun a => by
      rw [one_smul, TensorProduct.tmul_smul, ← algebraMap_smul O' x, Finset.sum_eq_single a]
      · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      · intro c _ hc
        simp only [Matrix.smul_apply, Matrix.one_apply_ne hc, smul_zero, zero_smul]
      · simp)
    (by rw [hxd']; exact pow_ne_zero _ hx')
  have n1 : nval O l (1 ^ n) = 0 := by simp [nval]
  have n2 : nval O' l (1 ^ n) = 0 := by simp [nval]
  rw [hxd, n1] at e4
  rw [hxd', n2] at e6
  rw [baseChange_span_range]
  linarith

open IsLocalRing in

theorem isUnit_det_of_eigen {O : Type} [CommRing O] [IsLocalRing O] [IsAlgClosed (ResidueField O)] {W : Type}
    [AddCommGroup W] [Module O W] {n : ℕ} {bs : Fin n → W} (hbs : LinearIndependent O bs) {κ : Type}
    (good : ℕ → κ → Prop) (T : ℕ → κ → Module.End O W) (t : ℕ → κ → Matrix (Fin n) (Fin n) O)
    (hT : ∀ k p k' p', good k p → good k' p' → T k p * T k' p' = T k' p' * T k p)
    (ht : ∀ k p, good k p → ∀ a, T k p (bs a) = ∑ c, t k p c a • bs c) (s : Finset ℕ) (p₀ : κ) (c : ℕ → O)
    (hs : ∀ k ∈ s, good k p₀)
    (h : ∀ x ∈ Submodule.span O (Set.range bs), x ∉ maximalIdeal O • Submodule.span O (Set.range bs) →
      ∀ ev : ℕ → κ → O, (∀ k p, good k p → T k p x - ev k p • x ∈ maximalIdeal O • Submodule.span O (Set.range bs)) →
      IsUnit (1 + ∑ k ∈ s, c k * ev k p₀)) :
    IsUnit (1 + ∑ k ∈ s, c k • t k p₀).det := by
  classical
  let φ : (Fin n → O) →ₗ[O] W := Fintype.linearCombination O bs
  have hφ : Function.Injective φ := hbs.fintypeLinearCombination_injective
  have hφr : LinearMap.range φ = Submodule.span O (Set.range bs) := Fintype.range_linearCombination O bs
  have hφT : ∀ k p, good k p → ∀ v, T k p (φ v) = φ ((t k p).mulVec v) := by
    intro k p hg v
    simp only [φ, Fintype.linearCombination_apply, map_sum, map_smul, ht k p hg, Matrix.mulVec, dotProduct,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hmem : ∀ v, φ v ∈ maximalIdeal O • Submodule.span O (Set.range bs) ↔ ∀ a, v a ∈ maximalIdeal O := by
    intro v
    rw [← hφr, ← Submodule.map_top, ← Submodule.map_smul'']
    constructor
    · rintro ⟨v', hv', e⟩
      obtain rfl := hφ e
      refine Submodule.smul_induction_on hv' (fun r hr y _ a => Ideal.mul_mem_right _ _ hr)
        fun y z hy hz a => Ideal.add_mem _ (hy a) (hz a)
    · intro hv
      refine ⟨v, ?_, rfl⟩
      rw [pi_eq_sum_univ v]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem_smul (hv a) trivial
  have hcomm : ∀ k p k' p', good k p → good k' p' → t k p * t k' p' = t k' p' * t k p := by
    intro k p k' p' hg hg'
    refine Matrix.ext_of_mulVec_single fun a => hφ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hφT _ _ hg, ← hφT _ _ hg', ← hφT _ _ hg', ← hφT _ _ hg]
    exact LinearMap.congr_fun (hT k p k' p' hg hg') _
  by_contra hne
  let ρ := residue O
  let Pm : Matrix (Fin n) (Fin n) (ResidueField O) := 1 + ∑ k ∈ s, ρ (c k) • (t k p₀).map ρ
  have hPm : Pm.det = 0 := by
    have : ρ (1 + ∑ k ∈ s, c k • t k p₀).det = Pm.det := by
      rw [RingHom.map_det]
      congr 1
      ext a b
      simp [Pm, Matrix.one_apply, Matrix.sum_apply, apply_ite]
    rw [← this]
    exact (residue_eq_zero_iff _).2 hne
  let T' : {kp : ℕ × κ // good kp.1 kp.2} → (Fin n → ResidueField O) →ₗ[ResidueField O] (Fin n → ResidueField O) :=
    fun kp => Matrix.toLin' ((t kp.1.1 kp.1.2).map ρ)
  have hc' : ∀ k p k' p', good k p → good k' p' →
      (t k p).map ρ * (t k' p').map ρ = (t k' p').map ρ * (t k p).map ρ := by
    intro k p k' p' hg hg'
    rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm k p k' p' hg hg']
  obtain ⟨v, hv, hv0, hev⟩ := GlobalTheory.exists_common_eigenvector_mem T'
    (fun i j v => by simp only [T', Matrix.toLin'_apply, Matrix.mulVec_mulVec, hc' _ _ _ _ i.2 j.2])
    (LinearMap.ker (Matrix.toLin' Pm))
    (by
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hPm
      exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
    (by
      intro i v hv
      have : Pm * (t i.1.1 i.1.2).map ρ = (t i.1.1 i.1.2).map ρ * Pm := by
        simp only [Pm, add_mul, mul_add, one_mul, mul_one, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
          mul_smul_comm]
        congr 1
        exact Finset.sum_congr rfl fun k hk => by rw [hc' _ _ _ _ (hs k hk) i.2]
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
      simp only [T', Matrix.toLin'_apply]
      rw [Matrix.mulVec_mulVec, this, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero])
  choose lam hlam using hev
  choose lift hlift using residue_surjective (R := O)
  let x : Fin n → O := fun a => lift (v a)
  have hx : ρ ∘ x = v := funext fun a => hlift _
  let ev : ℕ → κ → O := fun k p => if hg : good k p then lift (lam ⟨(k, p), hg⟩) else 0
  have hev : ∀ k p, good k p → ((t k p).map ρ).mulVec v = ρ (ev k p) • v := by
    intro k p hg
    have := hlam ⟨(k, p), hg⟩
    simp only [ev, dif_pos hg, ρ, hlift]
    exact this
  have hu := h (φ x) (hφr ▸ LinearMap.mem_range_self φ x)
    (by
      rw [hmem]
      intro h0
      exact hv0 (hx ▸ funext fun a => (residue_eq_zero_iff _).2 (h0 a))) ev
    (by
      intro k p hg
      rw [hφT k p hg, ← map_smul, ← map_sub, hmem]
      intro a
      rw [← residue_eq_zero_iff]
      have := congrFun (hev k p hg) a
      rw [← hx, ← RingHom.map_mulVec] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sub_eq_zero]
      exact this)
  have h2 : Pm.mulVec v = ρ (1 + ∑ k ∈ s, c k * ev k p₀) • v := by
    simp only [Pm, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, map_add, map_one,
      map_sum, map_mul, add_smul, one_smul, Finset.sum_smul, mul_smul]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [hev k p₀ (hs k hk)]
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, h2, smul_eq_zero] at hv
  exact hv.elim (hu.map ρ).ne_zero hv0

theorem exists_basis_fin {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {W : Type} [AddCommGroup W]
    [Module O W] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] {n : ℕ} {th : Fin n → W}
    {B : Submodule O W} (hB : B.FG) (hth : LinearIndependent O th)
    (hsp : Submodule.span (FractionRing O) (Set.range th) = Submodule.span (FractionRing O) (B : Set W)) :
    ∃ bs : Fin n → W, LinearIndependent O bs ∧ Submodule.span O (Set.range bs) = B := by
  have : Module.Finite O B := Module.Finite.iff_fg.2 hB
  have : Module.IsTorsionFree O W := Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) W
  let b := Module.finBasis O B
  have h1 : LinearIndependent O (fun a => (b a : W)) := b.linearIndependent.map' B.subtype B.ker_subtype
  have h2 : Submodule.span O (Set.range fun a => (b a : W)) = B := by
    have := congrArg (Submodule.map B.subtype) b.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at this
  have h3 : Module.finrank O B = n := by
    have e1 := finrank_span_eq_card ((LinearIndependent.iff_fractionRing O (FractionRing O)).1 h1)
    have e2 := finrank_span_eq_card ((LinearIndependent.iff_fractionRing O (FractionRing O)).1 hth)
    have e3 : Submodule.span (FractionRing O) (Set.range fun a => (b a : W)) =
        Submodule.span (FractionRing O) (B : Set W) := by
      conv_rhs => rw [← h2]
      rw [Submodule.span_span_of_tower]
    rw [hsp, ← e3, e1] at e2
    simpa using e2
  subst h3
  exact ⟨_, h1, h2⟩

open Classical in

def IsChi {V ι A : Type} [Fintype ι] [CommGroup A] {n : ℕ} (P : ι → V) (Q : Finset V) (u : ι → A)
    (χ : Multiplicative (↥Q → ZMod n) →* A) : Prop :=
  ∀ x : ↥Q → ZMod n, χ (Multiplicative.ofAdd x) = ∏ q, if h : P q ∈ Q then u q ^ (x ⟨P q, h⟩).val else 1

theorem exists_isChi {V ι A : Type} [Fintype ι] [CommGroup A] {n : ℕ} [NeZero n] (P : ι → V) (Q : Finset V)
    (u : ι → A) (hu : ∀ q, u q ^ n = 1) : ∃ χ : Multiplicative (↥Q → ZMod n) →* A, IsChi P Q u χ := by
  classical
  refine ⟨MonoidHom.mk' (fun x => ∏ q, if h : P q ∈ Q then u q ^ (Multiplicative.toAdd x ⟨P q, h⟩).val else 1)
    fun x y => ?_, fun x => by simp [MonoidHom.mk'_apply]⟩
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  split_ifs with h
  · rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add]
  · rw [one_mul]

theorem IsChi.unique {V ι A : Type} [Fintype ι] [CommGroup A] {n : ℕ} {P : ι → V} {Q : Finset V} {u : ι → A}
    {χ χ' : Multiplicative (↥Q → ZMod n) →* A} (h : IsChi P Q u χ) (h' : IsChi P Q u χ') : χ = χ' :=
  MonoidHom.ext fun x => (h x.toAdd).trans (h' x.toAdd).symm

open MvPolynomial in

theorem exists_coords {O W V ι : Type} [CommRing O] [AddCommGroup W] [Module O W] [Fintype ι] {N n : ℕ}
    (bs : Fin n → W) (P : ι → V) (Q : Finset V) (w : W ⊗[O] AddMonoidAlgebra O (↥Q → ZMod N))
    (hw : w ∈ LinearMap.range ((Submodule.span O (Set.range bs)).subtype.rTensor _)) :
    ∃ m : Fin n → MvPolynomial ι O, ∀ (O' : Type) [CommRing O'] [Algebra O O'] (u : ι → O'ˣ)
      (χ : Multiplicative (↥Q → ZMod N) →* O'ˣ), IsChi P Q u χ →
      TensorProduct.comm O W O' (((AddMonoidAlgebra.lift O O' (↥Q → ZMod N)
        ((Units.coeHom O').comp χ)).toLinearMap.lTensor W) w) =
      ∑ c, aeval (fun q => (u q : O') - 1) (m c) • (1 : O') ⊗ₜ[O] bs c := by
  classical
  obtain ⟨w, rfl⟩ := hw
  induction w with
  | zero => exact ⟨0, fun _ _ _ _ _ _ => by simp⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', hm'⟩ := hy
    refine ⟨m + m', fun O' _ _ u χ h => ?_⟩
    simp only [map_add, hm O' u χ h, hm' O' u χ h, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | tmul x g =>
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 x.2
    have hg : ∃ p : MvPolynomial ι O, ∀ (O' : Type) [CommRing O'] [Algebra O O'] (u : ι → O'ˣ)
        (χ : Multiplicative (↥Q → ZMod N) →* O'ˣ), IsChi P Q u χ →
        AddMonoidAlgebra.lift O O' (↥Q → ZMod N) ((Units.coeHom O').comp χ) g =
          aeval (fun q => (u q : O') - 1) p := by
      induction g using AddMonoidAlgebra.induction_on with
      | of y =>
        refine ⟨∏ q, if h : P q ∈ Q then (1 + X q) ^ (y ⟨P q, h⟩).val else 1, fun O' _ _ u χ h => ?_⟩
        rw [AddMonoidAlgebra.lift_of, MonoidHom.comp_apply, h, map_prod, map_prod]
        refine Finset.prod_congr rfl fun q _ => ?_
        split_ifs <;> simp
      | add f g hf hg =>
        obtain ⟨p, hp⟩ := hf
        obtain ⟨p', hp'⟩ := hg
        exact ⟨p + p', fun O' _ _ u χ h => by rw [map_add, map_add, hp O' u χ h, hp' O' u χ h]⟩
      | smul r f hf =>
        obtain ⟨p, hp⟩ := hf
        exact ⟨r • p, fun O' _ _ u χ h => by rw [map_smul, map_smul, hp O' u χ h]⟩
    obtain ⟨p, hp⟩ := hg
    refine ⟨fun c => v c • p, fun O' _ _ u χ h => ?_⟩
    rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.comm_tmul, AlgHom.toLinearMap_apply,
      hp O' u χ h, Submodule.subtype_apply, ← hv, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]

end GlobalTheory.TwistDet

end
