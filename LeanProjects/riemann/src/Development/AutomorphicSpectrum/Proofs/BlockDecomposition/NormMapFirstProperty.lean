import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open scoped TensorProduct
open Finset

namespace GlobalTheory.CompanionTheory.NormOnto

theorem field_norm_onto {L : Type*} [Field L] [Finite L] (ρ : RingAut L) (e : ℕ) (he : 0 < e)
    (h1 : ρ ^ e = 1) (hne : ∀ j, 0 < j → j < e → ρ ^ j ≠ 1) (a : L) (ha0 : a ≠ 0) (hfix : ρ a = a) :
    ∃ w : L, w ≠ 0 ∧ ∏ j ∈ range e, (ρ ^ j) w = a := by
  have hord : orderOf ρ = e := by
    rw [orderOf_eq_iff he]
    exact ⟨h1, fun m hm hm0 => hne m hm0 hm⟩
  have hfin : IsOfFinOrder ρ := isOfFinOrder_iff_pow_eq_one.2 ⟨e, he, h1⟩
  let G := Subgroup.zpowers ρ
  haveI : Finite G := Finite.of_equiv _ (finEquivZPowers hfin)
  haveI := Fintype.ofFinite G
  let K := FixedPoints.subfield G L
  have haK : a ∈ K := by
    intro g
    have hle : G ≤ MulAction.stabilizer (RingAut L) a := by
      rw [Subgroup.zpowers_le]
      exact hfix
    exact hle g.2
  let aK : K := ⟨a, haK⟩
  have haK0 : aK ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
  obtain ⟨v, hv⟩ := FiniteField.unitsMap_norm_surjective K L (Units.mk0 aK haK0)
  have hv' : Algebra.norm K (v : L) = aK := by
    have := congrArg Units.val hv
    simpa using this
  refine ⟨v, v.ne_zero, ?_⟩
  have h2 := Algebra.norm_eq_prod_automorphisms K (v : L)
  rw [hv'] at h2
  have h3 : (∏ σ : L ≃ₐ[K] L, σ (v : L)) = ∏ g : G, (g : RingAut L) (v : L) := by
    symm
    exact Fintype.prod_equiv (FixedPoints.toAlgAutMulEquiv G L) _ _ (fun g => rfl)
  have h4 : (∏ g : G, (g : RingAut L) (v : L)) = ∏ i : Fin (orderOf ρ), (ρ ^ (i : ℕ)) (v : L) := by
    symm
    exact Fintype.prod_equiv (finEquivZPowers hfin) _ _ (fun i => by simp [finEquivZPowers_apply])
  rw [h3, h4, Fin.prod_univ_eq_prod_range (fun i => (ρ ^ i) (v : L)), hord] at h2
  exact h2.symm

theorem prod_range_stride {M : Type*} [CommMonoid M] (f : ℕ → M) (d e : ℕ) (hd : 0 < d)
    (h : ∀ i, ¬ d ∣ i → f i = 1) :
    ∏ i ∈ range (d * e), f i = ∏ j ∈ range e, f (d * j) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, prod_range_add, ih, prod_range_succ]
    congr 1
    rw [prod_eq_single 0]
    · simp
    · intro b hb hb0
      apply h
      have hlt := mem_range.1 hb
      intro hdvd
      have : d ∣ b := (Nat.dvd_add_right (Dvd.intro _ rfl)).1 hdvd
      exact hb0 (Nat.eq_zero_of_dvd_of_lt this hlt)
    · intro h0
      exact absurd (mem_range.2 hd) h0

end GlobalTheory.CompanionTheory.NormOnto

namespace GlobalTheory.CompanionTheory.NormOnto

section Core

variable {B : Type*} [CommRing B]

def pull (T : RingAut B) (I : Ideal B) : Ideal B := I.comap (T : B →+* B)

theorem mem_pull_iter (T : RingAut B) (i : ℕ) (I : Ideal B) (b : B) :
    b ∈ (pull T)^[i] I ↔ (T ^ i) b ∈ I := by
  induction i generalizing I with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [pull, Ideal.mem_comap, pow_succ']
    rfl

theorem pull_iter_period (T : RingAut B) (ℓ : ℕ) (hT : T ^ ℓ = 1) (I : Ideal B) :
    (pull T)^[ℓ] I = I := by
  ext b
  rw [mem_pull_iter, hT]
  rfl

theorem pull_iter_max (T : RingAut B) (i : ℕ) (I : Ideal B) (hI : I.IsMaximal) :
    ((pull T)^[i] I).IsMaximal := by
  induction i generalizing I with
  | zero => simpa
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    exact Ideal.comap_isMaximal_of_surjective (T : B →+* B) (RingEquiv.surjective T)

theorem norm_fixed (T : RingAut B) (ℓ : ℕ) (hℓ : 0 < ℓ) (hT : T ^ ℓ = 1) (c : B) :
    T (∏ i ∈ range ℓ, (T ^ i) c) = ∏ i ∈ range ℓ, (T ^ i) c := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hs : ∀ i, T ((T ^ i) c) = (T ^ (i + 1)) c := fun i => by
    rw [pow_succ']; rfl
  rw [map_prod]
  simp only [hs]
  rw [prod_range_succ, prod_range_succ' (fun i => (T ^ i) c), hT]
  simp

theorem local_step [Finite B] (T : RingAut B) (ℓ : ℕ) (hℓ : 0 < ℓ) (hT : T ^ ℓ = 1)
    (n : ℕ) (x y : Fin n → B)
    (hxy : ∀ j < ℓ, ∑ i, x i * (T ^ j) (y i) = if j = 0 then 1 else 0)
    (a : B) (ha : IsUnit a) (hfix : T a = a) (m : Ideal B) (hm : m.IsMaximal) :
    ∃ w : B, w ∉ m ∧ ∀ c : B, c - w ∈ m →
      (∀ i, ¬ Function.minimalPeriod (pull T) m ∣ i → c - 1 ∈ (pull T)^[i] m) →
      ∏ i ∈ range ℓ, (T ^ i) c - a ∈ m := by
  classical
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Finite (B ⧸ m) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := m))
  set d := Function.minimalPeriod (pull T) m with hd
  have hper : Function.IsPeriodicPt (pull T) ℓ m := pull_iter_period T ℓ hT m
  have hdpos : 0 < d := Function.minimalPeriod_pos_of_mem_periodicPts ⟨ℓ, hℓ, hper⟩
  obtain ⟨e, he⟩ : d ∣ ℓ := hper.minimalPeriod_dvd
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hdm : ∀ b, (T ^ d) b ∈ m ↔ b ∈ m := fun b => by
    rw [← mem_pull_iter, Function.iterate_minimalPeriod]
  have hmap : m = Ideal.map ((T ^ d : RingAut B) : B ≃+* B) m := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨((T ^ d : RingAut B) : B ≃+* B).symm b, ?_, by simp⟩
      rw [← hdm]
      simpa using hb
    · rintro ⟨z, hz, rfl⟩
      exact (hdm z).2 hz
  let ρ : RingAut (B ⧸ m) := Ideal.quotientEquiv m m ((T ^ d : RingAut B) : B ≃+* B) hmap
  have hρ : ∀ (j : ℕ) (b : B), (ρ ^ j) (Ideal.Quotient.mk m b) =
      Ideal.Quotient.mk m ((T ^ (d * j)) b) := by
    intro j
    induction j with
    | zero => intro b; simp
    | succ j ih =>
      intro b
      rw [pow_succ', Nat.mul_succ, Nat.add_comm, pow_add]
      show ρ ((ρ ^ j) _) = _
      rw [ih]
      rfl
  have hρ1 : ρ ^ e = 1 := by
    ext z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hρ, ← he, hT]
    rfl
  have hne : ∀ j, 0 < j → j < e → ρ ^ j ≠ 1 := by
    intro j hj0 hje h1
    have hlt : d * j < ℓ := by rw [he]; exact Nat.mul_lt_mul_of_pos_left hje hdpos
    have h0 := hxy (d * j) hlt
    rw [if_neg (Nat.mul_ne_zero hdpos.ne' hj0.ne')] at h0
    have h1' := hxy 0 hℓ
    rw [if_pos rfl] at h1'
    have hy : ∀ b, Ideal.Quotient.mk m ((T ^ (d * j)) b) = Ideal.Quotient.mk m b := by
      intro b
      rw [← hρ, h1]
      rfl
    have := congrArg (Ideal.Quotient.mk m) h0
    simp only [map_sum, map_mul, hy, map_zero] at this
    have h2 := congrArg (Ideal.Quotient.mk m) h1'
    simp only [map_sum, map_mul, pow_zero, map_one] at h2
    have h3 : ∀ i, Ideal.Quotient.mk m (((1 : RingAut B)) (y i)) = Ideal.Quotient.mk m (y i) :=
      fun i => rfl
    simp only [h3] at h2
    rw [this] at h2
    exact zero_ne_one h2
  have ha0 : Ideal.Quotient.mk m a ≠ 0 := by
    intro h
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h) ha)
  have hafix : ρ (Ideal.Quotient.mk m a) = Ideal.Quotient.mk m a := by
    have : (T ^ d) a = a := by
      have : ∀ k : ℕ, (T ^ k) a = a := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ']
          show T ((T ^ k) a) = a
          rw [ih, hfix]
      exact this d
    show Ideal.Quotient.mk m ((T ^ d) a) = _
    rw [this]
  obtain ⟨wb, hw0, hw⟩ := field_norm_onto ρ e hepos hρ1 hne _ ha0 hafix
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective wb
  refine ⟨w, fun h => hw0 (Ideal.Quotient.eq_zero_iff_mem.2 h), ?_⟩
  intro c hcw hc1
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_prod, he,
    prod_range_stride (fun i => Ideal.Quotient.mk m ((T ^ i) c)) d e hdpos, ← hw]
  · apply prod_congr rfl
    intro j _
    rw [← hρ, Ideal.Quotient.eq.2 hcw]
  · intro i hi
    have := (mem_pull_iter T i m (c - 1)).1 (hc1 i hi)
    rw [map_sub, map_one] at this
    have h := Ideal.Quotient.eq.2 this
    simpa using h

end Core

end GlobalTheory.CompanionTheory.NormOnto

namespace GlobalTheory.CompanionTheory.NormOnto

section Core2

variable {B : Type*} [CommRing B]

theorem norm_mod_max [Finite B] (T : RingAut B) (ℓ : ℕ) (hℓ : 0 < ℓ) (hT : T ^ ℓ = 1)
    (n : ℕ) (x y : Fin n → B)
    (hxy : ∀ j < ℓ, ∑ i, x i * (T ^ j) (y i) = if j = 0 then 1 else 0)
    (a : B) (ha : IsUnit a) (hfix : T a = a) :
    ∃ c : Bˣ, ∀ m : Ideal B, m.IsMaximal → ∏ i ∈ range ℓ, (T ^ i) (c : B) - a ∈ m := by
  classical
  have hmul : ∀ (k i : ℕ) (I : Ideal B), (pull T)^[i * k] ((pull T)^[k] I) = (pull T)^[(i + 1) * k] I := by
    intro k i I
    rw [← Function.iterate_add_apply]
    congr 1
    ring
  let s : Setoid (Ideal B) :=
    { r := fun I J => ∃ i, (pull T)^[i] I = J
      iseqv :=
        { refl := fun I => ⟨0, rfl⟩
          symm := by
            rintro I J ⟨i, rfl⟩
            refine ⟨(ℓ - 1) * i, ?_⟩
            rw [hmul, Nat.sub_add_cancel hℓ]
            rw [Nat.mul_comm]
            exact Function.IsPeriodicPt.const_mul (pull_iter_period T ℓ hT I) i
          trans := by
            rintro I J K ⟨i, rfl⟩ ⟨j, rfl⟩
            exact ⟨j + i, Function.iterate_add_apply _ _ _ _⟩ } }
  let rep : Ideal B → Ideal B := fun I => (Quotient.mk s I).out
  have hrep : ∀ I, ∃ i, (pull T)^[i] (rep I) = I := fun I => Quotient.mk_out (s := s) I
  have hrep_eq : ∀ I J, (∃ i, (pull T)^[i] I = J) → rep I = rep J := by
    intro I J h
    have : Quotient.mk s I = Quotient.mk s J := Quotient.sound h
    simp only [rep, this]
  have hrr : ∀ I, rep (rep I) = rep I := by
    intro I
    obtain ⟨i, hi⟩ := hrep I
    exact hrep_eq _ _ ⟨i, hi⟩
  have hloc := fun (m : {I : Ideal B // I.IsMaximal}) =>
    local_step T ℓ hℓ hT n x y hxy a ha hfix m.1 m.2
  choose w hw hwc using hloc
  let W : {I : Ideal B // I.IsMaximal} → B := fun I => if rep I.1 = I.1 then w I else 1
  haveI : Finite (Ideal B) :=
    Finite.of_injective (fun I : Ideal B => (I : Set B)) SetLike.coe_injective
  have hco : Pairwise (Function.onFun IsCoprime fun I : {I : Ideal B // I.IsMaximal} => I.1) := by
    intro I J hIJ
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne I.2 J.2 (fun h => hIJ (Subtype.ext h))
  obtain ⟨c, hc⟩ := Ideal.exists_forall_sub_mem_ideal hco W
  have hcu : IsUnit c := by
    by_contra hnu
    obtain ⟨M, hM, hcM⟩ := exists_max_ideal_of_mem_nonunits hnu
    have h1 := hc ⟨M, hM⟩
    by_cases hr : rep M = M
    · have h2 : c - w ⟨M, hM⟩ ∈ M := by simpa [W, hr] using h1
      have h3 := M.sub_mem hcM h2
      rw [sub_sub_cancel] at h3
      exact hw ⟨M, hM⟩ h3
    · have h2 : c - 1 ∈ M := by simpa [W, hr] using h1
      have h3 := M.sub_mem hcM h2
      rw [sub_sub_cancel] at h3
      exact hM.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨cu, rfl⟩ := hcu
  refine ⟨cu, fun J hJ => ?_⟩
  obtain ⟨i0, hi0⟩ := hrep J
  set I := rep J with hI
  obtain ⟨i1, hi1⟩ : ∃ i, (pull T)^[i] J = I := s.symm ⟨i0, hi0⟩
  have hImax : I.IsMaximal := hi1 ▸ pull_iter_max T i1 J hJ
  have hII : rep I = I := hrr J
  have hmemI : ∏ i ∈ range ℓ, (T ^ i) (cu : B) - a ∈ I := by
    apply hwc ⟨I, hImax⟩
    · have h1 := hc ⟨I, hImax⟩
      simpa [W, hII] using h1
    · intro i hi
      have hmax' := pull_iter_max T i I hImax
      have hne : (pull T)^[i] I ≠ I := fun h =>
        hi (Function.IsPeriodicPt.minimalPeriod_dvd h)
      have hr : rep ((pull T)^[i] I) ≠ (pull T)^[i] I := by
        rw [← hrep_eq I _ ⟨i, rfl⟩, hII]
        exact hne.symm
      have h1 := hc ⟨_, hmax'⟩
      simpa [W, hr] using h1
  have hzfix : T (∏ i ∈ range ℓ, (T ^ i) (cu : B) - a) = ∏ i ∈ range ℓ, (T ^ i) (cu : B) - a := by
    rw [map_sub, norm_fixed T ℓ hℓ hT, hfix]
  have hz : ∀ k : ℕ, (T ^ k) (∏ i ∈ range ℓ, (T ^ i) (cu : B) - a) =
      ∏ i ∈ range ℓ, (T ^ i) (cu : B) - a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ']
      show T ((T ^ k) _) = _
      rw [ih, hzfix]
  rw [← hi0, mem_pull_iter, hz]
  exact hmemI

end Core2

theorem fixed_tensor {κ κ' A : Type*} [Field κ] [CommRing κ'] [Algebra κ κ'] [CommRing A] [Algebra κ A]
    (τ : κ' ≃ₐ[κ] κ') (hfix : ∀ z : κ', τ z = z → z ∈ Set.range (algebraMap κ κ'))
    (s : κ' ⊗[κ] A) (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id κ A) s = s) :
    ∃ t : A, s = 1 ⊗ₜ[κ] t := by
  classical
  let C := Module.Basis.ofVectorSpace κ A
  obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right C s
  have hinj := TensorProduct.sum_tmul_basis_right_injective (M := κ') C
  have hbb : b.mapRange τ (map_zero τ) = b := by
    apply hinj
    simp only [Finsupp.coe_lsum]
    change (Finsupp.mapRange τ (map_zero τ) b).sum (fun i m => m ⊗ₜ[κ] C i) =
      b.sum (fun i m => m ⊗ₜ[κ] C i)
    rw [Finsupp.sum_mapRange_index (by simp)]
    conv_rhs => rw [← hs]
    simp [Finsupp.sum, map_sum]
  have hb : ∀ i, τ (b i) = b i := fun i => by
    have := DFunLike.congr_fun hbb i
    simpa using this
  choose t ht using fun i => hfix (b i) (hb i)
  refine ⟨∑ i ∈ b.support, t i • C i, ?_⟩
  rw [Finsupp.sum, TensorProduct.tmul_sum]
  apply sum_congr rfl
  intro i _
  rw [← ht i, TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

end GlobalTheory.CompanionTheory.NormOnto

namespace GlobalTheory.CompanionTheory.NormOnto

theorem norm_onto : PositivityTheory.Rg.Tf.Loc.N1 := by
  intro κ κ' A _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual a
  obtain ⟨x, y, hxy⟩ := hdual
  classical
  by_cases hκ' : Subsingleton κ'
  · haveI : Subsingleton (κ' ⊗[κ] A) := by
      refine ⟨fun p q => ?_⟩
      have hz : ∀ s : κ' ⊗[κ] A, s = 0 := by
        intro s
        induction s with
        | zero => rfl
        | tmul z b => rw [Subsingleton.elim z 0, TensorProduct.zero_tmul]
        | add u v hu hv => rw [hu, hv, add_zero]
      rw [hz p, hz q]
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI : Nontrivial κ' := not_subsingleton_iff_nontrivial.1 hκ'
  haveI : Finite κ' := Module.finite_of_finite κ
  haveI : Finite (κ' ⊗[κ] A) := Module.finite_of_finite κ
  let T : RingAut (κ' ⊗[κ] A) :=
    (Algebra.TensorProduct.congr τ (AlgEquiv.refl : A ≃ₐ[κ] A)).toRingEquiv
  have hT1 : ∀ (z : κ') (b : A), T (z ⊗ₜ[κ] b) = τ z ⊗ₜ[κ] b := fun z b => rfl
  have hTm : ∀ (i : ℕ) (z : κ') (b : A), (T ^ i) (z ⊗ₜ[κ] b) = (τ ^ i) z ⊗ₜ[κ] b := by
    intro i
    induction i with
    | zero => intro z b; rfl
    | succ i ih =>
      intro z b
      rw [pow_succ', pow_succ']
      show T ((T ^ i) _) = τ ((τ ^ i) z) ⊗ₜ[κ] b
      rw [ih, hT1]
  have hTi : ∀ (i : ℕ) (s : κ' ⊗[κ] A),
      Algebra.TensorProduct.map ((τ ^ i : κ' ≃ₐ[κ] κ').toAlgHom) (AlgHom.id κ A) s = (T ^ i) s := by
    intro i s
    induction s with
    | zero => simp
    | tmul z b => rw [hTm]; rfl
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hT : T ^ ℓ = 1 := by
    ext s
    rw [← hTi, hτ]
    induction s with
    | zero => simp
    | tmul z b => rfl
    | add u v hu hv => rw [map_add, hu, hv]; rfl
  have hXY : ∀ j < ℓ, ∑ i, (x i ⊗ₜ[κ] (1 : A)) * (T ^ j) (y i ⊗ₜ[κ] (1 : A)) =
      if j = 0 then 1 else 0 := by
    intro j hj
    have h := congrArg (fun z : κ' => z ⊗ₜ[κ] (1 : A)) (hxy j hj)
    simp only [TensorProduct.sum_tmul] at h
    simp only [hTm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [h]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _
  have haU : IsUnit ((1 : κ') ⊗ₜ[κ] (a : A)) :=
    a.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[κ] κ' ⊗[κ] A)
  obtain ⟨c, hc⟩ := norm_mod_max T ℓ hℓ hT ℓ (fun i => x i ⊗ₜ[κ] (1 : A))
    (fun i => y i ⊗ₜ[κ] (1 : A)) hXY _ haU (by rw [hT1, map_one])
  refine ⟨c, ?_⟩
  simp only [hTi]
  rw [Algebra.TensorProduct.includeRight_apply, ← sub_eq_zero]
  set z := ∏ i ∈ range ℓ, (T ^ i) (c : κ' ⊗[κ] A) - (1 : κ') ⊗ₜ[κ] (a : A) with hz
  have hzfix : T z = z := by
    rw [hz, map_sub, norm_fixed T ℓ hℓ hT, hT1, map_one]
  obtain ⟨t, ht⟩ := fixed_tensor τ hfix z (by
    have := hTi 1 z
    rw [pow_one, pow_one] at this
    exact this.trans hzfix)
  have hznil : IsNilpotent z := by
    have hj : z ∈ (⊥ : Ideal (κ' ⊗[κ] A)).jacobson := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro M ⟨-, hM⟩
      exact hc M hM
    rw [IsArtinianRing.jacobson_eq_radical] at hj
    obtain ⟨k, hk⟩ := hj
    exact ⟨k, by simpa using hk⟩
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[κ] κ' ⊗[κ] A) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective κ κ')
  have htn : IsNilpotent t := by
    obtain ⟨k, hk⟩ := hznil
    refine ⟨k, hinj ?_⟩
    rw [map_pow, map_zero, Algebra.TensorProduct.includeRight_apply, ← ht, hk]
  have ht0 : t = 0 := htn.eq_zero
  rw [ht, ht0, TensorProduct.tmul_zero]

end GlobalTheory.CompanionTheory.NormOnto
