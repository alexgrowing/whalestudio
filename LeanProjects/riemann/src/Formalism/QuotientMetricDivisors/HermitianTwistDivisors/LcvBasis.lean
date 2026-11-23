import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic

open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.DivisionValues.LocalCovolumeBasis

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

theorem mem_locP' (p : Ideal (𝓞 K)) [p.IsPrime] (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem len_zero_of_le (P Q : Submodule (𝓞 K) V) (h : P ≤ Q) :
    Module.length (𝓞 K) (↥P ⧸ Q.comap P.subtype) = 0 := by
  apply Module.length_eq_zero_iff.mpr
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.Quotient.eq]
      exact h (x - y).2

theorem kill {N : Submodule (𝓞 K) V} {a : V} {p : Ideal (𝓞 K)} (hp : ∀ r, r ∈ p ↔ r • a ∈ N)
    {s : 𝓞 K} (hs : s ∈ p) {y : V} (hy : y ∈ N ⊔ Submodule.span (𝓞 K) {a}) : s • y ∈ N := by
  obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [smul_add, smul_smul]
  exact N.add_mem (N.smul_mem s hn) ((hp _).mp (Ideal.mul_mem_right c p hs))

theorem len_off {N : Submodule (𝓞 K) V} {a : V} {p : Ideal (𝓞 K)} (hpmax : p.IsMaximal)
    (hp : ∀ r, r ∈ p ↔ r • a ∈ N) (q : Ideal (𝓞 K)) [hq : q.IsPrime] (hqmax : q ≠ ⊤)
    (hqp : q ≠ p) :
    Module.length (𝓞 K) (↥(localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})) ⧸
      (localization₂ q N).comap (localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})).subtype) = 0 := by
  apply len_zero_of_le
  have : ∃ s ∈ p, s ∉ q := by
    by_contra hcon
    push Not at hcon
    exact hqp (hpmax.eq_of_le hqmax hcon).symm
  obtain ⟨s, hsp, hsq⟩ := this
  intro x hx
  obtain ⟨t, htq, htx⟩ := (mem_locP' q _ x).mp hx
  refine (mem_locP' q N x).mpr ⟨s * t, fun h => (hq.mem_or_mem h).elim hsq htq, ?_⟩
  rw [mul_smul]
  exact kill hp hsp htx

theorem len_on {N : Submodule (𝓞 K) V} {a : V} (q : Ideal (𝓞 K)) [hq : q.IsPrime]
    (hqmax : q.IsMaximal) (hp : ∀ r, r ∈ q ↔ r • a ∈ N) :
    Module.length (𝓞 K) (↥(localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})) ⧸
      (localization₂ q N).comap (localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})).subtype) = 1 := by
  set M := N ⊔ Submodule.span (𝓞 K) {a} with hM
  have haM : a ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self a)
  have haL : a ∈ localization₂ q M := locBasic_le_locS _ M haM
  set Q := (localization₂ q N).comap (localization₂ q M).subtype with hQ
  let f : 𝓞 K →ₗ[𝓞 K] ↥(localization₂ q M) ⧸ Q :=
    Q.mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) (↥(localization₂ q M)) ⟨a, haL⟩
  have hf : ∀ r, f r = Submodule.Quotient.mk (r • (⟨a, haL⟩ : ↥(localization₂ q M))) := fun r => rfl
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨t, htq, htx⟩ := (mem_locP' q M x.1).mp x.2
      obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp htx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      obtain ⟨u, i, hi, hui⟩ := hqmax.exists_inv htq
      refine ⟨u * c, ?_⟩
      rw [hf, Submodule.Quotient.eq]
      show ((u * c) • a - (x : V)) ∈ localization₂ q N
      refine (mem_locP' q N _).mpr ⟨t, htq, ?_⟩
      have hc : c = t * (u * c) + i * c := by linear_combination (-c) * hui
      have key : t • ((u * c) • a - (x : V)) = -((i * c) • a) - n := by
        rw [smul_sub, ← hnz, smul_smul]
        have : c • a = (t * (u * c)) • a + (i * c) • a := by rw [← add_smul, ← hc]
        rw [this]; abel
      rw [key]
      exact N.sub_mem (N.neg_mem ((hp _).mp (Ideal.mul_mem_right c q hi))) hn
  have hker : LinearMap.ker f = q := by
    ext r
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      obtain ⟨t, htq, htr⟩ := (mem_locP' q N _).mp h
      have : (t * r) • a ∈ N := by rw [mul_smul]; exact htr
      exact ((hq.mem_or_mem ((hp _).mpr this)).resolve_left htq)
    · intro h
      exact locBasic_le_locS _ N ((hp r).mp h)
  have e : (↥(localization₂ q M) ⧸ Q) ≃ₗ[𝓞 K] (𝓞 K ⧸ q) :=
    (f.quotKerEquivOfSurjective hsurj).symm.trans (Submodule.quotEquivOfEq _ _ hker)
  have : IsSimpleModule (𝓞 K) (𝓞 K ⧸ q) := isSimpleModule_iff_isCoatom.mpr hqmax.out
  have : IsSimpleModule (𝓞 K) (↥(localization₂ q M) ⧸ Q) := IsSimpleModule.congr e
  exact Module.length_eq_one_iff.mpr inferInstance

end Formalism.DivisionValues.LocalCovolumeBasis

namespace Formalism.DivisionValues.LocalCovolumeBasis

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

theorem le_of_image {A N M1 M2 : Submodule (𝓞 K) V} (hN2 : N ≤ M2) (h1A : M1 ≤ A)
    (himg : (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M1 : Set V)) =
      (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M2 : Set V))) : M1 ≤ M2 := by
  intro x hx
  have hmem : (N.comap A.subtype).mkQ ⟨x, h1A hx⟩ ∈
      (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M1 : Set V)) := ⟨⟨x, h1A hx⟩, hx, rfl⟩
  rw [himg] at hmem
  obtain ⟨z, hz, hzx⟩ := hmem
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzx
  have h1 : ((z : V) - x) ∈ M2 := hN2 hzx
  have h2 : (z : V) ∈ M2 := hz
  have : x = (z : V) - ((z : V) - x) := by abel
  rw [this]
  exact M2.sub_mem h2 h1

theorem key (A : Submodule (𝓞 K) V) : ∀ (n : ℕ) (N : Submodule (𝓞 K) V), N ≤ A →
    N.toAddSubgroup.relIndex A.toAddSubgroup = n → n ≠ 0 →
    (∀ w : HeightOneSpectrum (𝓞 K), Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal A) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal A).subtype) ≠ ⊤) ∧
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => locLen w.asIdeal A N).Finite ∧
    Real.log (n : ℝ) = ∑ᶠ w : HeightOneSpectrum (𝓞 K),
      Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal A N : ℝ) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hNA hn hn0
  by_cases hEq : N = A
  · subst hEq
    have h0 : ∀ w : HeightOneSpectrum (𝓞 K), locLen w.asIdeal N N = 0 :=
      fun w => indexBasic_locLen_self _ _
    have hn1 : n = 1 := by rw [← hn]; exact AddSubgroup.relIndex_self _
    refine ⟨fun w => by rw [len_zero_of_le _ _ le_rfl]; exact ENat.zero_ne_top, ?_, ?_⟩
    · simp [h0]
    · simp [h0, hn1]
  have hlt : N < A := lt_of_le_of_ne hNA hEq
  have hfin : Finite (↥A ⧸ N.comap A.subtype) := by
    apply Nat.finite_of_card_ne_zero
    rw [← hn] at hn0
    exact hn0

  set S : Set (Submodule (𝓞 K) V) := {M | N < M ∧ M ≤ A} with hS
  have hSfin : S.Finite := by
    apply Set.Finite.of_finite_image (f := fun M : Submodule (𝓞 K) V =>
      (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M : Set V))) (Set.toFinite _)
    intro M1 h1 M2 h2 himg
    exact le_antisymm (le_of_image h2.1.le h1.2 himg) (le_of_image h1.1.le h2.2 himg.symm)
  obtain ⟨M0, hM0⟩ := hSfin.exists_minimal ⟨A, hlt, le_rfl⟩
  have hM0S : M0 ∈ S := hM0.1
  have hmin : ∀ M, N < M → M ≤ M0 → M = M0 := fun M h1 h2 =>
    le_antisymm h2 (hM0.2 ⟨h1, h2.trans hM0S.2⟩ h2)
  obtain ⟨a, haM0, haN⟩ := SetLike.exists_of_lt hM0S.1
  have hstep : ∀ b ∈ M0, b ∉ N → N ⊔ Submodule.span (𝓞 K) {b} = M0 := by
    intro b hb hbN
    apply hmin
    · refine lt_of_le_of_ne le_sup_left fun h => hbN ?_
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)
    · exact sup_le hM0S.1.le ((Submodule.span_singleton_le_iff_mem _ _).mpr hb)
  have hM0eq : M0 = N ⊔ Submodule.span (𝓞 K) {a} := (hstep a haM0 haN).symm

  set p : Ideal (𝓞 K) := N.comap (LinearMap.toSpanSingleton (𝓞 K) V a) with hpdef
  have hp : ∀ r, r ∈ p ↔ r • a ∈ N := fun r => Iff.rfl
  have hpmax : p.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => haN (by simpa using (hp 1).mp h), ?_⟩
    intro J x hpJ hxp hxJ
    have hxa : x • a ∈ M0 := M0.smul_mem x haM0
    have hxaN : x • a ∉ N := fun h => hxp ((hp x).mpr h)
    have e := hstep _ hxa hxaN
    have ha' : a ∈ N ⊔ Submodule.span (𝓞 K) {x • a} := e ▸ haM0
    obtain ⟨m, hm, z, hz, hmz⟩ := Submodule.mem_sup.mp ha'
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have h1 : (1 - s * x) ∈ p := by
      rw [hp, sub_smul, one_smul, mul_smul]
      rw [sub_eq_iff_eq_add.mpr hmz.symm]
      exact hm
    have h2 : s * x ∈ J := J.mul_mem_left s hxJ
    have := J.add_mem (hpJ h1) h2
    simpa using this

  have hcard : N.toAddSubgroup.relIndex M0.toAddSubgroup = Ideal.absNorm p := by
    have haM0' : a ∈ M0 := haM0
    let g : 𝓞 K →ₗ[𝓞 K] ↥M0 ⧸ N.comap M0.subtype :=
      (N.comap M0.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) (↥M0) ⟨a, haM0'⟩
    have hg : ∀ r, g r = Submodule.Quotient.mk (r • (⟨a, haM0'⟩ : ↥M0)) := fun r => rfl
    have hgs : Function.Surjective g := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H x =>
        have hx : (x : V) ∈ N ⊔ Submodule.span (𝓞 K) {a} := hM0eq ▸ x.2
        obtain ⟨m, hm, z, hz, hmz⟩ := Submodule.mem_sup.mp hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
        refine ⟨c, ?_⟩
        rw [hg, Submodule.Quotient.eq]
        show (c • a - (x : V)) ∈ N
        rw [← hmz]
        have : c • a - (m + c • a) = -m := by abel
        rw [this]; exact N.neg_mem hm
    have hker : LinearMap.ker g = p := by
      ext r
      rw [LinearMap.mem_ker, hg, Submodule.Quotient.mk_eq_zero, hp]
      rfl
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (g.quotKerEquivOfSurjective hgs)).toEquiv)).symm
  set m := M0.toAddSubgroup.relIndex A.toAddSubgroup with hmdef
  have hprod : Ideal.absNorm p * m = n := by
    rw [← hcard, hmdef, AddSubgroup.relIndex_mul_relIndex _ _ _ hM0S.1.le hM0S.2, hn]
  have hm0 : m ≠ 0 := fun h => hn0 (by rw [← hprod, h, mul_zero])
  have hN0 : Ideal.absNorm p ≠ 0 := fun h => hn0 (by rw [← hprod, h, zero_mul])
  have hN1 : Ideal.absNorm p ≠ 1 := fun h => hpmax.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hmn : m < n := by
    rw [← hprod]
    have : 2 ≤ Ideal.absNorm p := by omega
    calc m = 1 * m := (one_mul m).symm
      _ < Ideal.absNorm p * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
  obtain ⟨ihlen, ihsupp, ihlog⟩ := ih m hmn M0 hM0S.2 rfl hm0
  have hpbot : p ≠ ⊥ := fun h => hN0 (Ideal.absNorm_eq_zero_iff.mpr h)
  let w0 : HeightOneSpectrum (𝓞 K) := ⟨p, hpmax.isPrime, hpbot⟩

  have hsmall : ∀ w : HeightOneSpectrum (𝓞 K), Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal M0) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal M0).subtype) =
        ((if w = w0 then 1 else 0 : ℕ) : ℕ∞) := by
    intro w
    rw [hM0eq]
    by_cases hw : w = w0
    · have hwp : w.asIdeal = p := by rw [hw]
      rw [if_pos hw]
      have := len_on (N := N) (a := a) w.asIdeal (hwp ▸ hpmax) (fun r => by rw [hwp]; exact hp r)
      rw [this]; rfl
    · rw [if_neg hw]
      have hwp : w.asIdeal ≠ p := fun h => hw (HeightOneSpectrum.ext h)
      have := len_off (N := N) (a := a) hpmax hp w.asIdeal w.isMaximal.ne_top hwp
      rw [this]; rfl
  have hadd : ∀ w : HeightOneSpectrum (𝓞 K), Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal A) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal A).subtype) =
      Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal M0) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal M0).subtype) +
      Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal A) ⧸ (localization₂ w.asIdeal M0).comap (localization₂ w.asIdeal A).subtype) :=
    fun w => indexBasic_len_add _ _ _ (locBasic_locS_mono _ hM0S.1.le)
      (locBasic_locS_mono _ hM0S.2)
  have hlen : ∀ w : HeightOneSpectrum (𝓞 K),
      locLen w.asIdeal A N = (if w = w0 then 1 else 0) + locLen w.asIdeal A M0 := by
    intro w
    unfold locLen
    rw [hadd w, hsmall w, ENat.toNat_add (ENat.natCast_ne_top _) (ihlen w), ENat.toNat_natCast]
  refine ⟨fun w => by rw [hadd w, hsmall w]; exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ihlen w⟩,
    ?_, ?_⟩
  · apply (ihsupp.union (Set.finite_singleton w0)).subset
    intro w hw
    rw [Function.mem_support, hlen w] at hw
    by_cases h : w = w0
    · exact Or.inr h
    · left
      rw [if_neg h, zero_add] at hw
      exact hw
  · have hsum : (fun w : HeightOneSpectrum (𝓞 K) =>
        Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal A N : ℝ)) =
        fun w => Real.log (Ideal.absNorm w.asIdeal : ℝ) * ((if w = w0 then 1 else 0 : ℕ) : ℝ) +
          Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal A M0 : ℝ) := by
      funext w
      rw [hlen w]; push_cast; ring
    rw [hsum, finsum_add_distrib, ← ihlog, finsum_eq_single _ w0]
    · rw [if_pos rfl, ← hprod]
      push_cast
      rw [Real.log_mul (by exact_mod_cast hN0) (by exact_mod_cast hm0)]
      simp [w0]
    · intro w hw; simp [hw]
    · apply (Set.finite_singleton w0).subset
      intro w hw
      by_contra h
      have h' : w ≠ w0 := h
      apply hw
      simp [h']
    · apply ihsupp.subset
      intro w hw
      rw [Function.mem_support] at hw ⊢
      intro h; apply hw; rw [h]; simp

end Formalism.DivisionValues.LocalCovolumeBasis

namespace Formalism.DivisionValues.LocalCovolumeBasis

variable {K : Type} [Field K] [NumberField K]

theorem exists_int_mul {d : ℕ} (L : Submodule (𝓞 K) (Fin d → K))
    (hsp : Submodule.span K (L : Set (Fin d → K)) = ⊤) (e : Fin d → Fin d → K) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ i, ((y : K)) • e i ∈ L := by
  classical
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set (Fin d → K))
  have hfin : s.Finite := hli.setFinite
  haveI : Fintype s := hfin.fintype
  let f : Basis s K (Fin d → K) := Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  have hf : ∀ j, f j ∈ L := fun j => by rw [Basis.mk_apply]; exact hsL j.2
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun q : Fin d × s => f.repr (e q.1) q.2)
  refine ⟨y, hy, fun i => ?_⟩
  rw [← f.sum_repr (e i), Finset.smul_sum]
  apply Submodule.sum_mem
  intro j _
  have hi : IsIntegral ℤ (y • f.repr (e i) j) :=
    hint _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • f.repr (e i) j, hi⟩
  have hr : ((y : K)) • (f.repr (e i) j • f j) = r • f j := by
    rw [← algebraMap_smul K r, smul_smul]
    congr 1
    show (y : K) * f.repr (e i) j = y • f.repr (e i) j
    rw [zsmul_eq_mul]
  rw [hr]
  exact Submodule.smul_mem _ _ (hf j)

end Formalism.DivisionValues.LocalCovolumeBasis

namespace Formalism.DivisionValues

open LocalCovolumeBasis in

theorem covolume_via_basis : LcvBasis := by
  intro K _ _ _ _ d X hX L hL e he
  classical
  set E := Submodule.span (𝓞 K) (Set.range e) with hEdef
  have hLfg : L.FG := hL.fg
  have hLsp : Submodule.span K (L : Set (Fin d → K)) = ⊤ := hL.span_eq_top
  obtain ⟨y, hy0, hyL⟩ := exists_int_mul L hLsp e
  have hyK : (y : K) ≠ 0 := Int.cast_ne_zero.mpr hy0
  set e' : Fin d → Fin d → K := fun i => (y : K) • e i with he'def
  have he' : LinearIndependent K e' := by
    have := he.units_smul (fun _ => Units.mk0 (y : K) hyK)
    convert this using 1
    funext i
    simp [e', Units.smul_def]
  set E' := Submodule.span (𝓞 K) (Set.range e') with hE'def
  have hE'L : E' ≤ L := Submodule.span_le.mpr (Set.range_subset_iff.mpr hyL)
  have hE'E : E' ≤ E := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    show (y : K) • e i ∈ E
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) y
  have hEfg : E.FG := Submodule.fg_span (Set.finite_range e)
  have hE'fg : E'.FG := Submodule.fg_span (Set.finite_range e')
  have hrkL : Formalism.HN.rkK L = d := by
    unfold Formalism.HN.rkK; rw [hLsp, finrank_top, Module.finrank_fin_fun]
  have hrkE : Formalism.HN.rkK E = d := by
    unfold Formalism.HN.rkK
    rw [hEdef, Submodule.span_span_of_tower, finrank_span_eq_card he, Fintype.card_fin]
  obtain ⟨hG1, -⟩ := Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e he
  obtain ⟨-, hG2⟩ :=
    Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e' he'
  have h1 := hG2 L hLfg hE'L hrkL
  have h2 := hG2 E hEfg hE'E hrkE
  have hpos : ∀ M : Submodule (𝓞 K) (Fin d → K), M.FG →
      0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X M :=
    fun M hM => (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hM).2.2
  set rL := E'.toAddSubgroup.relIndex L.toAddSubgroup with hrL
  set rE := E'.toAddSubgroup.relIndex E.toAddSubgroup with hrE
  have hrL0 : rL ≠ 0 := by
    intro h
    have := hpos E' hE'fg
    rw [← h1, h, Nat.cast_zero, mul_zero] at this
    exact lt_irrefl _ this
  have hrE0 : rE ≠ 0 := by
    intro h
    have := hpos E' hE'fg
    rw [← h2, h, Nat.cast_zero, mul_zero] at this
    exact lt_irrefl _ this
  obtain ⟨lenL, suppL, logL⟩ := key L rL E' hE'L rfl hrL0
  obtain ⟨lenE, suppE, logE⟩ := key E rE E' hE'E rfl hrE0
  have hidx : ∀ w : HeightOneSpectrum (𝓞 K),
      idx w E L = (locLen w.asIdeal E E' : ℤ) - locLen w.asIdeal L E' :=
    fun w => indexBasic_lidx_via w.asIdeal E L E' hE'E hE'L (lenE w) (lenL w)
  have hn : (finrank ℚ K : ℝ) ≠ 0 := (Nat.cast_pos.mpr Module.finrank_pos).ne'
  set fE := fun w : HeightOneSpectrum (𝓞 K) =>
    Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal E E' : ℝ) with hfEdef
  set fL := fun w : HeightOneSpectrum (𝓞 K) =>
    Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal L E' : ℝ) with hfLdef
  have hpt : (fun w => lw w * (idx w E L : ℝ)) =
      fun w => (fE w - fL w) * (1 / (finrank ℚ K : ℝ)) := by
    funext w
    rw [hidx w]
    simp only [lw, fE, fL]
    push_cast
    field_simp
  have hfE : (Function.support fE).Finite := by
    apply suppE.subset
    intro w hw h
    apply hw
    simp [fE, h]
  have hfL : (Function.support fL).Finite := by
    apply suppL.subset
    intro w hw h
    apply hw
    simp [fL, h]
  refine ⟨?_, ?_⟩
  · rw [hpt]
    apply (hfE.union hfL).subset
    intro w hw
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
    apply hw
    simp only
    rw [hcon.1, hcon.2]
    simp
  · unfold lcv
    rw [hpt, ← finsum_mul, finsum_sub_distrib hfE hfL, ← logE, ← logL]
    have hlogL : Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X L) =
        Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E') - Real.log (rL : ℝ) := by
      rw [← h1, Real.log_mul (hpos L hLfg).ne' (Nat.cast_ne_zero.mpr hrL0)]
      ring
    have hlogE : Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E) =
        Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E') - Real.log (rE : ℝ) := by
      rw [← h2, Real.log_mul (hpos E hEfg).ne' (Nat.cast_ne_zero.mpr hrE0)]
      ring
    have hdet : Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E) =
        ∑ v, Real.log (gram X v e).det.re := by
      have hne := (hpos E hEfg).ne'
      rw [hG1] at hne ⊢
      exact Real.log_prod fun v hv => Finset.prod_ne_zero_iff.mp hne v hv
    rw [hlogL, ← hdet]
    field_simp
    linarith [hlogE]

end Formalism.DivisionValues
