import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEpsteinZetaContinuationStatement

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.PartialZeta

variable {K : Type} [Field K] [NumberField K]

theorem place_unique [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (v w : InfinitePlace K) : v = w := by
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, h2] at hr
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at hc
  have h1 : Fintype.card (InfinitePlace K) = 1 := by omega
  exact Fintype.card_le_one_iff.1 h1.le v w

theorem normSq_eq [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩
  have hprod := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply,
    InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex _))] at hprod
  rw [hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Algebra.coe_norm_int]
  norm_cast

theorem finite_units [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) : Finite (𝓞 K)ˣ := by
  have hfin := Embeddings.finite_of_norm_le K ℂ 1
  have hone : ∀ (u : (𝓞 K)ˣ) (ψ : K →+* ℂ), ‖ψ ((u : 𝓞 K) : K)‖ = 1 := by
    intro u ψ
    have h := normSq_eq h2 ψ (u : 𝓞 K)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  haveI := hfin.to_subtype
  refine Finite.of_injective (fun u : (𝓞 K)ˣ =>
    (⟨((u : 𝓞 K) : K), (u : 𝓞 K).isIntegral_coe, fun ψ => (hone u ψ).le⟩ :
      {x : K | IsIntegral ℤ x ∧ ∀ ψ : K →+* ℂ, ‖ψ x‖ ≤ 1})) ?_
  intro u v huv
  exact Units.ext (RingOfIntegers.ext (by simpa using congrArg Subtype.val huv))

theorem im_ne_zero [IsTotallyComplex K] (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) :
    (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ≠ 0 := by
  intro him
  have h2 : Module.finrank ℚ K = 2 := by
    rw [← RingOfIntegers.rank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h
    exact b.ne_zero 0 (RingOfIntegers.ext (by simpa using h))
  have ha0 : φ (b 0 : K) ≠ 0 := (map_ne_zero φ).2 hb0
  have hca0 : starRingEnd ℂ (φ (b 0 : K)) ≠ 0 := (map_ne_zero _).2 ha0
  set y : K := (b 1 : K) / (b 0 : K) with hy
  have hφy : (φ y).im = 0 := by
    have hq : φ y = (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)) /
        (Complex.normSq (φ (b 0 : K)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_div_mul_left _ _ hca0, hy, map_div₀]
    rw [hq, Complex.div_ofReal_im, him, zero_div]
  by_cases hyq : y ∈ Set.range (algebraMap ℚ K)
  · obtain ⟨q, hq⟩ := hyq
    have hK : (q.den : K) * (b 1 : K) = (q.num : K) * (b 0 : K) := by
      have hd : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
      have h1 : (b 1 : K) = (q : K) * (b 0 : K) := by
        rw [← eq_ratCast (algebraMap ℚ K) q, hq, hy, div_mul_cancel₀ _ hb0]
      rw [h1, Rat.cast_def]
      field_simp
    have hz : (-q.num) • b 0 + ((q.den : ℤ)) • b 1 = 0 := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.coe_eq_algebraMap] at hK ⊢
      simp only [zsmul_eq_mul, map_add, map_mul, map_intCast, map_neg, map_zero, map_natCast]
      push_cast at hK ⊢
      linear_combination hK
    have := Fintype.linearIndependent_iff.1 b.linearIndependent ![-q.num, (q.den : ℤ)]
      (by simpa [Fin.sum_univ_two] using hz) 1
    simp at this
  · have hli : LinearIndependent ℚ ![(1 : K), y] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have hg1 : g 1 = 0 := by
        by_contra hne
        apply hyq
        refine ⟨-(g 0) / g 1, ?_⟩
        rw [eq_ratCast]
        push_cast
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hg
        rw [div_eq_iff (by exact_mod_cast hne)]
        linear_combination -hg
      have hg0 : g 0 = 0 := by
        rw [hg1, zero_smul, add_zero, smul_eq_zero] at hg
        simpa using hg
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
    have hreal : ∀ x : K, (φ x).im = 0 := by
      intro x
      have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), y]) := htop ▸ Submodule.mem_top
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hx
      simp [Fin.sum_univ_two, Rat.smul_def, hφy]
    have hR : ComplexEmbedding.IsReal φ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.2 (hreal x)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex
      (InfinitePlace.mk φ))) (InfinitePlace.isReal_mk_iff.2 hR)

theorem abs_im_eq (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (J : Ideal (𝓞 K))
    (e : Module.Basis (Fin 2) ℤ J) :
    |(starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im| =
      Ideal.absNorm J * |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| := by
  classical
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψdef
  have hψ : ∀ x : 𝓞 K, φ (x : K) = ψ x := fun x => rfl
  have he : ∀ j, ψ (e j : 𝓞 K) = (b.repr (e j : 𝓞 K) 0 : ℂ) * ψ (b 0) +
      (b.repr (e j : 𝓞 K) 1 : ℂ) * ψ (b 1) := by
    intro j
    conv_lhs => rw [← b.sum_repr (e j : 𝓞 K)]
    simp [map_sum, Fin.sum_univ_two, zsmul_eq_mul]
  have hdet := Ideal.natAbs_det_basis_change b J e
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at hdet
  simp only [hψ]
  rw [← hdet, Nat.cast_natAbs, Int.cast_abs, ← abs_mul, he 0, he 1]
  congr 1
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem cls_iff {M : ℕ} (D : RayData K M) (c : D.G) (B I : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹)
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI0 : I ≠ ⊥) :
    D.cls I = c ↔ ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I * B := by
  constructor
  · intro h
    have hIB : D.cls (I * B) = 1 := by
      rw [D.cls_mul I B hI hB hI0 hB0, h, hc, mul_inv_cancel]
    obtain ⟨a, b', ha, hb, ha1, hb1, hab⟩ :=
      (D.cls_eq_one_iff (hI.mul_left hB) (mul_ne_zero hI0 hB0)).1 hIB
    have hmem : b' ∈ Ideal.span {a} := by
      have : b' ∈ Ideal.span {a} * (I * B) := by
        rw [hab]; exact Ideal.mem_span_singleton_self b'
      exact Ideal.mul_le_left this
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_, ?_⟩
    · have hax : a * x - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [mul_comm, hx]; exact hb1
      have : x - 1 = (a * x - 1) - (a - 1) * x := by ring
      rw [this]
      exact Ideal.sub_mem _ hax (Ideal.mul_mem_right x _ ha1)
    · have hspan : Ideal.span {a} * (I * B) = Ideal.span {a} * Ideal.span {x} := by
        rw [hab, ← hx, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
      have ha' : Ideal.span {a} ≠ 0 := by
        rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact ha
      exact (mul_left_cancel₀ ha' hspan).symm
  · rintro ⟨x, hx1, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
      exact mul_ne_zero hI0 hB0 hx.symm
    have h1 : D.cls (I * B) = 1 := by rw [← hx]; exact D.cls_span hx0 hx1
    rw [D.cls_mul I B hI hB hI0 hB0, hc] at h1
    exact mul_inv_eq_one.1 h1

theorem lattice_bij (N B : Ideal (𝓞 K)) (hB : IsCoprime B N) (e : Module.Basis (Fin 2) ℤ ↥(N * B))
    (x₀ : 𝓞 K) (h0 : x₀ ∈ B) (h1 : x₀ - 1 ∈ N) :
    ∃ f : ℤ × ℤ ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N},
      ∀ p, (f p : 𝓞 K) = x₀ + p.1 * (e 0 : 𝓞 K) + p.2 * (e 1 : 𝓞 K) := by
  have hmemNB : ∀ y : ↥(N * B), (y : 𝓞 K) ∈ B ∧ (y : 𝓞 K) ∈ N := fun y =>
    ⟨Ideal.mul_le_right y.2, Ideal.mul_le_left y.2⟩
  let g : ↥(N * B) ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N} :=
    { toFun := fun y => ⟨x₀ + y, B.add_mem h0 (hmemNB y).1, by
        rw [add_sub_right_comm]; exact N.add_mem h1 (hmemNB y).2⟩
      invFun := fun x => ⟨x.1 - x₀, by
        rw [← Ideal.inf_eq_mul_of_isCoprime hB.symm]
        refine ⟨?_, ?_⟩
        · have : x.1 - x₀ = (x.1 - 1) - (x₀ - 1) := by ring
          rw [this]; exact N.sub_mem x.2.2 h1
        · exact B.sub_mem x.2.1 h0⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  refine ⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩
  simp [g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]

theorem ne_bot_of_coprime {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hI
  exact hM hI

theorem gen_bij {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G)
    (B : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹) :
    ∃ f : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
        {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} ≃
        {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}},
      ∀ p, Ideal.span {(f p : 𝓞 K)} = p.1 * B := by
  classical
  have hgen : ∀ I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c},
      ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I.1 * B := fun I =>
    (cls_iff D c B I.1 hB hB0 hc I.2.1 (ne_bot_of_coprime hM I.2.1)).1 I.2.2
  choose g hg1 hg using hgen
  have hgB : ∀ I, g I ∈ B := fun I => by
    have : g I ∈ Ideal.span {g I} := Ideal.mem_span_singleton_self _
    rw [hg I] at this
    exact Ideal.mul_le_right this
  have hg0 : ∀ I, g I ≠ 0 := fun I h => by
    have := hg I
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (ne_bot_of_coprime hM I.2.1) hB0 this.symm
  let F : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
      {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} →
      {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} := fun p =>
    ⟨(p.2.1 : 𝓞 K) * g p.1, Ideal.mul_mem_left _ _ (hgB p.1), by
      have : (p.2.1 : 𝓞 K) * g p.1 - 1 = (p.2.1 : 𝓞 K) * (g p.1 - 1) + ((p.2.1 : 𝓞 K) - 1) := by
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hg1 p.1)) p.2.2⟩
  have hspanF : ∀ p, Ideal.span {(F p : 𝓞 K)} = p.1 * B := fun p => by
    show Ideal.span {(p.2.1 : 𝓞 K) * g p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.1.isUnit, hg]
  have hinj : Function.Injective F := by
    rintro ⟨I, u⟩ ⟨I', u'⟩ h
    have h1 := hspanF (I, u)
    rw [h, hspanF (I', u')] at h1
    have hII : I = I' := Subtype.ext (mul_right_cancel₀ (by simpa using hB0) h1.symm)
    subst hII
    have h2 : (u.1 : 𝓞 K) * g I = (u'.1 : 𝓞 K) * g I := congrArg Subtype.val h
    have h3 : (u.1 : 𝓞 K) = (u'.1 : 𝓞 K) := mul_right_cancel₀ (hg0 I) h2
    rw [Subtype.ext (Units.ext h3)]
  have hsurj : Function.Surjective F := by
    rintro ⟨x, hxB, hx1⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hM
      rw [Ideal.eq_top_iff_one]
      have := (Ideal.neg_mem_iff _).2 hx1
      simpa using this
    have hle : Ideal.span {x} ≤ B := (Ideal.span_singleton_le_iff_mem _).2 hxB
    obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 hle
    have hxc : IsCoprime (Ideal.span {x}) (Ideal.span {(M : 𝓞 K)}) := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have : (1 : 𝓞 K) = x - (x - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
        (Ideal.mem_sup_right hx1)
    have hIc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
      rw [hI] at hxc; exact hxc.of_mul_left_right
    have hIB : Ideal.span {x} = I * B := by rw [hI, mul_comm]
    have hIcls : D.cls I = c :=
      (cls_iff D c B I hB hB0 hc hIc (ne_bot_of_coprime hM hIc)).2 ⟨x, hx1, hIB⟩
    let I' : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} :=
      ⟨I, hIc, hIcls⟩
    have hass : Associated (g I') x := by
      rw [← Ideal.span_singleton_eq_span_singleton, hg I', hIB]
    obtain ⟨u, hu⟩ := hass
    have hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have hgu : g I' * u - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [hu]; exact hx1
      have : (u : 𝓞 K) - 1 = (g I' * u - 1) - (g I' - 1) * u := by ring
      rw [this]
      exact Ideal.sub_mem _ hgu (Ideal.mul_mem_right _ _ (hg1 I'))
    refine ⟨(I', ⟨u, hu1⟩), Subtype.ext ?_⟩
    show (u : 𝓞 K) * g I' = x
    rw [mul_comm, hu]
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun p => hspanF p⟩

theorem hasSum_cnt {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G) (s a : ℂ)
    (h : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} =>
      (Ideal.absNorm I.1 : ℂ) ^ (-s)) a) : LSeriesHasSum (D.cnt c) s a := by
  classical
  let C := {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}
  let Nm : C → ℕ := fun I => Ideal.absNorm I.1
  have h' : HasSum (fun x : (Σ n : ℕ, {I : C // Nm I = n}) =>
      (Ideal.absNorm x.2.1.1 : ℂ) ^ (-s)) a :=
    (Equiv.sigmaFiberEquiv Nm).hasSum_iff.2 h
  refine h'.sigma (fun n => ?_)
  let en : {I : C // Nm I = n} ≃
      {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = c} :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.2, x.1.2.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.2⟩, y.2.2.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  haveI : Finite {I : C // Nm I = n} := by
    haveI := D.finite_cnt c n
    exact Finite.of_equiv _ en.symm
  haveI : Fintype {I : C // Nm I = n} := Fintype.ofFinite _
  have hconst : (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) =
      fun _ => (n : ℂ) ^ (-s) := by
    funext x
    rw [show Ideal.absNorm x.1.1 = n from x.2]
  show HasSum (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) _
  rw [hconst]
  by_cases hn : n = 0
  · subst hn
    haveI : IsEmpty {I : C // Nm I = 0} := ⟨fun x => by
      have hx : x.1.1 = ⊥ := Ideal.absNorm_eq_zero_iff.1 x.2
      exact ne_bot_of_coprime hM x.1.2.1 hx⟩
    rw [LSeries.term_zero]
    exact hasSum_empty
  · rw [LSeries.term_of_ne_zero hn]
    have hs := hasSum_fintype (fun _ : {I : C // Nm I = n} => (n : ℂ) ^ (-s))
    convert hs using 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, RayData.cnt,
      ← Nat.card_congr en, Nat.card_eq_fintype_card, Complex.cpow_neg, div_eq_mul_inv]

theorem partial_zeta_continuation : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ D : RayData K M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : D.G, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = ρ ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → LSeriesSummable (D.cnt c) s ∧ Z s = (s - 1) * LSeries (D.cnt c) s := by
  intro K _ _ _ h2 M hM2 D
  classical
  have hrk : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, h2]
  have hNnorm : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton,
      show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) (M : ℤ) by simp, Algebra.norm_algebraMap, hrk]
    simp [Int.natAbs_pow]
  have hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_top] at this
    nlinarith
  have hN0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_bot] at this
    nlinarith
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk
  let φ : K →+* ℂ := Classical.choice inferInstance
  let ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K)
  haveI : Finite (𝓞 K)ˣ := finite_units h2
  let U := {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}
  haveI : Fintype U := Fintype.ofFinite _
  have hw : 0 < Fintype.card U := Fintype.card_pos_iff.2 ⟨⟨1, by simp⟩⟩
  set ib := |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| with hib
  have hib0 : 0 < ib := abs_pos.2 (im_ne_zero φ b)
  refine ⟨Real.pi / (Fintype.card U * (M : ℝ) ^ 2 * ib), by positivity, fun c => ?_⟩
  obtain ⟨B, hBc, hB0, hcB⟩ := D.cls_surj c⁻¹
  obtain ⟨x₀, hx₀B, z, hz, hxz⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hBc))
  have hx₀1 : x₀ - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
    have : x₀ - 1 = -z := by rw [← hxz]; ring
    rw [this]; exact (Ideal.neg_mem_iff _).2 hz
  have hNB0 : Ideal.span {(M : 𝓞 K)} * B ≠ ⊥ := mul_ne_zero hN0 hB0
  let e : Module.Basis (Fin 2) ℤ ↥(Ideal.span {(M : 𝓞 K)} * B) := Ideal.selfBasis b _ hNB0
  obtain ⟨fL, hfL⟩ := lattice_bij (Ideal.span {(M : 𝓞 K)}) B hBc e x₀ hx₀B hx₀1
  obtain ⟨fG, hfG⟩ := gen_bij hM D c B hBc hB0 hcB
  have hBn0 : Ideal.absNorm B ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hIm := abs_im_eq φ b (Ideal.span {(M : 𝓞 K)} * B) e
  rw [map_mul, hNnorm] at hIm
  have him : (starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hIm
    have : (0 : ℝ) < ((M ^ 2 * Ideal.absNorm B : ℕ) : ℝ) * ib := by
      have : 0 < M ^ 2 * Ideal.absNorm B := by positivity
      positivity
    linarith
  have hψL : ∀ p : ℤ × ℤ, ψ (fL p : 𝓞 K) =
      φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) + p.2 * φ ((e 1 : 𝓞 K) : K) := by
    intro p
    rw [hfL p]
    simp [ψ, map_add, map_mul, map_intCast]
  have hnz : ∀ m n : ℤ, φ (x₀ : K) + m * φ ((e 0 : 𝓞 K) : K) + n * φ ((e 1 : 𝓞 K) : K) ≠ 0 := by
    intro m n h0
    have hx := (fL (m, n)).2.2
    have hzero : (fL (m, n) : 𝓞 K) = 0 := by
      have := hψL (m, n)
      rw [h0] at this
      have hinj : Function.Injective ψ :=
        φ.injective.comp (IsFractionRing.injective (𝓞 K) K)
      exact hinj (by rw [this, map_zero])
    rw [hzero, zero_sub] at hx
    apply hM
    rw [Ideal.eq_top_iff_one]
    simpa using (Ideal.neg_mem_iff _).2 hx
  obtain ⟨Z0, hZd, hZ1, hZm1, hZs⟩ := GlobalTheory.T.lattice_epstein_zeta_continuation _ _ _ him hnz
  have hBc0 : (Ideal.absNorm B : ℂ) ≠ 0 := by exact_mod_cast hBn0
  have hwc : (Fintype.card U : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  refine ⟨fun s => (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s, ?_, ?_, ?_, ?_⟩
  · exact ((differentiable_id.const_cpow (Or.inl hBc0)).div_const _).mul hZd
  · simp only [Complex.cpow_one]
    rw [hZ1, hIm]
    push_cast
    field_simp
    rw [← hib]
    exact div_self (by exact_mod_cast hib0.ne')
  · simp [hZm1]
  · intro s hs
    obtain ⟨hsum, hZeq⟩ := hZs s hs
    set S := ∑' p : ℤ × ℤ, ((‖φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) +
      p.2 * φ ((e 1 : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) with hS
    let G : {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} → ℂ := fun x =>
      ((‖ψ (x : 𝓞 K)‖ ^ 2 : ℝ) : ℂ) ^ (-s)
    have hG : HasSum G S := by
      rw [← fL.hasSum_iff]
      convert hsum.hasSum using 1
      funext p
      simp only [Function.comp_apply, G, hψL p]
    have hGG := fG.hasSum_iff.2 hG
    have hterm : ∀ p, (G ∘ fG) p = (Ideal.absNorm p.1.1 : ℂ) ^ (-s) *
        (Ideal.absNorm B : ℂ) ^ (-s) := by
      intro p
      simp only [Function.comp_apply, G]
      have hn := normSq_eq h2 φ (fG p : 𝓞 K)
      rw [hfG p, map_mul] at hn
      show ((‖φ ((fG p : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) = _
      rw [hn]
      push_cast
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast (Ideal.absNorm B),
        ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    have hfib := hGG.prod_fiberwise (fun I => hasSum_fintype (fun u : U => (G ∘ fG) (I, u)))
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfib
    have hcnt : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧
        D.cls I = c} => (Ideal.absNorm I.1 : ℂ) ^ (-s))
        ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U * S) := by
      have hBs : (Ideal.absNorm B : ℂ) ^ s ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; tauto
      refine (hfib.mul_left ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U)).congr_fun (fun I => ?_)
      rw [Complex.cpow_neg (Ideal.absNorm B : ℂ)]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have hL := hasSum_cnt hM D c s _ hcnt
    refine ⟨hL.LSeriesSummable, ?_⟩
    rw [hL.LSeries_eq]
    show (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s = _
    rw [hZeq]
    ring

end GlobalTheory.Mem.PartialZeta

end
