import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace Ker

theorem matrix_data (L : PeriodPair) (α : ℂ) (h : MulStable L α) :
    ∃ a b c d : ℤ, α * L.ω₁ = a * L.ω₁ + c * L.ω₂ ∧ α * L.ω₂ = b * L.ω₁ + d * L.ω₂ ∧
      (2 * α.re = ((a + d : ℤ) : ℝ)) ∧ Complex.normSq α = ((a * d - b * c : ℤ) : ℝ) := by
  obtain ⟨a, c, hac⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₁_mem_lattice)
  obtain ⟨b, d, hbd⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₂_mem_lattice)
  refine ⟨a, b, c, d, hac.symm, hbd.symm, ?_⟩
  have hind := LinearIndependent.pair_iff.1 L.indep
  have hω1 : L.ω₁ ≠ 0 := by
    intro h0
    exact one_ne_zero (hind 1 0 (by simp [h0])).1
  have hω2 : L.ω₂ ≠ 0 := by
    intro h0
    exact one_ne_zero (hind 0 1 (by simp [h0])).2
  have e1 : (α - a) * L.ω₁ = c * L.ω₂ := by linear_combination -hac
  have e2 : (α - d) * L.ω₂ = b * L.ω₁ := by linear_combination -hbd
  have hq : α ^ 2 - ((a + d : ℤ) : ℂ) * α + ((a * d - b * c : ℤ) : ℂ) = 0 := by
    have h0 : ((α - a) * (α - d) - b * c) * (L.ω₁ * L.ω₂) = 0 := by
      linear_combination (α - d) * L.ω₂ * e1 + c * L.ω₂ * e2
    rcases mul_eq_zero.1 h0 with h1 | h1
    · push_cast
      linear_combination h1
    · exact absurd h1 (mul_ne_zero hω1 hω2)
  by_cases him : α.im = 0
  · have hαr : α = (α.re : ℂ) := Complex.ext (by simp) (by simp [him])
    obtain ⟨h1, h2⟩ := hind (α.re - a) (-c) (by
      rw [Complex.real_smul, Complex.real_smul]
      rw [hαr] at e1
      push_cast
      linear_combination e1)
    obtain ⟨h3, h4⟩ := hind (-b) (α.re - d) (by
      rw [Complex.real_smul, Complex.real_smul]
      rw [hαr] at e2
      push_cast
      linear_combination e2)
    have ha : (a : ℝ) = α.re := by linarith
    have hd : (d : ℝ) = α.re := by linarith
    have hb : (b : ℝ) = 0 := by linarith
    have hc : (c : ℝ) = 0 := by linarith
    constructor
    · push_cast
      linarith
    · rw [Complex.normSq_apply, him]
      push_cast
      rw [ha, hd, hb, hc]
      ring
  · have hq' : (starRingEnd ℂ α) ^ 2 - ((a + d : ℤ) : ℂ) * starRingEnd ℂ α + ((a * d - b * c : ℤ) : ℂ) = 0 := by
      have := congrArg (starRingEnd ℂ) hq
      simpa using this
    have hne : α - starRingEnd ℂ α ≠ 0 := by
      intro h0
      apply him
      have := congrArg Complex.im h0
      simp at this
      linarith
    have hsum : α + starRingEnd ℂ α = ((a + d : ℤ) : ℂ) := by
      have h0 : (α - starRingEnd ℂ α) * (α + starRingEnd ℂ α - ((a + d : ℤ) : ℂ)) = 0 := by
        linear_combination hq - hq'
      linear_combination (mul_eq_zero.1 h0).resolve_left hne
    have hprod : α * starRingEnd ℂ α = ((a * d - b * c : ℤ) : ℂ) := by
      linear_combination α * hsum - hq
    constructor
    · have h2 := Complex.add_conj α
      rw [hsum] at h2
      exact_mod_cast h2.symm
    · have h3 := Complex.mul_conj α
      rw [hprod] at h3
      exact_mod_cast h3.symm

def mulEnd (L : PeriodPair) (α : ℂ) (h : MulStable L α) : L.lattice →ₗ[ℤ] L.lattice where
  toFun x := ⟨α * x, h _ x.2⟩
  map_add' x y := by ext; simp [mul_add]
  map_smul' n x := by ext; simp; ring

theorem mulEnd_injective (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    Function.Injective (mulEnd L α h) := by
  intro x y hxy
  have := congrArg Subtype.val hxy
  apply Subtype.ext
  simpa [mulEnd, hα] using this

theorem det_mulEnd (L : PeriodPair) (α : ℂ) (h : MulStable L α) :
    ((LinearMap.det (mulEnd L α h) : ℤ) : ℝ) = Complex.normSq α := by
  obtain ⟨a, b, c, d, hac, hbd, -, hn⟩ := matrix_data L α h
  have h0 : mulEnd L α h (L.latticeBasis 0) = a • L.latticeBasis 0 + c • L.latticeBasis 1 := by
    apply Subtype.ext
    simp [mulEnd, L.latticeBasis_zero, L.latticeBasis_one, hac]
  have h1 : mulEnd L α h (L.latticeBasis 1) = b • L.latticeBasis 0 + d • L.latticeBasis 1 := by
    apply Subtype.ext
    simp [mulEnd, L.latticeBasis_zero, L.latticeBasis_one, hbd]
  have key : LinearMap.det (mulEnd L α h) = a * d - b * c := by
    rw [← LinearMap.det_toMatrix L.latticeBasis, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, h0, h1] <;> ring
  rw [hn, key]

theorem card_quot (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    ((Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) : ℕ) : ℝ) = Complex.normSq α := by
  haveI := Module.Free.of_basis L.latticeBasis
  haveI := Module.Finite.of_basis L.latticeBasis
  have key : (LinearMap.det (mulEnd L α h)).natAbs =
      Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) := by
    rw [← Submodule.natAbs_det_equiv (LinearMap.range (mulEnd L α h))
      (LinearEquiv.ofInjective (mulEnd L α h) (mulEnd_injective L α hα h))]
    congr 2
  rw [← key, Nat.cast_natAbs, Int.cast_abs, det_mulEnd, abs_of_nonneg (Complex.normSq_nonneg α)]

theorem mk_eq_iff (L : PeriodPair) (α : ℂ) (h : MulStable L α) (u v : L.lattice) :
    (Submodule.Quotient.mk u : L.lattice ⧸ LinearMap.range (mulEnd L α h)) = Submodule.Quotient.mk v ↔
      ∃ x ∈ L.lattice, (u : ℂ) - v = α * x := by
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, x.2, ?_⟩
    have := congrArg Subtype.val hx
    simpa [mulEnd] using this.symm
  · rintro ⟨x, hx, hxe⟩
    exact ⟨⟨x, hx⟩, Subtype.ext (by simp [mulEnd, hxe])⟩

end Ker

open Ker

theorem mul_stable_integral : MulStableIntegral := by
  unfold MulStableIntegral
  intro L α h
  obtain ⟨a, b, c, d, -, -, htr, hn⟩ := matrix_data L α h
  have h1 : α + conj α = ((a + d : ℤ) : ℂ) := by
    rw [Complex.add_conj]
    exact_mod_cast htr
  have h2 : α * conj α = ((a * d - b * c : ℤ) : ℂ) := by
    rw [Complex.mul_conj]
    exact_mod_cast hn
  exact ⟨a + d, a * d - b * c, h1, h2, by linear_combination α * h1 - h2⟩

theorem kernel_reps_card : KerRepsCard := by
  unfold KerRepsCard
  intro L α S hα h hS
  obtain ⟨h1, h2, h3⟩ := hS
  haveI : Finite (L.lattice ⧸ LinearMap.range (mulEnd L α h)) := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    have hc := card_quot L α hα h
    rw [h0] at hc
    have hn : Complex.normSq α = 0 := by rw [← hc]; simp
    exact hα (Complex.normSq_eq_zero.1 hn)
  have hout : ∀ q : L.lattice ⧸ LinearMap.range (mulEnd L α h), Submodule.Quotient.mk (Quotient.out q) = q :=
    fun q => Quotient.out_eq' q
  have hdiv : ∀ u : ℂ, α * (u / α) = u := fun u => by field_simp
  classical
  haveI := Fintype.ofFinite (L.lattice ⧸ LinearMap.range (mulEnd L α h))
  have hφ0 : ∀ P : S, (Submodule.Quotient.mk (⟨α * P, (h1 P P.2).1⟩ : L.lattice) :
      L.lattice ⧸ LinearMap.range (mulEnd L α h)) ≠ 0 := by
    intro P h0
    rw [← Submodule.Quotient.mk_zero, mk_eq_iff] at h0
    obtain ⟨x, hx, hxe⟩ := h0
    have hPx : (P : ℂ) = x := by simpa [hα] using hxe
    exact (h1 P P.2).2 (hPx ▸ hx)
  let φ : S → {q : L.lattice ⧸ LinearMap.range (mulEnd L α h) // ¬ q = 0} :=
    fun P => ⟨Submodule.Quotient.mk (⟨α * P, (h1 P P.2).1⟩ : L.lattice), hφ0 P⟩
  have hinj : Function.Injective φ := by
    intro P P' hPP
    have h6 := congrArg Subtype.val hPP
    simp only [φ] at h6
    rw [mk_eq_iff] at h6
    obtain ⟨x, hx, hxe⟩ := h6
    have hxe' : α * (P : ℂ) - α * (P' : ℂ) = α * x := hxe
    have hd : (P : ℂ) - P' = x := mul_left_cancel₀ hα (by rw [mul_sub]; exact hxe')
    exact Subtype.ext (h2 P P.2 P' P'.2 (hd ▸ hx))
  have hsurj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    have hz1 : α * (((Quotient.out q : L.lattice) : ℂ) / α) ∈ L.lattice := by
      rw [hdiv]; exact (Quotient.out q).2
    have hz2 : ((Quotient.out q : L.lattice) : ℂ) / α ∉ L.lattice := by
      intro hm
      apply hq
      rw [← hout q, ← Submodule.Quotient.mk_zero, mk_eq_iff]
      exact ⟨_, hm, by rw [hdiv]; simp⟩
    obtain ⟨P, hP, hzP⟩ := h3 _ hz1 hz2
    refine ⟨⟨P, hP⟩, Subtype.ext ?_⟩
    show (Submodule.Quotient.mk (⟨α * P, (h1 P hP).1⟩ : L.lattice) :
      L.lattice ⧸ LinearMap.range (mulEnd L α h)) = q
    conv_rhs => rw [← hout q]
    rw [mk_eq_iff]
    refine ⟨-(((Quotient.out q : L.lattice) : ℂ) / α - P), neg_mem hzP, ?_⟩
    show α * (P : ℂ) - ((Quotient.out q : L.lattice) : ℂ) = _
    rw [mul_neg, mul_sub, hdiv]
    ring
  have hcard : Nat.card S = Nat.card {q : L.lattice ⧸ LinearMap.range (mulEnd L α h) // ¬ q = 0} :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
  have hc1 : Nat.card {q : L.lattice ⧸ LinearMap.range (mulEnd L α h) // ¬ q = 0} + 1 =
      Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have := Fintype.card_pos (α := L.lattice ⧸ LinearMap.range (mulEnd L α h))
    omega
  have e2 : Nat.card S = S.card := by simp
  rw [← card_quot L α hα h]
  exact_mod_cast (show S.card + 1 = Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) by
    rw [← e2, hcard, hc1])

theorem kernel_reps_exist : KerRepsExist := by
  unfold KerRepsExist
  intro L α hα h
  haveI : Finite (L.lattice ⧸ LinearMap.range (mulEnd L α h)) := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    have hc := card_quot L α hα h
    rw [h0] at hc
    have hn : Complex.normSq α = 0 := by rw [← hc]; simp
    exact hα (Complex.normSq_eq_zero.1 hn)
  have hout : ∀ q : L.lattice ⧸ LinearMap.range (mulEnd L α h), Submodule.Quotient.mk (Quotient.out q) = q :=
    fun q => Quotient.out_eq' q
  have hdiv : ∀ u : ℂ, α * (u / α) = u := fun u => by field_simp
  classical
  haveI := Fintype.ofFinite (L.lattice ⧸ LinearMap.range (mulEnd L α h))
  refine ⟨(Finset.univ.filter (fun q : L.lattice ⧸ LinearMap.range (mulEnd L α h) => q ≠ 0)).image
    (fun q => ((Quotient.out q : L.lattice) : ℂ) / α), ?_⟩
  unfold IsKerReps
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨by rw [hdiv]; exact (Quotient.out q).2, ?_⟩
    intro hm
    apply hq
    rw [← hout q, ← Submodule.Quotient.mk_zero, mk_eq_iff]
    exact ⟨_, hm, by rw [hdiv]; simp⟩
  · intro P hP P' hP' hd
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hP'
    have hqq : q = q' := by
      rw [← hout q, ← hout q', mk_eq_iff]
      exact ⟨_, hd, by rw [mul_sub, hdiv, hdiv]⟩
    rw [hqq]
  · intro z hz hzn
    have hq0 : (Submodule.Quotient.mk (⟨α * z, hz⟩ : L.lattice) :
        L.lattice ⧸ LinearMap.range (mulEnd L α h)) ≠ 0 := by
      intro h0
      rw [← Submodule.Quotient.mk_zero, mk_eq_iff] at h0
      obtain ⟨x, hx, hxe⟩ := h0
      have hzx : z = x := by simpa [hα] using hxe
      exact hzn (hzx ▸ hx)
    set q : L.lattice ⧸ LinearMap.range (mulEnd L α h) := Submodule.Quotient.mk (⟨α * z, hz⟩ : L.lattice) with hqdef
    refine ⟨((Quotient.out q : L.lattice) : ℂ) / α, Finset.mem_image.2 ⟨q, by simp [hq0], rfl⟩, ?_⟩
    have h5 := hout q
    rw [hqdef, mk_eq_iff] at h5
    obtain ⟨x, hx, hxe⟩ := h5
    have hxe' : ((Quotient.out q : L.lattice) : ℂ) - α * z = α * x := hxe
    have hzx : z - ((Quotient.out q : L.lattice) : ℂ) / α = -x :=
      mul_left_cancel₀ hα (by rw [mul_sub, hdiv]; linear_combination -hxe')
    rw [hzx]
    exact neg_mem hx

end Formalism.L2.Th1.F
