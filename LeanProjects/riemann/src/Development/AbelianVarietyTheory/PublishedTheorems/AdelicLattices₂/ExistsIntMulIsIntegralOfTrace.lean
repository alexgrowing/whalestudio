import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsShortOfTraceDet

namespace GlobalTheory.HermClass

open Module Submodule NumberField

theorem exists_finite_residues {V : Type} [AddCommGroup V] (L : Submodule ℤ V) (hL : L.FG)
    {m : ℤ} (hm : m ≠ 0) :
    ∃ R : Set V, R.Finite ∧ (∀ ρ ∈ R, ρ ∈ L) ∧ ∀ x ∈ L, ∃ ρ ∈ R, ∃ y ∈ L, x = ρ + m • y := by
  have : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL
  let P : Submodule ℤ L := LinearMap.range (m • LinearMap.id)
  have : Finite (L ⧸ P) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    change m • P.mkQ x = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  choose s hs using P.mkQ_surjective
  refine ⟨Set.range fun q => (s q : V), Set.finite_range _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨q, rfl⟩; exact (s q).2
  · have h := hs (P.mkQ ⟨x, hx⟩)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq] at h
    obtain ⟨y, hy⟩ := h
    refine ⟨_, ⟨P.mkQ ⟨x, hx⟩, rfl⟩, y, y.2, ?_⟩
    have := congrArg Subtype.val hy
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul_of_tower,
      Submodule.coe_sub] at this
    rw [this]; simp

section NumberField

variable (E : Type) [Field E] [NumberField E]

theorem exists_int_mul_isIntegral {S : Set E} (hS : S.Finite) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ a ∈ S, IsIntegral ℤ ((M : E) * a) := by
  obtain ⟨M, hM, h⟩ := exists_integral_multiples ℤ ℚ hS.toFinset
  exact ⟨M, hM, fun a ha => by simpa using h a (by simpa using ha)⟩

theorem exists_int_mul_isIntegral_of_trace :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ a : E, (∀ t : E, IsIntegral ℤ t → ∃ m : ℤ, Algebra.trace ℚ E (a * t) = m) →
      IsIntegral ℤ ((D : E) * a) := by
  classical
  obtain ⟨D, hD, h⟩ := exists_int_mul_isIntegral E (Set.finite_range (integralBasis E).traceDual)
  refine ⟨D, hD, fun a ha => ?_⟩
  rw [← (integralBasis E).traceDual.sum_repr a, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨m, hm⟩ := ha (integralBasis E i) (by
    rw [integralBasis_apply]; exact (RingOfIntegers.basis E i).isIntegral_coe)
  rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply, hm, mul_smul_comm, Int.cast_smul_eq_zsmul]
  exact (h _ ⟨i, rfl⟩).smul m

theorem exists_int_mul_mem_span :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ J : Ideal (𝓞 E), J ≠ ⊥ →
      ∃ j ∈ J, j ≠ 0 ∧ ∀ a ∈ J, j ∣ (M : 𝓞 E) * a := by
  classical
  choose I hI using ClassGroup.mk0_surjective (R := 𝓞 E)
  refine ⟨∏ C, (Ideal.absNorm (I C : Ideal (𝓞 E)) : ℤ), Finset.prod_ne_zero_iff.2 fun C _ => ?_,
    fun J hJ => ?_⟩
  · exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors (I C)
  · let J' : nonZeroDivisors (Ideal (𝓞 E)) := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
    obtain ⟨j, hj0, hj⟩ := ClassGroup.mk0_eq_mk0_inv_iff.1 (hI (ClassGroup.mk0 J')⁻¹)
    refine ⟨j, ?_, hj0, fun a ha => ?_⟩
    · have hjm : j ∈ (I (ClassGroup.mk0 J')⁻¹ : Ideal (𝓞 E)) * J := by
        rw [hj]; exact Ideal.mem_span_singleton_self j
      exact (Ideal.mul_le_inf hjm).2
    · have hj' : (I (ClassGroup.mk0 J')⁻¹ : Ideal (𝓞 E)) * J = Ideal.span {j} := hj
      rw [← Ideal.mem_span_singleton, ← hj']
      refine Ideal.mul_mem_mul ?_ ha
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (ClassGroup.mk0 J')⁻¹), Int.cast_mul]
      refine Ideal.mul_mem_right _ _ ?_
      simpa using Ideal.absNorm_mem _

theorem fg_integers : (Subalgebra.toSubmodule (integralClosure ℤ E)).FG :=
  Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite ℤ (𝓞 E)))

end NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIntegral_star {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (star a) :=
  ha.map (starRingEnd E).toIntAlgHom

theorem trace_star (a : E) : Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem exists_bound_short (n : ℕ) (hn : n ≠ 0) {N : ℤ} (hN : N ≠ 0) :
    ∃ C : ℝ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v ∈ Λ, v ≠ 0 ∧ ∀ φ : E →+* ℂ, ‖φ (h v v)‖ ≤ C := by
  classical
  obtain ⟨D, hD, hDa⟩ := exists_int_mul_isIntegral_of_trace E
  set F := maximalRealSubfield E with hF
  have hM0 : N * D * 2 ≠ 0 := by positivity
  refine ⟨(2 * n : ℕ) * (|((N * D * 2 : ℤ) : ℝ)| + 1) ^ 2, ?_⟩
  intro V _ _ _ h Λ hV hs hfg hsp hO hdual
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_compHom ℚ E V
  have : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 hfg
  have : IsAddTorsionFree V := .of_module_rat V
  have : Module.Free ℤ Λ := inferInstance
  let β := Module.Free.chooseBasis ℤ Λ
  let κ := Module.Free.ChooseBasisIndex ℤ Λ
  let b : κ → V := fun i => β i
  have hbZ : LinearIndependent ℤ b := β.linearIndependent.map' Λ.subtype (ker_subtype Λ)
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hbZ
  have hbΛ : ∀ x ∈ Λ, ∃ c : κ → ℤ, x = ∑ i, c i • b i := fun x hx =>
    ⟨β.repr ⟨x, hx⟩, by
      have := congrArg Λ.subtype (β.sum_repr ⟨x, hx⟩)
      rw [map_sum] at this
      exact this.symm⟩
  have hbs : ⊤ ≤ span ℚ (Set.range b) := by
    have hΛ : ∀ x ∈ Λ, x ∈ span ℚ (Set.range b) := fun x hx => by
      obtain ⟨c, rfl⟩ := hbΛ x hx
      exact sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _
    have key : ∀ x ∈ span E (Λ : Set V), ∀ a : E, a • x ∈ span ℚ (Set.range b) := by
      intro x hx
      induction hx using span_induction with
      | mem x hx =>
        intro a
        obtain ⟨M, hM, hMa⟩ := exists_int_mul_isIntegral E (Set.finite_singleton a)
        have h1 := smul_mem _ (M : ℚ)⁻¹ (hΛ _ (hO _ (hMa a rfl) x hx))
        rw [← smul_assoc, ← smul_mul_assoc, Algebra.smul_def] at h1
        have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
        simpa [hM'] using h1
      | zero => intro a; simp
      | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
      | smul c x _ hx => intro a; rw [smul_smul]; exact hx _
    intro x _
    simpa using key x (hsp ▸ mem_top) 1
  have hFV : finrank F V = 2 * n := by
    rw [← finrank_mul_finrank F E V, hV, Algebra.IsQuadraticExtension.finrank_eq_two]
  have : FiniteDimensional F V := Module.Finite.trans E V
  have hκ : Fintype.card κ = finrank ℚ F * finrank F V := by
    rw [← finrank_eq_card_basis (Basis.mk hbQ hbs), ← finrank_mul_finrank ℚ E V,
      ← finrank_mul_finrank F E V, ← finrank_mul_finrank ℚ F E, mul_assoc]
  have hreal : ∀ x y, h x y + h y x ∈ F := fun x y => by
    rw [← IsCMField.complexConj_eq_self_iff]
    change star _ = _
    rw [star_add, ← hs, ← hs, add_comm]
  have hstF : ∀ c : F, starRingEnd E (c : E) = c := fun c => IsCMField.complexConj_apply_eq_self E c
  let q : LinearMap.BilinForm F V := LinearMap.mk₂ F (fun x y => ⟨h x y + h y x, hreal x y⟩)
    (fun x x' y => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
    (fun x y y' => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
  have hq : ∀ x y, (q x y : E) = h x y + h y x := fun _ _ => rfl
  have hqs : LinearMap.IsSymm q := ⟨fun x y => Subtype.ext (by simp [hq, add_comm])⟩
  have htr : ∀ x y, Algebra.trace ℚ F (q x y) = Algebra.trace ℚ E (h x y) := fun x y => by
    have h1 := Algebra.trace_trace (R := ℚ) (S := F) (T := E) (algebraMap F E (q x y))
    rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, map_nsmul] at h1
    have h2 : algebraMap F E (q x y) = h x y + star (h x y) := by rw [← hs]; rfl
    rw [h2, map_add, trace_star, two_nsmul] at h1
    linarith
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  obtain ⟨hT0, hT1⟩ := det_ne_zero_and_abs_le T hM0 (by
    intro x hx i
    set y : V := ∑ i, x i • b i with hy
    have h1 : ∀ j, ∃ m : ℤ, Algebra.trace ℚ E (h y (b j)) = m := fun j => by
      obtain ⟨m, hm⟩ := hx j
      refine ⟨m, ?_⟩
      rw [← hm, hy, map_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul, map_smul, ← htr]
      rfl
    have h2 : ∀ w ∈ Λ, ∃ m : ℤ, Algebra.trace ℚ E (h y w) = m := fun w hw => by
      obtain ⟨c, rfl⟩ := hbΛ w hw
      choose m hm using h1
      refine ⟨∑ j, c j * m j, ?_⟩
      rw [map_sum, map_sum, Int.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, map_zsmul, hm, zsmul_eq_mul, Int.cast_mul]
    have h3 : (N : E) • (D : E) • y ∈ Λ := hdual _ fun w hw => by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      refine hDa _ fun t ht => ?_
      obtain ⟨m, hm⟩ := h2 _ (hO _ (isIntegral_star ht) w hw)
      exact ⟨m, by rw [← hm, map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]⟩
    obtain ⟨c, hc⟩ := hbΛ _ h3
    have h4 : ∑ i, ((N : ℚ) * D * x i - c i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul, ← hc, mul_smul,
        ← Finset.smul_sum, ← hy, sub_self]
    have h5 := Fintype.linearIndependent_iff.1 hbQ _ h4 i
    exact ⟨2 * c i, by push_cast; linarith⟩)
  have hcard : Fintype.card κ ≠ 0 := by
    rw [hκ, hFV]; exact mul_ne_zero finrank_pos.ne' (by omega)
  set M : ℝ := |((N * D * 2 : ℤ) : ℝ)| with hM
  have hM' : 0 ≤ M := abs_nonneg _
  obtain ⟨z, hz0, hz⟩ := exists_short_of_trace_det q hqs b hκ (t := M + 1) (by positivity) hT0 (by
    have h1 : |((T.det : ℚ) : ℝ)| ≤ M ^ Fintype.card κ := by rw [hM]; exact_mod_cast hT1
    have h2 : M ^ Fintype.card κ < (M + 1) ^ Fintype.card κ :=
      pow_lt_pow_left₀ (by linarith) hM' hcard
    have h3 : 1 ≤ (M + 1) ^ Fintype.card κ := one_le_pow₀ (by linarith)
    refine h1.trans_lt (h2.trans_le ?_)
    nlinarith)
  refine ⟨∑ i, z i • b i, sum_mem fun i _ => Λ.smul_mem _ (β i).2, fun h0 => hz0 ?_, fun φ => ?_⟩
  · exact funext (Fintype.linearIndependent_iff.1 hbZ z h0)
  · have h1 := hz (φ.comp (algebraMap F E))
    rw [hFV] at h1
    refine le_trans ?_ h1
    change _ ≤ ‖φ (h _ _ + h _ _)‖
    rw [← two_mul, map_mul, norm_mul, map_ofNat, Complex.norm_ofNat]
    linarith [norm_nonneg (φ (h (∑ i, z i • b i) (∑ i, z i • b i)))]

end GlobalTheory.HermClass
