import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

namespace GlobalTheory.UCls.NormOne

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem sg_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
  simp [sg]

omit [NumberField E] in
theorem sg_sg (c : E ≃ₐ[F] E) (hcc : ∀ x, c (c x) = x) (z : RA F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (sg (FiniteAdeleRing (𝓞 F) F) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [sg_tmul, sg_tmul, hcc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [NumberField E] in

theorem finiteAdele_quadratic_exists_unit_eq_mul_sg (c : E ≃ₐ[F] E) (hcc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → ∃ t : F, x = algebraMap F E t) (hc : c ≠ 1) (u : RA F E)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x : (RA F E)ˣ, (x : RA F E) = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  have hT : ∀ z : RA F E, ∃ t : FiniteAdeleRing (𝓞 F) F,
      z + sg (FiniteAdeleRing (𝓞 F) F) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := hfix (x + c x) (by rw [map_add, hcc, add_comm])
      refine ⟨t • a, ?_⟩
      rw [sg_tmul, ← TensorProduct.tmul_add, ht, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  obtain ⟨t, ht⟩ := hT u
  obtain ⟨e, he, hun⟩ := GlobalTheory.AdIdem.finite_part (𝓞 F) F ((2 : F)⁻¹ • t)
  let ι : FiniteAdeleRing (𝓞 F) F →+* RA F E := Algebra.TensorProduct.includeLeftRingHom
  have hι : ∀ a, ι a = a ⊗ₜ 1 := fun a => rfl
  let κ : E →ₐ[F] RA F E := Algebra.TensorProduct.includeRight
  have hκ : ∀ a, κ a = 1 ⊗ₜ a := fun a => rfl
  have h2 : IsUnit (2 : RA F E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (RA F E))
    rwa [map_ofNat] at this
  refine hilbert90_involution_of_idempotent_unit (sg (FiniteAdeleRing (𝓞 F) F) c : _ →+* _) (sg_sg c hcc) u (κ (y - c y)) (ι e)
    (ι ((2 : F)⁻¹ • t)) hu ?_ ?_ h2 ?_ ?_ ?_ ?_
  · change sg _ c _ = _
    rw [← map_neg, hκ, hκ, sg_tmul, map_sub, hcc, neg_sub]
  · exact (IsUnit.mk0 _ (sub_ne_zero.2 hy.symm)).map κ
  · rw [← map_mul, he]
  · change sg _ c _ = _
    rw [hι, sg_tmul, map_one]
  · change u + sg _ c u = _
    rw [ht, two_mul, ← map_add, ← add_smul, hι]
    norm_num
  · have := hun.map ι
    simpa only [map_add, map_mul, map_sub, map_one] using this

omit [NumberField E] in
theorem one_tmul_natCast (d : ℕ) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (d : E) : RA F E) = d :=
  map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) d

omit [NumberField E] in
theorem one_tmul_mul (x y : E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x * y) : RA F E) = 1 ⊗ₜ[F] x * 1 ⊗ₜ[F] y := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem exists_nat_mul_mem (z : RA F E) :
    ∃ d : ℕ, 0 < d ∧ (d : RA F E) * z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  obtain ⟨x, h, hh, rfl⟩ := GlobalTheory.AdIdem.exists_eq_one_tmul_add F E z
  obtain ⟨d, hd, hx⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E x
  refine ⟨d, hd, ?_⟩
  rw [mul_add]
  refine add_mem ?_ ?_
  · rw [← one_tmul_natCast, ← one_tmul_mul]
    exact one_tmul_mem_adelicCompletionOfElementSet F hx
  · rw [← nsmul_eq_mul]; exact nsmul_mem hh d

theorem exists_ideal (z w : RA F E) (hzw : z * w = 1)
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ I : (Ideal (𝓞 E))⁰, (∀ x ∈ (I : Ideal (𝓞 E)), w * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) ∈
        hat1 F (Set.range (algebraMap (𝓞 E) E))) ∧
      ∃ x ∈ (I : Ideal (𝓞 E)), ∃ e ∈ (I : Ideal (𝓞 E)), ∃ h ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
        z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) +
          (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e : E) * h := by
  let I : Ideal (𝓞 E) :=
    { carrier := {x | w * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) ∈
        hat1 F (Set.range (algebraMap (𝓞 E) E))}
      add_mem' := by
        intro x y hx hy
        change w * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((x : E) + (y : E)) ∈
          hat1 F (Set.range (algebraMap (𝓞 E) E))
        rw [TensorProduct.tmul_add, mul_add]
        exact add_mem hx hy
      zero_mem' := by
        change w * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (0 : E) ∈
          hat1 F (Set.range (algebraMap (𝓞 E) E))
        rw [TensorProduct.tmul_zero, mul_zero]
        exact zero_mem _
      smul_mem' := by
        intro a x hx
        change w * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((a : E) * (x : E)) ∈
          hat1 F (Set.range (algebraMap (𝓞 E) E))
        rw [one_tmul_mul, mul_left_comm]
        exact GlobalTheory.AdIdem.mul_mem_hat F E (one_tmul_mem_adelicCompletionOfElementSet F ⟨a, rfl⟩) hx }
  obtain ⟨e, he, hew⟩ := exists_nat_mul_mem w
  have he' : (e : E) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  have heE : (((e : 𝓞 E)) : E) = e := map_natCast (algebraMap (𝓞 E) E) e
  have heI : (e : 𝓞 E) ∈ I := by
    change w * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((e : 𝓞 E)) : E) ∈
          hat1 F (Set.range (algebraMap (𝓞 E) E))
    rw [heE, one_tmul_natCast, mul_comm]
    exact hew
  have hI : I ∈ (Ideal (𝓞 E))⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    rw [h0] at heI
    exact (Nat.cast_ne_zero.2 he.ne') (Ideal.mem_bot.1 heI)
  obtain ⟨y, h, hh, hy⟩ := GlobalTheory.AdIdem.exists_eq_one_tmul_add F E
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e : E)⁻¹ * z)
  have hz' : z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((e : E) * y) + (e : RA F E) * h := by
    rw [one_tmul_mul, one_tmul_natCast, ← mul_add, ← hy, ← one_tmul_natCast, ← mul_assoc,
      ← one_tmul_mul, mul_inv_cancel₀ he', ← Algebra.TensorProduct.one_def, one_mul]
  have hint : (e : E) * y ∈ Set.range (algebraMap (𝓞 E) E) := by
    apply GlobalTheory.AdIdem.mem_range_of_one_tmul_mem F E
    rw [eq_sub_of_add_eq hz'.symm, ← nsmul_eq_mul]
    exact sub_mem hz (nsmul_mem hh e)
  obtain ⟨x, hx⟩ := hint
  have hx' : (x : E) = (e : E) * y := hx
  refine ⟨⟨I, hI⟩, fun x hx => hx, x, ?_, e, heI, h, hh, ?_⟩
  · change w * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) ∈
          hat1 F (Set.range (algebraMap (𝓞 E) E))
    rw [hx', eq_sub_of_add_eq hz'.symm, mul_sub, mul_comm w z, hzw, ← mul_assoc, mul_comm w]
    exact sub_mem (one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩) (GlobalTheory.AdIdem.mul_mem_hat F E hew hh)
  · rw [hx', heE, one_tmul_natCast]
    exact hz'

omit [NumberField E] in

theorem exists_quot {z w' : RA F E} {I I' : Ideal (𝓞 E)} {a b : 𝓞 E}
    (hab : Ideal.span {a} * I ≤ Ideal.span {b} * I')
    (hz : ∃ x ∈ I, ∃ e ∈ I, ∃ h ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
        z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) +
          (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e : E) * h)
    (hw : ∀ x ∈ I', w' * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) ∈
        hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ k ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (a : E) * z * w' =
        (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) * k := by
  obtain ⟨x, hx, e, he, h, hh, rfl⟩ := hz
  have key : ∀ x ∈ I, ∃ x' ∈ I', ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (a : E) : RA F E) * 1 ⊗ₜ[F] (x : E)
      = 1 ⊗ₜ[F] (b : E) * 1 ⊗ₜ[F] (x' : E) := by
    intro x hx
    obtain ⟨x', hx', e⟩ := Ideal.mem_span_singleton_mul.1
      (hab (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self a) hx))
    refine ⟨x', hx', ?_⟩
    rw [← one_tmul_mul, ← one_tmul_mul]
    congr 1
    exact_mod_cast e.symm
  obtain ⟨x', hx', ex⟩ := key x hx
  obtain ⟨e', he', ee⟩ := key e he
  refine ⟨_, add_mem (hw x' hx') (GlobalTheory.AdIdem.mul_mem_hat F E (hw e' he') hh), ?_⟩
  linear_combination w' * ex + w' * h * ee

theorem exists_class (c : E ≃ₐ[F] E) (hcc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → ∃ t : F, x = algebraMap F E t) (hc : c ≠ 1) :
    ∃ f : {t : RA F E // IsTA c t} → ClassGroup (𝓞 E), ∀ t s, f t = f s →
      ∃ u : E, u * c u = 1 ∧ ∃ k : RA F E, IsTA c k ∧ k ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) ∧
        t.1 = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ u) * s.1 * k := by
  classical
  have h90 : ∀ t : {t : RA F E // IsTA c t}, ∃ z w : RA F E, z * w = 1 ∧
      z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) ∧
      t.1 = z * sg (FiniteAdeleRing (𝓞 F) F) c w := by
    intro t
    obtain ⟨x, hx⟩ := finiteAdele_quadratic_exists_unit_eq_mul_sg c hcc hfix hc t.1 t.2
    obtain ⟨d, hd, hdx⟩ := exists_nat_mul_mem (x : RA F E)
    have hdu : IsUnit (d : RA F E) := by
      have := (IsUnit.mk0 (d : F) (Nat.cast_ne_zero.2 hd.ne')).map (algebraMap F (RA F E))
      rwa [map_natCast] at this
    obtain ⟨w, hw⟩ := (hdu.mul x.isUnit).exists_right_inv
    refine ⟨_, w, hw, hdx, ?_⟩
    have h1 := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) hw
    rw [map_mul, map_mul, map_natCast, map_one] at h1
    linear_combination (-t.1) * h1 - d * sg (FiniteAdeleRing (𝓞 F) F) c w * hx
  choose z w hzw hz ht using h90
  choose I hI hI' using fun t => exists_ideal (z t) (w t) (hzw t) (hz t)
  refine ⟨fun t => ClassGroup.mk0 (I t), fun t s hts => ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.1 hts
  obtain ⟨k, hk, ek⟩ := exists_quot hab.le (hI' t) (hI s)
  obtain ⟨k', hk', ek'⟩ := exists_quot hab.ge (hI' s) (hI t)
  have ha' : (a : E) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : E) ≠ 0 := by exact_mod_cast hb
  let κ : E →ₐ[F] RA F E := Algebra.TensorProduct.includeRight
  have hκ : ∀ a, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ a = κ a := fun a => rfl
  have hσκ : ∀ a, sg (FiniteAdeleRing (𝓞 F) F) c (κ a) = κ (c a) := fun a => sg_tmul c 1 a
  simp only [hκ] at ek ek' ⊢
  have hA : κ a * κ (a : E)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha', map_one]
  have hB : κ b * κ (b : E)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hb', map_one]
  have e1 : z t = κ ((b : E) * (a : E)⁻¹) * z s * k := by
    rw [map_mul]
    linear_combination κ (a : E)⁻¹ * z s * ek - z t * hzw s - z t * z s * w s * hA
  have e2 : w t = κ ((a : E) * (b : E)⁻¹) * w s * k' := by
    rw [map_mul]
    linear_combination κ (b : E)⁻¹ * w s * ek' - w t * hzw s - w t * z s * w s * hB
  have e3 : k * k' = 1 := by
    have := hzw t
    rw [e1, e2, map_mul, map_mul] at this
    linear_combination this - (κ a * κ (a : E)⁻¹ * κ b * κ (b : E)⁻¹ * k * k') * hzw s
      - (κ b * κ (b : E)⁻¹ * k * k') * hA - k * k' * hB
  refine ⟨(b : E) * (a : E)⁻¹ * c ((a : E) * (b : E)⁻¹), ?_,
    k * sg (FiniteAdeleRing (𝓞 F) F) c k', ?_, ?_, ?_⟩
  · have : c (a : E) ≠ 0 := (map_ne_zero c).2 ha'
    have : c (b : E) ≠ 0 := (map_ne_zero c).2 hb'
    simp only [map_mul, map_inv₀, hcc]
    field_simp
  · have e4 := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) e3
    rw [map_mul, map_one] at e4
    unfold IsTA
    rw [map_mul, sg_sg c hcc]
    linear_combination (k * k') * e4 + e3
  · refine GlobalTheory.AdIdem.mul_mem_hat F E hk (galoisAut_mem_adelicCompletionOfElementSet F c ?_ hk')
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨c y, (RingOfIntegers.isIntegral_coe y).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩
  · rw [ht t, ht s, e1, e2, map_mul (sg _ c), map_mul (sg _ c), hσκ, map_mul κ _ (c _)]
    ring

end GlobalTheory.UCls.NormOne

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

theorem GlobalTheory.UCls.normOne_classes_le_classNumber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∃ S : Finset (RA (maximalRealSubfield E) E), S.card ≤ classNumber E ∧ ∀ t : RA (maximalRealSubfield E) E, IsTA (IsCMField.complexConj E) t → ∃ s ∈ S, ∃ u : E, u * cc u = 1 ∧ ∃ k : RA (maximalRealSubfield E) E, IsTA (IsCMField.complexConj E) k ∧ k ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x} ∧ IsTA (IsCMField.complexConj E) s ∧ t = ((1 : IsDedekindDomain.FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u) * s * k := by
  intro E _ _ _ _
  classical
  obtain ⟨f, hf⟩ := GlobalTheory.UCls.NormOne.exists_class (IsCMField.complexConj E)
    (IsCMField.complexConj_apply_apply E)
    (fun x hx => ⟨⟨x, (IsCMField.complexConj_eq_self_iff E x).1 hx⟩, rfl⟩)
    (IsCMField.complexConj_ne_one E)
  have hset : {x : E | IsIntegral ℤ x} = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y⟩
  haveI : Nonempty {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} :=
    ⟨⟨1, by simp [IsTA]⟩⟩
  refine ⟨Finset.univ.image fun x => (Function.invFun f x).1, Finset.card_image_le, fun t ht => ?_⟩
  obtain ⟨u, hu, k, hk, hk', e⟩ := hf ⟨t, ht⟩ (Function.invFun f (f ⟨t, ht⟩))
    (Function.invFun_eq ⟨_, rfl⟩).symm
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (f ⟨t, ht⟩)), u, hu, k, hk, hset ▸ hk',
    (Function.invFun f (f ⟨t, ht⟩)).2, e⟩
