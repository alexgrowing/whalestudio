import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem exists_separable_aeval_eq_zero_ringOfIntegers {F : Type} [Field F] [NumberField F] {R : Type} [Ring R] [Algebra ℂ R]
    (f : 𝓞 F →+* R) (c : 𝓞 F) : ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hint : IsIntegral ℤ (c : F) := RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (Int.castRingHom ℂ), ?_, ?_⟩
  · have hq : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have hsep : (minpoly ℚ (c : F)).Separable := Algebra.IsSeparable.isSeparable ℚ (c : F)
    have hm := hsep.map (f := algebraMap ℚ ℂ)
    rw [hq, Polynomial.map_map, RingOfIntegers.minpoly_coe] at hm
    have e : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [e] at hm
    exact hm
  · rw [aeval_def, eval₂_map]
    have e : (algebraMap ℂ R).comp (Int.castRingHom ℂ) = f.comp (algebraMap ℤ (𝓞 F)) :=
      RingHom.ext_int _ _
    rw [e, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

private theorem exists_integral_bezout_of_separable {F : Type} [Field F] [NumberField F] (χ : F[X]) (hs : χ.Separable) :
    ∃ (q u v : (𝓞 F)[X]) (y : ℤ), y ≠ 0 ∧ χ ∣ q.map (algebraMap (𝓞 F) F) ∧
      u * q + v * derivative q = C ((y : 𝓞 F) ^ 2) := by
  classical
  obtain ⟨a, b, hab⟩ := (separable_def' χ).1 hs
  let s : Finset F := (χ.support.image χ.coeff ∪ a.support.image a.coeff) ∪ b.support.image b.coeff
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ s
  have hlift : ∀ P : F[X], (∀ n, P.coeff n ≠ 0 → P.coeff n ∈ s) →
      ∃ Q : (𝓞 F)[X], Q.map (algebraMap (𝓞 F) F) = C (y : F) * P := by
    intro P hP
    have hl : C (y : F) * P ∈ Polynomial.lifts (algebraMap (𝓞 F) F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_C_mul]
      by_cases h0 : P.coeff n = 0
      · rw [h0, mul_zero]; exact ⟨0, map_zero _⟩
      · have hi := hy _ (hP n h0)
        rw [zsmul_eq_mul] at hi
        obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hi
        exact ⟨z, hz⟩
    exact hl
  have hs1 : ∀ n, χ.coeff n ≠ 0 → χ.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inl (Or.inl ⟨n, h, rfl⟩)
  have hs2 : ∀ n, a.coeff n ≠ 0 → a.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inl (Or.inr ⟨n, h, rfl⟩)
  have hs3 : ∀ n, b.coeff n ≠ 0 → b.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inr ⟨n, h, rfl⟩
  obtain ⟨q, hq⟩ := hlift χ hs1
  obtain ⟨u, hu⟩ := hlift a hs2
  obtain ⟨v, hv⟩ := hlift b hs3
  refine ⟨q, u, v, y, hy0, ?_, ?_⟩
  · rw [hq]; exact dvd_mul_left _ _
  · apply Polynomial.map_injective (algebraMap (𝓞 F) F) RingOfIntegers.coe_injective
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      hq, hu, hv, Polynomial.map_C, Polynomial.derivative_C_mul, map_pow, map_intCast, C_pow]
    simp only [map_intCast, C_eq_intCast]
    linear_combination ((y : F[X])) ^ 2 * hab

private theorem isSemisimple_of_commute_of_integral_bezout {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : R →+* Module.End ℂ V) (hf : ∀ c, (f c).IsSemisimple)
    (h : Module.End ℂ V) (hc : ∀ c, Commute (f c) h) (q u v : R[X]) (y : ℤ) (hy : y ≠ 0)
    (hq : q.eval₂ f h = 0) (huv : u * q + v * derivative q = C ((y : R) ^ 2)) : h.IsSemisimple := by
  classical
  let S : Set (Module.End ℂ V) := Set.range f ∪ {h}
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (⟨c, rfl⟩ | ha) b (⟨c', rfl⟩ | hb)
    · rw [← map_mul, ← map_mul, mul_comm]
    · rw [Set.mem_singleton_iff.1 hb]; exact hc c
    · rw [Set.mem_singleton_iff.1 ha]; exact (hc c').symm
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  let A := Algebra.adjoin ℂ S
  letI : CommRing A := Algebra.adjoinCommRingOfComm ℂ hS
  have hfA : ∀ c, f c ∈ A := fun c => Algebra.subset_adjoin (Or.inl ⟨c, rfl⟩)
  have hhA : h ∈ A := Algebra.subset_adjoin (Or.inr rfl)
  let fA : R →+* A := f.codRestrict A hfA
  letI : Algebra R A := fA.toAlgebra
  obtain ⟨n, hn, s, hs, hnil, hss, hns⟩ := Module.End.exists_isNilpotent_isSemisimple (f := h)
  have hsub : Algebra.adjoin ℂ {h} ≤ A := Algebra.adjoin_mono Set.subset_union_right
  let x : A := ⟨h, hhA⟩
  let r : A := ⟨s, hsub hs⟩
  have hev : ∀ (z : A) (p : R[X]), ((aeval z p : A) : Module.End ℂ V) = p.eval₂ f (z : Module.End ℂ V) := by
    intro z p
    rw [aeval_def]
    exact Polynomial.hom_eval₂ p (algebraMap R A) (A.val : A →+* Module.End ℂ V) z
  have hx0 : aeval x q = 0 := Subtype.ext (by rw [hev]; exact hq)
  have hunit : IsUnit (aeval x (derivative q)) := by
    have e := congrArg (aeval x) huv
    rw [map_add, map_mul, map_mul, hx0, mul_zero, zero_add, aeval_C] at e
    have hu : IsUnit (algebraMap R A ((y : R) ^ 2)) := by
      rw [map_pow, map_intCast, ← map_intCast (algebraMap ℂ A)]
      exact (IsUnit.map _ (isUnit_iff_ne_zero.2 (by exact_mod_cast hy))).pow 2
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_right hu
  obtain ⟨r0, -, huniq⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero
    (by rw [hx0]; exact IsNilpotent.zero) hunit
  have hxr : IsNilpotent (x - r) := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, Subtype.ext ?_⟩
    have e1 : ((x - r : A) : Module.End ℂ V) = n := by
      show h - s = n
      rw [hns]; abel
    rw [SubmonoidClass.coe_pow, e1, hk]
    rfl
  have hsc : ∀ c, Commute (f c) s := fun c =>
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs (hc c)
  have hcomA : ∀ a b : A, Commute (a : Module.End ℂ V) b := fun a b =>
    congrArg Subtype.val (mul_comm a b)
  have hssq : ∀ p : R[X], (p.eval₂ f s).IsSemisimple := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' =>
      rw [eval₂_add]
      have e1 := hev r p
      have e2 := hev r p'
      refine Module.End.IsSemisimple.add_of_commute ?_ hp hp'
      rw [← e1, ← e2]
      exact hcomA _ _
    | monomial k c =>
      rw [eval₂_monomial]
      exact Module.End.IsSemisimple.mul_of_commute ((hsc c).pow_right k) (hf c) (hss.pow k)
  have hr0 : aeval r q = 0 := by
    have hnil2 := isNilpotent_aeval_sub_of_isNilpotent_sub q hxr
    rw [hx0, zero_sub, isNilpotent_neg_iff] at hnil2
    apply Subtype.ext
    have hnilE : IsNilpotent (q.eval₂ f s) := by
      rw [← hev r q]
      exact hnil2.map (A.val : A →+* Module.End ℂ V)
    rw [hev r q, Module.End.eq_zero_of_isNilpotent_isSemisimple hnilE (hssq q)]
    rfl
  have hxr' : x = r := (huniq x ⟨by simp, hx0⟩).trans (huniq r ⟨hxr, hr0⟩).symm
  have hhs : h = s := congrArg Subtype.val hxr'
  rw [hhs]
  exact hss

theorem UpperTheory.Gal.W2.hSep_of :
    UpperTheory.Gal.W2.HSep := by
  intro F _ _ O _ bar g ρ a H hcomm χ hmon hsep hkill
  obtain ⟨q, u, v, y, hy, hdvd, huv⟩ := exists_integral_bezout_of_separable χ hsep
  let e := Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)
  let f : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (e : Matrix (Fin g) (Fin g) ℂ →+* _).comp (ρ.comp a)
  have hf : ∀ c, (f c).IsSemisimple := by
    intro c
    obtain ⟨p, hp, hpa⟩ := exists_separable_aeval_eq_zero_ringOfIntegers f c
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree hpa
  have hc : ∀ c, Commute (f c) (e H) := fun c => by
    show e (ρ (a c)) * e H = e H * e (ρ (a c))
    rw [← map_mul, ← map_mul, hcomm c]
  have hq : q.eval₂ f (e H) = 0 := by
    have hk := hkill q hdvd
    rw [eval₂_eq_sum]
    have e2 : (q.sum fun i b => f b * (e H) ^ i) = e (q.sum fun i b => ρ (a b) * H ^ i) := by
      simp only [Polynomial.sum, map_sum, map_mul, map_pow]
      rfl
    rw [e2, hk, map_zero]
  have hss := isSemisimple_of_commute_of_integral_bezout f hf (e H) hc q u v y hy hq huv
  refine ⟨minpoly ℂ H, ?_, minpoly.aeval ℂ H⟩
  rw [← minpoly.algEquiv_eq e H]
  exact PerfectField.separable_iff_squarefree.mpr hss.minpoly_squarefree
