import Mathlib
import Formalism.GL3MeanSquares.AffineFibreCountComparison

namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums

open Module Finset Matrix

section IdxDet

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem lenQuotSpan (ϖ : R) (hϖ : Irreducible ϖ) (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = emultiplicity ϖ a := by
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 : Ideal.span ({(w : R) * ϖ ^ k} : Set R) = IsLocalRing.maximalIdeal R ^ k := by
    rw [Ideal.span_singleton_mul_left_unit w.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [h1, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
    emultiplicity_eq_of_associated_right (associated_unit_mul_left (ϖ ^ k) (w : R) w.isUnit),
    emultiplicity_pow_self_of_prime hϖ.prime]

theorem mulVecLin_inj {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n R) (hu : u.det ≠ 0) :
    Function.Injective u.mulVecLin := by
  intro x y hxy
  simp only [Matrix.mulVecLin_apply] at hxy
  have h2 : u.adjugate *ᵥ (u *ᵥ x) = u.adjugate *ᵥ (u *ᵥ y) := by rw [hxy]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  exact smul_right_injective _ hu h2

theorem endo_inj {n : Type} [Fintype n] [DecidableEq n] (P : (n → R) →ₗ[R] (n → R))
    (hP : LinearMap.det P ≠ 0) : Function.Injective P := by
  have h := mulVecLin_inj (LinearMap.toMatrix' P) (by rwa [LinearMap.det_toMatrix'])
  rwa [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix'] at h

theorem index_det (ϖ : R) (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n]
    (u : Matrix n n R) (hu : u.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range u.mulVecLin) = emultiplicity ϖ u.det := by
  set L := u.mulVecLin with hL
  have hinj : Function.Injective L := mulVecLin_inj u hu
  have h : Module.finrank R (LinearMap.range L) = Module.finrank R (n → R) :=
    LinearMap.finrank_range_of_inj hinj
  let b := Pi.basisFun R n
  rw [(Submodule.quotientEquivPiSpan (LinearMap.range L) b h).length_eq,
    Module.length_pi_of_fintype]
  rw [Finset.sum_congr rfl (fun i _ => lenQuotSpan ϖ hϖ _ (Submodule.smithNormalFormCoeffs_ne_zero b h i)),
    ← Finset.emultiplicity_prod hϖ.prime]
  set a := Submodule.smithNormalFormCoeffs b h
  set b' := Submodule.smithNormalFormTopBasis b h
  set ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : n → R) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  let P : (n → R) →ₗ[R] (n → R) := b'.constr R (fun i => (ab i : n → R))
  have hPb : ∀ i, P (b' i) = a i • b' i := by
    intro i; simp only [P, Basis.constr_basis, hab]
  have hdetP : LinearMap.det P = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' P = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hPb, map_smul, b'.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.det_diagonal]
  have hPinj : Function.Injective P := endo_inj P (by
    rw [hdetP]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i))
  have hPL : ∀ x, P x ∈ LinearMap.range L := by
    intro x
    rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [map_smul, hPb, ← hab]
    exact Submodule.smul_mem _ _ (ab i).2
  have hLP : ∀ x, L x ∈ LinearMap.range P := by
    intro x
    let y : LinearMap.range L := ⟨L x, LinearMap.mem_range_self L x⟩
    refine ⟨∑ i, ab.repr y i • b' i, ?_⟩
    have e2 := congrArg Subtype.val (ab.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [map_sum]
    calc ∑ i, P (ab.repr y i • b' i) = ∑ i, ab.repr y i • (ab i : n → R) :=
          Finset.sum_congr rfl (fun i _ => by rw [map_smul, hPb, hab])
      _ = L x := e2
  let g : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective P hPinj).symm.toLinearMap ∘ₗ L.codRestrict (LinearMap.range P) hLP
  let g' : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective L hinj).symm.toLinearMap ∘ₗ P.codRestrict (LinearMap.range L) hPL
  have hg : P ∘ₗ g = L := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective P hPinj).apply_symm_apply
      (L.codRestrict (LinearMap.range P) hLP x))
  have hg' : L ∘ₗ g' = P := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective L hinj).apply_symm_apply
      (P.codRestrict (LinearMap.range L) hPL x))
  have hdetL : LinearMap.det L = u.det := by
    rw [hL, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  have d1 : LinearMap.det P ∣ u.det := ⟨LinearMap.det g, by rw [← hdetL, ← hg, LinearMap.det_comp]⟩
  have d2 : u.det ∣ LinearMap.det P := ⟨LinearMap.det g', by rw [← hdetL, ← hg', LinearMap.det_comp]⟩
  rw [← hdetP]
  exact emultiplicity_eq_of_associated_right (associated_of_dvd_dvd d1 d2)

end IdxDet

theorem index_eq_determinant : Formalism.HermitianLattices.RamifiedLatticeOperators.Index_det := by
  intro R _ _ _ ϖ hϖ n _ _ u hu
  exact index_det ϖ hϖ u hu

theorem root_of_unity_congruence_one : Formalism.HermitianLattices.RamifiedLatticeOperators.RootOfUnityCongruenceOne := by
  intro K _ _ P T n b hT hP hTP hn hb hb1 hne
  have hfo : IsOfFinOrder b := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hb⟩
  have hfin : orderOf b ≠ 0 := (orderOf_pos_iff.mpr hfo).ne'
  have hne1 : orderOf b ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, hld⟩ := Nat.exists_prime_and_dvd hne1
  set c := b ^ (orderOf b / l) with hc
  have hco : orderOf c = l := orderOf_pow_orderOf_div hfin hld
  have hpow : ∀ (x : NumberField.RingOfIntegers K) (m : ℕ), x - 1 ∈ P → x ^ m - 1 ∈ P := by
    intro x m hx
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow x 1 m
    rw [one_pow] at hd
    rw [hd]; exact P.mul_mem_right d hx
  have hc1 : c - 1 ∈ P := hpow b _ hb1
  have hcl : c ^ l = 1 := hco ▸ pow_orderOf_eq_one c
  have hcne : c ≠ 1 := by
    intro h; rw [h, orderOf_one] at hco; exact hl.one_lt.ne hco
  have hsum : ∑ i ∈ range l, c ^ i = 0 := by
    have h := mul_geom_sum c l
    rw [hcl, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hcne)
  have hlP : (l : NumberField.RingOfIntegers K) ∈ P := by
    have e : (l : NumberField.RingOfIntegers K) =
        ∑ i ∈ range l, c ^ i - ∑ i ∈ range l, (c ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e, hsum, zero_sub]
    exact P.neg_mem (P.sum_mem fun i _ => hpow c i hc1)
  have hlT : l = T := by
    by_contra hlt
    have hcop : IsCoprime (l : ℤ) (T : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hT).mpr hlt)
    obtain ⟨x, y, hxy⟩ := hcop
    have h1 : (1 : NumberField.RingOfIntegers K) ∈ P := by
      have e := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers K) hxy
      push_cast at e
      rw [← e]
      exact P.add_mem (P.mul_mem_left _ hlP) (P.mul_mem_left _ hTP)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hprim : IsPrimitiveRoot (algebraMap (NumberField.RingOfIntegers K) K c) T := by
    rw [← hlT, ← hco]
    exact (IsPrimitiveRoot.orderOf c).map_of_injective (IsFractionRing.injective _ K)
  have : NeZero T := ⟨hT.ne_zero⟩
  have hmin := Polynomial.cyclotomic_eq_minpoly_rat hprim (Nat.pos_of_ne_zero hT.ne_zero)
  have hdeg := minpoly.natDegree_le (A := ℚ) (algebraMap (NumberField.RingOfIntegers K) K c)
  rw [← hmin, Polynomial.natDegree_cyclotomic, Nat.totient_prime hT] at hdeg
  exact hdeg

theorem invariant_kernel_trace_vanishes : Formalism.HermitianLattices.RamifiedLatticeOperators.InvariantKernelTraceVanishes := by
  intro F _ _ _ r R _ k φ hk hnm
  classical
  set s := univ.filter (fun f : Fin r → F => f ≠ 0) with hs
  let g : (Fin r → F) → Set (Fin r → F) := fun f => MulAction.orbit Fˣ f
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
    (fun i hi => Finset.mem_image_of_mem g hi)]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.mp hj
  have hf0' : f0 ≠ 0 := (Finset.mem_filter.mp hf0).2
  have key : ∑ i ∈ s with g i = g f0, k i * φ i = ∑ c : Fˣ, k ((c : F) • f0) * φ ((c : F) • f0) := by
    symm
    refine Finset.sum_bij (fun c _ => (c : F) • f0) ?_ ?_ ?_ ?_
    · intro c _
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact smul_ne_zero (Units.ne_zero c) hf0'
      · show MulAction.orbit Fˣ ((c : F) • f0) = MulAction.orbit Fˣ f0
        rw [← Units.smul_def]; exact MulAction.orbit_smul c f0
    · intro c _ c' _ h
      have h2 : ((c : F) - c') • f0 = 0 := by rw [sub_smul, h, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact Units.ext (sub_eq_zero.mp h3)
      · exact absurd h3 hf0'
    · intro i hi
      have hi2 : MulAction.orbit Fˣ i = MulAction.orbit Fˣ f0 := (Finset.mem_filter.mp hi).2
      have hi3 : i ∈ MulAction.orbit Fˣ f0 := hi2 ▸ MulAction.mem_orbit_self i
      obtain ⟨c, hc⟩ := hi3
      exact ⟨c, Finset.mem_univ _, by rw [← hc]; exact (Units.smul_def c f0).symm⟩
    · intro c _; rfl
  rw [key]
  have : ∑ c : Fˣ, k ((c : F) • f0) * φ ((c : F) • f0) = k f0 * Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f0 := by
    rw [Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hk c f0]; rfl
  rw [this, hnm f0 hf0', mul_zero]

theorem overlattice_three_orbits : Formalism.HermitianLattices.RamifiedLatticeOperators.OverlatticeThreeOrbits := by
  intro q hqF n La hz hint
  dsimp only
  have hq2 : 2 ≤ q := hqF.out.two_le
  have : NeZero q := ⟨hqF.out.ne_zero⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqF.out.ne_zero
  have notint : ∀ k : ℤ, (q : ℚ)⁻¹ ≠ k := by
    intro k h
    have h1 : (((q : ℤ) * k : ℤ) : ℚ) = 1 := by
      push_cast; rw [← h, mul_inv_cancel₀ hq0]
    have h2 : (q : ℤ) * k = 1 := by exact_mod_cast h1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h3 | h3 <;> omega
  have h10 : (1 : ZMod q) ≠ 0 := one_ne_zero
  have hzm : ∀ m : ℤ, ((0 : Fin n → ℚ), (m : ℚ)) ∈ La := by
    intro m
    have e : ((0 : Fin n → ℚ), (m : ℚ)) = m • ((0 : Fin n → ℚ), (1 : ℚ)) :=
      Prod.ext (by simp) (by simp)
    rw [e]; exact La.zsmul_mem hz m
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hzq : ((0 : Fin n → ℚ), (q : ℚ)⁻¹) ∈ La
    · right; left
      refine ⟨hzq, fun p hp => ?_⟩
      obtain ⟨k, hk⟩ := hint p hp
      have e : (p.1, (0 : ℚ)) = p - k • ((0 : Fin n → ℚ), (q : ℚ)⁻¹) := by
        refine Prod.ext (by simp) ?_
        rw [Prod.snd_sub, Prod.smul_snd, zsmul_eq_mul]
        rw [← hk, mul_comm (q : ℚ) p.2, mul_assoc, mul_inv_cancel₀ hq0, mul_one, sub_self]
      rw [e]; exact La.sub_mem hp (La.zsmul_mem hzq k)
    · have S0 : ∀ s : ℚ, ((0 : Fin n → ℚ), s) ∈ La → ∃ m : ℤ, s = m := by
        intro s hs
        obtain ⟨k, hk⟩ := hint _ hs
        change (q : ℚ) * s = k at hk
        by_cases hk0 : (k : ZMod q) = 0
        · obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k q).mp hk0
          refine ⟨m, ?_⟩
          have h3 : (q : ℚ) * s = q * m := by rw [hk, hm]; push_cast; ring
          exact mul_left_cancel₀ hq0 h3
        · exfalso; apply hzq
          obtain ⟨a, ha⟩ : ∃ a : ZMod q, a * k = 1 := ⟨(k : ZMod q)⁻¹, inv_mul_cancel₀ hk0⟩
          have hd : (((a.val : ℤ) * k - 1 : ℤ) : ZMod q) = 0 := by
            push_cast; rw [ZMod.natCast_zmod_val, ha, sub_self]
          obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hd
          have hb' : ((a.val : ℚ)) * k - 1 = q * b := by exact_mod_cast hb
          have key : (q : ℚ) * ((a.val : ℚ) * s - b) = 1 := by
            linear_combination (a.val : ℚ) * hk + hb'
          have e : ((0 : Fin n → ℚ), (q : ℚ)⁻¹) =
              ((a.val : ℤ) • ((0 : Fin n → ℚ), s) - b • ((0 : Fin n → ℚ), (1 : ℚ))) := by
            refine Prod.ext (by simp) ?_
            rw [Prod.snd_sub, Prod.smul_snd, Prod.smul_snd, zsmul_eq_mul, zsmul_eq_mul, mul_one]
            push_cast
            exact (eq_inv_of_mul_eq_one_right key).symm
          rw [e]; exact La.sub_mem (La.zsmul_mem hs _) (La.zsmul_mem hz b)
      have hmem : ∀ a : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), ∃ s : ℚ, (a.1, s) ∈ La := by
        rintro ⟨a, ha⟩
        obtain ⟨p, hp, rfl⟩ := AddSubgroup.mem_map.mp ha
        exact ⟨p.2, by simpa using hp⟩
      choose sel hsel using hmem
      have hfloor : ∀ a, (q : ℚ) * sel a = ((⌊(q : ℚ) * sel a⌋ : ℤ) : ℚ) := by
        intro a; obtain ⟨k, hk⟩ := hint _ (hsel a)
        change (q : ℚ) * sel a = k at hk
        rw [hk, Int.floor_intCast]
      let fv : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ) → ZMod q :=
        fun a => ((⌊(q : ℚ) * sel a⌋ : ℤ) : ZMod q)
      have W : ∀ p ∈ La, ∀ a : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), p.1 = a.1 →
          ∀ k : ℤ, (q : ℚ) * p.2 = k → (k : ZMod q) = fv a := by
        intro p hp a hpa k hk
        have hd : ((0 : Fin n → ℚ), p.2 - sel a) ∈ La := by
          have e : ((0 : Fin n → ℚ), p.2 - sel a) = p - (a.1, sel a) :=
            Prod.ext (by simp [hpa]) (by simp)
          rw [e]; exact La.sub_mem hp (hsel a)
        obtain ⟨m, hm⟩ := S0 _ hd
        have h1 : ((⌊(q : ℚ) * sel a⌋ : ℤ) : ℚ) = ((k - q * m : ℤ) : ℚ) := by
          rw [← hfloor]; push_cast
          linear_combination (-(q : ℚ)) * hm + hk
        have h2 : (⌊(q : ℚ) * sel a⌋ : ℤ) = k - q * m := by exact_mod_cast h1
        show (k : ZMod q) = ((⌊(q : ℚ) * sel a⌋ : ℤ) : ZMod q)
        rw [h2]; push_cast; simp [ZMod.natCast_self]
      have fv_zero : fv 0 = 0 := by
        have h := W 0 La.zero_mem 0 rfl 0 (by simp)
        simpa using h.symm
      have fv_add : ∀ a b, fv (a + b) = fv a + fv b := by
        intro a b
        have h := W ((a.1, sel a) + (b.1, sel b)) (La.add_mem (hsel a) (hsel b)) (a + b) (by simp)
          (⌊(q : ℚ) * sel a⌋ + ⌊(q : ℚ) * sel b⌋)
          (by rw [Int.cast_add, ← hfloor, ← hfloor, Prod.snd_add, mul_add])
        rw [← h]; push_cast; rfl
      let f : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ) →+ ZMod q :=
        { toFun := fv, map_zero' := fv_zero, map_add' := fv_add }
      have C : ∀ p : (Fin n → ℚ) × ℚ, p ∈ La ↔
          ∃ h : p.1 ∈ La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), ∃ k : ℤ, (q : ℚ) * p.2 = k ∧
            (k : ZMod q) = f ⟨p.1, h⟩ := by
        intro p
        constructor
        · intro hp
          refine ⟨AddSubgroup.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
          obtain ⟨k, hk⟩ := hint p hp
          exact ⟨k, hk, W p hp _ rfl k hk⟩
        · rintro ⟨h, k, hk, hkf⟩
          have hkf' : (k : ZMod q) = ((⌊(q : ℚ) * sel ⟨p.1, h⟩⌋ : ℤ) : ZMod q) := hkf
          have hd : ((k - ⌊(q : ℚ) * sel ⟨p.1, h⟩⌋ : ℤ) : ZMod q) = 0 := by
            push_cast; rw [hkf', sub_self]
          obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hd
          have e2 : p.2 = sel ⟨p.1, h⟩ + m := by
            have h1 : (((k - ⌊(q : ℚ) * sel ⟨p.1, h⟩⌋ : ℤ)) : ℚ) = ((q * m : ℤ) : ℚ) := by rw [hm]
            push_cast at h1
            rw [← hk, ← hfloor] at h1
            have h3 : (q : ℚ) * p.2 = q * (sel ⟨p.1, h⟩ + m) := by linear_combination h1
            exact mul_left_cancel₀ hq0 h3
          have e : p = (p.1, sel ⟨p.1, h⟩) + ((0 : Fin n → ℚ), (m : ℚ)) :=
            Prod.ext (by simp) (by simp [e2])
          rw [e]; exact La.add_mem (hsel ⟨p.1, h⟩) (hzm m)
      by_cases hs : Function.Surjective f
      · right; right
        refine ⟨f, ⟨hs, C⟩, ?_⟩
        rintro f' ⟨_, C'⟩
        ext a
        obtain ⟨h', k', hk', hkf'⟩ := (C' (a.1, sel a)).mp (hsel a)
        obtain ⟨h, k, hk, hkf⟩ := (C (a.1, sel a)).mp (hsel a)
        have hkk : k = k' := by exact_mod_cast hk.symm.trans hk'
        have e1 : f' a = (k' : ZMod q) := hkf'.symm
        have e2 : f a = (k : ZMod q) := hkf.symm
        rw [e1, e2, hkk]
      · left
        have hf0 : ∀ a, f a = 0 := by
          intro a
          by_contra hne
          apply hs
          intro d
          refine ⟨((d * (f a)⁻¹).val) • a, ?_⟩
          rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hne,
            mul_one]
        intro p hp
        obtain ⟨h, k, hk, hkf⟩ := (C p).mp hp
        rw [hf0] at hkf
        obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hkf
        have e2 : p.2 = m := by
          have h3 : (q : ℚ) * p.2 = q * m := by rw [hk, hm]; push_cast; ring
          exact mul_left_cancel₀ hq0 h3
        refine ⟨?_, m, e2⟩
        have e : (p.1, (0 : ℚ)) = p - ((0 : Fin n → ℚ), (m : ℚ)) :=
          Prod.ext (by simp) (by simp [e2])
        rw [e]; exact La.sub_mem hp (hzm m)
  · rintro ⟨h1, h2, _⟩
    obtain ⟨_, k, hk⟩ := h1 _ h2
    exact notint k hk
  · rintro ⟨h1, f, ⟨hs, hC⟩, _⟩
    obtain ⟨a, ha⟩ := hs 1
    have hmem : (a.1, (q : ℚ)⁻¹) ∈ La := (hC _).mpr ⟨a.2, 1,
      by show (q : ℚ) * (q : ℚ)⁻¹ = ((1 : ℤ) : ℚ); rw [mul_inv_cancel₀ hq0, Int.cast_one],
      by show ((1 : ℤ) : ZMod q) = f a; rw [ha, Int.cast_one]⟩
    obtain ⟨_, k, hk⟩ := h1 _ hmem
    exact notint k hk
  · rintro ⟨⟨hzq, _⟩, f, ⟨_, hC⟩, _⟩
    obtain ⟨h, k, hk, hkf⟩ := (hC _).mp hzq
    have hk1 : k = 1 := by
      have h3 : ((k : ℤ) : ℚ) = 1 := by rw [← hk]; exact mul_inv_cancel₀ hq0
      exact_mod_cast h3
    have h4 : f ⟨((0 : Fin n → ℚ), (q : ℚ)⁻¹).1, h⟩ = 0 := by
      have e : (⟨((0 : Fin n → ℚ), (q : ℚ)⁻¹).1, h⟩ : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ)) = 0 :=
        rfl
      rw [e, map_zero]
    rw [h4, hk1, Int.cast_one] at hkf
    exact h10 hkf

section Count

variable {F : Type} [Field F] [Fintype F]

theorem card_fiber_eq {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (x0 : V) :
    Nat.card {x : V // L x = L x0} = Nat.card {x : V // L x = 0} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1 - x0, by rw [map_sub, x.2, sub_self]⟩
      invFun := fun y => ⟨y.1 + x0, by rw [map_add, y.2, zero_add]⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

theorem card_fiber_prod {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (ψ : V →ₗ[F] F) (x1 : V) (a : W) (b : F) (ha : L x1 = a) (hb : ψ x1 = b) :
    Nat.card {x : V // L x = a ∧ ψ x = b} = Nat.card {x : V // L x = 0 ∧ ψ x = 0} := by
  subst ha hb
  have e1 : Nat.card {x : V // L x = L x1 ∧ ψ x = ψ x1} =
      Nat.card {x : V // (L.prod ψ) x = (L.prod ψ) x1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [Prod.ext_iff])
  have e2 : Nat.card {x : V // L x = 0 ∧ ψ x = 0} = Nat.card {x : V // (L.prod ψ) x = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [Prod.ext_iff])
  rw [e1, e2, card_fiber_eq]

theorem card_slice {V W : Type} [AddCommGroup V] [Module F V] [Finite V] [AddCommGroup W]
    [Module F W] (L : V →ₗ[F] W) (ψ : V →ₗ[F] F) (s : V) (hs : L s = 0) (hψ : ψ s ≠ 0) (c : F) :
    Fintype.card F * Nat.card {x : V // L x = 0 ∧ ψ x = c} = Nat.card {x : V // L x = 0} := by
  have hfib : ∀ c : F, Nat.card {x : V // L x = 0 ∧ ψ x = c} =
      Nat.card {x : V // L x = 0 ∧ ψ x = 0} := fun c =>
    card_fiber_prod L ψ ((c / ψ s) • s) 0 c (by rw [map_smul, hs, smul_zero])
      (by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hψ])
  have hsig : Nat.card {x : V // L x = 0} = ∑ c : F, Nat.card {x : V // L x = 0 ∧ ψ x = c} := by
    rw [← Nat.card_sigma (α := F) (β := fun c => {x : V // L x = 0 ∧ ψ x = c})]
    exact Nat.card_congr
      { toFun := fun x => ⟨ψ x.1, x.1, x.2, rfl⟩
        invFun := fun y => ⟨y.2.1, y.2.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => by rcases y with ⟨c, x, h1, rfl⟩; rfl }
  rw [hsig, Finset.sum_congr rfl (fun c _ => hfib c), hfib c, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]

theorem card_ker {V W : Type} [AddCommGroup V] [Module F V] [Fintype V] [AddCommGroup W]
    [Module F W] (L : V →ₗ[F] W) :
    Nat.card {x : V // L x = 0} = Fintype.card F ^ finrank F (LinearMap.ker L) := by
  classical
  rw [show Nat.card {x : V // L x = 0} = Nat.card (LinearMap.ker L) from
    Nat.card_congr (Equiv.subtypeEquivRight fun x => LinearMap.mem_ker.symm)]
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]

theorem mem_range_iff_dual {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (A : Matrix m k F) (v : m → F) :
    v ∈ LinearMap.range A.mulVecLin ↔ ∀ w : m → F, Aᵀ *ᵥ w = 0 → w ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ w hw
    rw [Matrix.mulVecLin_apply, dotProduct_mulVec, ← Matrix.mulVec_transpose, hw, zero_dotProduct]
  · intro h
    by_contra hv
    obtain ⟨φ, hφv, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    set w : m → F := fun i => φ (fun j => if i = j then 1 else 0) with hwdef
    have hφw : ∀ y, φ y = w ⬝ᵥ y := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ φ y, dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_eq_mul, mul_comm]
    apply hφv
    rw [hφw]
    apply h
    funext j
    rw [Matrix.mulVec_transpose]
    have hj : φ (A *ᵥ Pi.single j 1) = 0 := by
      have h1 : A *ᵥ Pi.single j 1 ∈ LinearMap.range A.mulVecLin := ⟨_, rfl⟩
      have h2 : φ (A *ᵥ Pi.single j 1) ∈ (LinearMap.range A.mulVecLin).map φ :=
        Submodule.mem_map_of_mem h1
      rw [hφ] at h2
      exact (Submodule.mem_bot F).mp h2
    rw [hφw, dotProduct_mulVec, dotProduct_single, mul_one] at hj
    simpa using hj

theorem pow_pred_of_mul {q a e : ℕ} (hq : 1 < q) (h : q * a = q ^ e) :
    1 ≤ e ∧ a = q ^ (e - 1) := by
  rcases e with _ | e
  · rw [pow_zero] at h
    have h1 : q ∣ 1 := ⟨a, h.symm⟩
    have h2 := Nat.le_of_dvd one_pos h1
    omega
  · refine ⟨by omega, ?_⟩
    rw [pow_succ'] at h
    simpa using Nat.eq_of_mul_eq_mul_left (by omega) h

end Count

theorem affine_fibre_count_comparison : Formalism.HermitianLattices.RamifiedLatticeOperators.AffineFibreCountComparison := by
  intro F _ _ n g xb f uW
  classical
  dsimp only
  set q := Fintype.card F with hqdef
  have hq1 : 1 < q := Fintype.one_lt_card
  set M := LinearMap.toMatrix' xb with hM
  have hxbM : M.mulVecLin = xb := by rw [hM, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hxb : ∀ l, xb l = M *ᵥ l := fun l => by rw [← hxbM]; rfl
  let T : (Fin (n + g) → F) →ₗ[F] (Fin n → F) := Mᵀ.mulVecLin
  have hTw : ∀ w, T w = w ᵥ* M := fun w => Matrix.mulVec_transpose M w
  have hcond : ∀ (w : Fin (n + g) → F) (f' : Fin n → F),
      (∀ l, w ⬝ᵥ xb l = f' ⬝ᵥ l) ↔ T w = f' := by
    intro w f'
    constructor
    · intro h; funext j
      have h1 := h (Pi.single j 1)
      rw [hxb, dotProduct_mulVec, dotProduct_single, dotProduct_single, mul_one, mul_one] at h1
      rw [hTw]; exact h1
    · intro h l; rw [hxb, dotProduct_mulVec, ← hTw, h]
  set rk := finrank F (LinearMap.range xb) with hrk
  have hrkT : finrank F (LinearMap.range T) = rk := by
    have h1 := Matrix.rank_transpose M
    unfold Matrix.rank at h1
    rw [hxbM] at h1
    exact h1
  have hrkle : rk ≤ n := by
    have h1 := LinearMap.finrank_range_le xb
    simpa using h1
  have hkerT : Nat.card {w : Fin (n + g) → F // T w = 0} = q ^ (n + g - rk) := by
    rw [card_ker]; congr 1
    have h1 := LinearMap.finrank_range_add_finrank_ker T
    rw [hrkT, Module.finrank_fin_fun] at h1; omega
  have hkerx : Nat.card {u : Fin n → F // xb u = 0} = q ^ (n - rk) := by
    rw [card_ker]; congr 1
    have h1 := LinearMap.finrank_range_add_finrank_ker xb
    rw [Module.finrank_fin_fun] at h1; omega
  have hfker : (∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0) ↔ f ∈ LinearMap.range T := by
    have h1 := mem_range_iff_dual Mᵀ f
    rw [Matrix.transpose_transpose] at h1
    rw [show f ∈ LinearMap.range T ↔ f ∈ LinearMap.range Mᵀ.mulVecLin from Iff.rfl, h1]
    constructor
    · intro h w hw
      rw [dotProduct_comm]; exact h w (by rw [LinearMap.mem_ker, hxb]; exact hw)
    · intro h l hl
      rw [dotProduct_comm]; exact h l (by rw [← hxb]; exact LinearMap.mem_ker.mp hl)
  have huW : uW ∈ LinearMap.range xb ↔ ∀ w, T w = 0 → w ⬝ᵥ uW = 0 := by
    have h1 := mem_range_iff_dual M uW
    rw [hxbM] at h1
    exact h1
  let ψ : (Fin (n + g) → F) →ₗ[F] F :=
    { toFun := fun w => w ⬝ᵥ uW, map_add' := fun a b => add_dotProduct a b uW,
      map_smul' := fun c a => smul_dotProduct c a uW }
  let χ : (Fin n → F) →ₗ[F] F :=
    { toFun := fun u => f ⬝ᵥ u, map_add' := fun a b => dotProduct_add f a b,
      map_smul' := fun c a => dotProduct_smul c f a }
  have hA : Nat.card {fW : Fin (n + g) → F // fW ⬝ᵥ uW = 1 ∧ ∀ l, fW ⬝ᵥ xb l = f ⬝ᵥ l} =
      Nat.card {w // T w = f ∧ ψ w = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by rw [hcond]; exact and_comm)
  have hB : Nat.card {u : Fin n → F // f ⬝ᵥ u = 1 ∧ xb u = uW} =
      Nat.card {u // xb u = uW ∧ χ u = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => and_comm)
  rw [hA, hB]
  have zeroA : f ∉ LinearMap.range T → Nat.card {w // T w = f ∧ ψ w = 1} = 0 := fun h =>
    Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h ⟨x.1, x.2.1⟩⟩)
  have zeroB : uW ∉ LinearMap.range xb → Nat.card {u // xb u = uW ∧ χ u = 1} = 0 := fun h =>
    Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h ⟨x.1, x.2.1⟩⟩)
  have halfA : f ∈ LinearMap.range T → uW ∉ LinearMap.range xb →
      q * Nat.card {w // T w = f ∧ ψ w = 1} = q ^ (n + g - rk) := by
    rintro ⟨w0, hw0⟩ hu
    rw [huW] at hu; push Not at hu
    obtain ⟨s, hs, hψs⟩ := hu
    have hψs' : ψ s ≠ 0 := hψs
    rw [card_fiber_prod T ψ (w0 + ((1 - ψ w0) / ψ s) • s) f 1
      (by rw [map_add, map_smul, hs, smul_zero, add_zero, hw0])
      (by rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hψs']; ring),
      card_slice T ψ s hs hψs' 0, hkerT]
  have halfB : uW ∈ LinearMap.range xb → ¬ (∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0) →
      q * Nat.card {u // xb u = uW ∧ χ u = 1} = q ^ (n - rk) := by
    rintro ⟨u0, hu0⟩ hf
    push Not at hf
    obtain ⟨s, hs, hχs⟩ := hf
    rw [LinearMap.mem_ker] at hs
    have hχs' : χ s ≠ 0 := hχs
    rw [card_fiber_prod xb χ (u0 + ((1 - χ u0) / χ s) • s) uW 1
      (by rw [map_add, map_smul, hs, smul_zero, add_zero, hu0])
      (by rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hχs']; ring),
      card_slice xb χ s hs hχs' 0, hkerx]
  have fullA : ∀ u0, xb u0 = uW → f ∈ LinearMap.range T →
      Nat.card {w // T w = f ∧ ψ w = 1} = if f ⬝ᵥ u0 = 1 then q ^ (n + g - rk) else 0 := by
    rintro u0 hu0 ⟨w0, hw0⟩
    have hval : ∀ w, T w = f → ψ w = f ⬝ᵥ u0 := by
      intro w hw
      show w ⬝ᵥ uW = f ⬝ᵥ u0
      rw [← hu0, hxb, dotProduct_mulVec, ← hTw, hw]
    split_ifs with h1
    · rw [← hkerT, ← card_fiber_eq T w0, hw0]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun w =>
        ⟨fun h => h.1, fun h => ⟨h, by rw [hval w h, h1]⟩⟩)
    · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h1 ((hval x.1 x.2.1).symm.trans x.2.2)⟩)
  have fullB : ∀ u0, xb u0 = uW → (∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0) →
      Nat.card {u // xb u = uW ∧ χ u = 1} = if f ⬝ᵥ u0 = 1 then q ^ (n - rk) else 0 := by
    intro u0 hu0 hf
    have hval : ∀ u, xb u = uW → χ u = f ⬝ᵥ u0 := by
      intro u hu
      have hk : u - u0 ∈ LinearMap.ker xb := by
        rw [LinearMap.mem_ker, map_sub, hu, hu0, sub_self]
      have h2 := hf _ hk
      show f ⬝ᵥ u = f ⬝ᵥ u0
      rw [dotProduct_sub, sub_eq_zero] at h2; exact h2
    split_ifs with h1
    · rw [← hkerx, ← card_fiber_eq xb u0, hu0]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun u =>
        ⟨fun h => h.1, fun h => ⟨h, by rw [hval u h, h1]⟩⟩)
    · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h1 ((hval x.1 x.2.1).symm.trans x.2.2)⟩)
  refine ⟨fun hu hf => ?_, fun hu hf => ?_, fun hu hf => ?_, fun hu hf => ?_⟩
  · rw [zeroB hu]
    obtain ⟨_, h2⟩ := pow_pred_of_mul hq1 (halfA (hfker.mp hf) hu)
    rw [h2]; push_cast; ring
  · rw [zeroA (fun h => hf (hfker.mpr h))]
    obtain ⟨he, h2⟩ := pow_pred_of_mul hq1 (halfB hu hf)
    rw [h2]; push_cast
    have e : n + g - rk - 1 = g + (n - rk - 1) := by omega
    rw [e, pow_add]; ring
  · obtain ⟨u0, hu0⟩ := hu
    rw [fullA u0 hu0 (hfker.mp hf), fullB u0 hu0 hf]
    have e : n + g - rk = g + (n - rk) := by omega
    split_ifs
    · push_cast; rw [e, pow_add]; ring
    · push_cast; ring
  · rw [zeroA (fun h => hf (hfker.mpr h)), zeroB hu]; simp

end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
