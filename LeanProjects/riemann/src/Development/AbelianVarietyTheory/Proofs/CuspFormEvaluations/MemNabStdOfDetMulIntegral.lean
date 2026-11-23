import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.DetSat

theorem mem_valuationSubring_of_indep {K σ ι : Type} [Field K] [Fintype ι] (A : ValuationSubring K)
    (q : ι → MvPolynomial σ ℤ)
    (hq : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i => map (Int.castRingHom (IsLocalRing.ResidueField A)) (q i)))
    (c : ι → K) (hc : ∀ m, (∑ i, c i • map (Int.castRingHom K) (q i)).coeff m ∈ A) (i : ι) : c i ∈ A := by
  by_contra hi
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => A.valuation (c i)) ⟨i, Finset.mem_univ i⟩
  have h1 : 1 < A.valuation (c j) :=
    lt_of_lt_of_le (not_le.mp fun h => hi ((A.valuation_le_one_iff _).mp h)) (hj i (Finset.mem_univ i))
  have hv0 : 0 < A.valuation (c j) := lt_trans zero_lt_one h1
  have hj0 : c j ≠ 0 := by
    rintro h
    rw [h, map_zero] at hv0
    exact lt_irrefl _ hv0
  have ha : ∀ k, c k / c j ∈ A := fun k => by
    rw [← A.valuation_le_one_iff, map_div₀, div_le_one₀ hv0]
    exact hj k (Finset.mem_univ k)
  let a : ι → A := fun k => ⟨c k / c j, ha k⟩
  have key : ∑ k, IsLocalRing.residue A (a k) • map (Int.castRingHom (IsLocalRing.ResidueField A)) (q k) = 0 := by
    ext m
    have e1 : (∑ k, IsLocalRing.residue A (a k) • map (Int.castRingHom (IsLocalRing.ResidueField A)) (q k)).coeff m
        = IsLocalRing.residue A (∑ k, a k * (((q k).coeff m : ℤ) : A)) := by
      simp [coeff_sum, coeff_map]
    rw [e1, coeff_zero, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    have e2 : ((∑ k, a k * (((q k).coeff m : ℤ) : A) : A) : K)
        = (∑ i, c i • map (Int.castRingHom K) (q i)).coeff m / c j := by
      rw [coeff_sum, Finset.sum_div]
      change A.subtype _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_intCast, coeff_smul, coeff_map]
      simp only [a, ValuationSubring.coe_subtype, smul_eq_mul, eq_intCast]
      ring
    rw [e2, map_div₀, div_lt_one₀ hv0]
    exact lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr (hc m)) h1
  have h0 := Fintype.linearIndependent_iff.mp hq _ key j
  have : a j = 1 := Subtype.ext (div_self hj0)
  rw [this, map_one] at h0
  exact one_ne_zero h0

theorem integral_of_indep {K σ ι : Type} [Field K] [NumberField K] [Fintype ι] (q : ι → MvPolynomial σ ℤ)
    (hq : ∀ (k : Type) [Field k], LinearIndependent k (fun i => map (Int.castRingHom k) (q i)))
    (c : ι → K) (hc : ∀ m, IsIntegral ℤ ((∑ i, c i • map (Int.castRingHom K) (q i)).coeff m)) (i : ι) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c i := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K (c i) fun v => ?_
  refine mem_valuationSubring_of_indep (v.valuation K).valuationSubring q (hq _) c (fun m => ?_) i
  exact v.valuation_le_one (K := K) (⟨_, hc m⟩ : 𝓞 K)

def ssZ (n : ℕ) (ν : Fin n → ℕ) : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℤ :=
  (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose

theorem ssZ_indep (k : Type) [Field k] (n : ℕ) (ν : Fin n → ℕ) :
    LinearIndependent k (fun m => map (Int.castRingHom k) (ssZ n ν m)) := by
  have h : ∀ m, (Formalism.GradedWeylDivisibility.colLex n n).degree (map (Int.castRingHom k) (ssZ n ν m)) = m.1 ∧
      (Formalism.GradedWeylDivisibility.colLex n n).leadingCoeff (map (Int.castRingHom k) (ssZ n ν m)) = 1 := fun m => by
    obtain ⟨hd, -, N, sz, hsz, I, -, hI, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.2 m
    have hb' : ssZ n ν m = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
    have hd' : (Formalism.GradedWeylDivisibility.colLex n n).degree (ssZ n ν m) = m.1 := hd
    rw [hb', (Formalism.GradedWeylDivisibility.column_lex_bideterminant ℤ n n N sz hsz I hI).1] at hd'
    rw [hb', Formalism.GradedWeylDivisibility.ldlat_map_bidet, ← hd']
    exact Formalism.GradedWeylDivisibility.column_lex_bideterminant k n n N sz hsz I hI
  refine Formalism.GradedWeylDivisibility.ldbasis_linearIndependent (Formalism.GradedWeylDivisibility.colLex n n) _ (fun m m' e => ?_) fun m => (h m).2
  exact Subtype.ext ((h m).1.symm.trans (e.trans (h m').1))

theorem ssZ_span (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ) :
    Submodule.span K (Set.range fun m => map (Int.castRingHom K) (ssZ n ν m)) = Formalism.GradedWeylDivisibility.dualWeyl K n n ν := by
  have h := (Formalism.GradedWeylDivisibility.nablaLKBasis ℤ K (algebraMap ℤ K).injective_int n n ν (ssZ n ν) _
    (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1 1 (by simp)).2
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) ((1 : Matrix (Fin n) (Fin n) K)⁻¹) = AlgHom.id K _ := by
    rw [inv_one]
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite C]
  rw [h1] at h
  exact h

theorem ssZ_mem (n : ℕ) (ν : Fin n → ℕ) (m) : ssZ n ν m ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
  rw [← (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1.2.1]
  exact Submodule.subset_span ⟨m, rfl⟩

variable {Ix : Type} [Fintype Ix] {n : ℕ}

def prodZ (lam : Ix → DomWeight n) (i : VVIdx lam) : MvPolynomial (Ix × Fin n × Fin n) ℤ :=
  ∏ t, Formalism.GradedWeylDivisibility.blockEmb ℤ t (ssZ n (lam t).natW (i t))

theorem map_prodZ (k : Type) [CommRing k] (lam : Ix → DomWeight n) (i : VVIdx lam) :
    map (Int.castRingHom k) (prodZ lam i) =
      ∏ t, Formalism.GradedWeylDivisibility.blockEmb k t (map (Int.castRingHom k) (ssZ n (lam t).natW (i t))) := by
  simp only [prodZ, map_prod, Formalism.GradedWeylDivisibility.blockEmb, map_rename]

theorem prodZ_basis (k : Type) [Field k] (lam : Ix → DomWeight n) :
    LinearIndependent k (fun i => map (Int.castRingHom k) (prodZ lam i)) ∧
      Submodule.span k (Set.range fun i => map (Int.castRingHom k) (prodZ lam i)) =
        Formalism.GradedWeylDivisibility.tensorLat k k fun t =>
          Submodule.span k (Set.range fun m => map (Int.castRingHom k) (ssZ n (lam t).natW m)) := by
  simp only [map_prodZ]
  exact Formalism.GradedWeylDivisibility.tensorBasis k k Ix n n (fun t => Formalism.GradedWeylDivisibility.ssIdx n n (lam t).natW) _
    (fun t m => map (Int.castRingHom k) (ssZ n (lam t).natW m)) (fun t => ssZ_indep k n _) (fun _ => rfl)

theorem prodZ_mem (K : Type) [Field K] [NumberField K] (lam : Ix → DomWeight n) (i : VVIdx lam) :
    map (Int.castRingHom K) (prodZ lam i) ∈ nabStd K lam := by
  rw [map_prodZ]
  refine Submodule.subset_span ⟨_, fun t => ?_, rfl⟩
  refine ⟨map (Int.castRingHom (𝓞 K)) (ssZ n (lam t).natW (i t)),
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ _ (ssZ_mem n _ _), ?_⟩
  change map (algebraMap (𝓞 K) K) _ = _
  rw [map_map]
  congr 2

theorem map_detProd (k : Type) [CommRing k] (e : Ix → ℕ) :
    map (Int.castRingHom k) (∏ t, (gen ℤ n t).det ^ e t) = ∏ t, (gen k n t).det ^ e t := by
  simp only [map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 2
  ext a s : 2
  simp [gen]

theorem detProd_ne_zero (k : Type) [Field k] (e : Ix → ℕ) : (∏ t, (gen k n t).det ^ e t) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ fun h => ?_
  have h2 := congrArg (eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) k) v.2.1 v.2.2) h
  rw [RingHom.map_det, map_zero] at h2
  have h3 : (eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) k) v.2.1 v.2.2).mapMatrix (gen k n t)
      = 1 := by
    ext a s
    simp [gen]
  rw [h3, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem mem_nabStd_of_det_mul_integral : ∀ (K : Type) [Field K] [NumberField K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) (e : Ix → ℕ), ∀ F ∈ VV K lam,
    (∀ m, IsIntegral ℤ (((∏ t, (gen K n t).det ^ e t) * F).coeff m)) → F ∈ nabStd K lam := by
  intro K _ _ Ix _ n lam e F hF hint
  have hV : Submodule.span K (Set.range fun i => map (Int.castRingHom K) (prodZ lam i)) = VV K lam := by
    rw [(prodZ_basis K lam).2]
    simp only [ssZ_span]
    rfl
  rw [← hV, Submodule.mem_span_range_iff_exists_fun] at hF
  obtain ⟨c, rfl⟩ := hF
  have h := integral_of_indep (fun i => (∏ t, (gen ℤ n t).det ^ e t) * prodZ lam i) (fun k _ => by
      simp only [map_mul, map_detProd]
      exact (prodZ_basis k lam).1.map' (LinearMap.mulLeft k (∏ t, (gen k n t).det ^ e t))
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ (detProd_ne_zero k e)))) c (fun m => by
      have := hint m
      rw [Finset.mul_sum] at this
      simpa only [map_mul, map_detProd, mul_smul_comm] using this)
  choose a ha using h
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← ha i, algebraMap_smul]
  exact Submodule.smul_mem _ _ (prodZ_mem K lam i)

end GlobalTheory.DetSat
