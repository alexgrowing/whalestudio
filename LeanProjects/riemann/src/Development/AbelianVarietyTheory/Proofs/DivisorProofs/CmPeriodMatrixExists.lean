import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem surj_lattice : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ e : Fin (Module.finrank ℚ (FR E)) ≃ I,
      ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ), Function.Surjective M ∧
        ∀ z, (∀ j, ∃ a b : ℤ, z j = a + b * io δ) → ∃ x ∈ lattice c y, M z = fun j ↦ φ (e j) x := by
  intro K _ _ d δ io hK hd hδ E _ _ _ _ I _ φ hφ hio c y hc e
  classical
  have hEK : Module.finrank K E = Module.finrank ℚ (FR E) := by
    have h1 : Module.finrank ℚ E = 2 * Module.finrank ℚ (FR E) := by
      rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
        Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
    have h2 : Module.finrank ℚ K * Module.finrank K E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ K E
    rw [hK, h1] at h2
    omega
  generalize Module.finrank ℚ (FR E) = f at e hEK ⊢
  let b := Module.finBasisOfFinrankEq K E hEK
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)
  obtain ⟨N, hN0, hNmem, -⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y

  have hint : ∀ j, IsIntegral ℤ (m • b j) := fun j => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hδint : IsIntegral ℤ (algebraMap K E δ) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [← map_pow, hδ]; simp
  let u : Fin f → 𝓞 E := fun j => ⟨m • b j, hint j⟩
  let v : Fin f → 𝓞 E := fun j => ⟨algebraMap K E δ * (m • b j), hδint.mul (hint j)⟩
  let w : Fin f → E := fun j => (N : E) * (m • b j)
  have hw : ∀ j, w j ∈ lattice c y := fun j => hNmem (u j)
  have hδw : ∀ j, algebraMap K E δ * w j ∈ lattice c y := fun j => by
    have := hNmem (v j)
    simpa [w, v, mul_left_comm] using this

  have hs : ∀ _j : Fin f, IsUnit ((N : K) * (m : K)) := fun _ => by
    refine IsUnit.mk0 _ (mul_ne_zero (by exact_mod_cast hN0.ne') (by exact_mod_cast hm0))
  let b' := b.isUnitSMul hs
  have hb' : ∀ j, b' j = w j := fun j => by
    simp only [b', Module.Basis.isUnitSMul_apply, w, Algebra.smul_def, zsmul_eq_mul, map_mul, map_natCast, map_intCast]
    simp only [algebraMap_int_eq, eq_intCast]
    ring
  let A : Matrix (Fin f) (Fin f) ℂ := fun i j => φ (e i) (w j)
  refine ⟨Matrix.mulVecLin A, ?_, ?_⟩
  ·
    show Function.Surjective A.mulVec
    rw [Matrix.mulVec_surjective_iff_isUnit, ← Matrix.linearIndependent_rows_iff_isUnit]
    have hinj : Function.Injective (fun i : Fin f => ((φ (e i) : E →+* ℂ) : E →* ℂ)) := by
      intro i i' h
      have h' : φ (e i) = φ (e i') := RingHom.ext fun x => DFunLike.congr_fun h x
      obtain ⟨k, -, hk⟩ := hφ (φ (e i))
      have a1 := hk (e i) (Or.inl rfl)
      have a2 := hk (e i') (Or.inl h')
      exact e.injective (a1.trans a2.symm)
    have li : LinearIndependent ℂ (fun i : Fin f => ((((φ (e i) : E →+* ℂ) : E →* ℂ)) : E → ℂ)) :=
      (linearIndependent_monoidHom E ℂ).comp _ hinj
    rw [Fintype.linearIndependent_iff] at li ⊢
    intro g hg i
    refine li g ?_ i
    funext x
    have hrow : ∀ j, ∑ i, g i * φ (e i) (w j) = 0 := fun j => by
      have := congrFun hg j
      simpa [Matrix.row, A, Finset.sum_apply] using this
    have hx : x = ∑ j, b'.repr x j • w j := by
      conv_lhs => rw [← b'.sum_repr x]
      simp only [hb']
    simp only [Finset.sum_apply, Pi.smul_apply, MonoidHom.coe_coe, smul_eq_mul, Pi.zero_apply]
    rw [hx]
    simp only [map_sum, Algebra.smul_def, map_mul]
    have hio' : ∀ i (k : K), φ (e i) (algebraMap K E k) = io k := fun i k => by
      rw [← hio (e i)]; rfl
    simp only [hio']
    calc ∑ i, g i * ∑ j, io (b'.repr x j) * φ (e i) (w j)
        = ∑ j, io (b'.repr x j) * ∑ i, g i * φ (e i) (w j) := by
          simp only [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by simp [hrow]
  · intro z hz
    choose a a' ha using hz
    refine ⟨∑ j, ((a j : E) * w j + (a' j : E) * (algebraMap K E δ * w j)), ?_, ?_⟩
    · rw [← coe_latticeSub]
      refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.add_mem _ ?_ ?_
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hw j) _
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hδw j) _
    · funext i
      have hio' : φ (e i) (algebraMap K E δ) = io δ := by rw [← hio (e i)]; rfl
      show A.mulVec z i = φ (e i) _
      simp only [Matrix.mulVec, dotProduct, A, map_sum, map_add, map_mul, map_intCast, hio', ha]
      refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.LatModel
