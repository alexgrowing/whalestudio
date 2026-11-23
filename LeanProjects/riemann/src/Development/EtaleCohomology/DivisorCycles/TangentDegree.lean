import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix

namespace LateralTheory.DivDb.TangentDegree
open LateralTheory.DivDb

variable {C : Type} [Field C]

lemma aeval_self_eq_ev {N : ℕ} (x : Mat C N) (f : MP C N) :
    MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = ev x f := rfl

noncomputable def U {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) i j

noncomputable def Z {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => (((k + 1).factorial : C)⁻¹ • Y ^ (k + 1)) i j

lemma U_eq {N : ℕ} (Y : Mat C N) : U Y = 1 + (PowerSeries.X : PowerSeries C) • Z Y := by
  ext i j k
  rcases k with _ | k
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      PowerSeries.coeff_zero_X_mul, add_zero, Matrix.one_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one]
    split_ifs <;> simp
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      PowerSeries.coeff_succ_X_mul, Matrix.one_apply]
    split_ifs <;> simp

lemma constantCoeff_Z {N : ℕ} (Y : Mat C N) (i j : Fin N) : PowerSeries.constantCoeff (Z Y i j) = Y i j := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Z, PowerSeries.coeff_mk]

lemma map_aeval_ring {R S σ : Type} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S] (k : R →+* S)
    (hk : k.comp (algebraMap C R) = algebraMap C S) (x : σ → R) (f : MvPolynomial σ C) :
    k (MvPolynomial.aeval x f) = MvPolynomial.aeval (k ∘ x) f := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hk]

lemma van_of (hD : DegPoly) {N n : ℕ} (S : Submonoid (Mat C N)) (hS : ∀ x ∈ S, Deg n x) :
    ∃ 𝓕 : Set (MP C N), (∀ (F : Type) [Field F] [Algebra C F] (x : Mat F N),
      Deg n x ↔ ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = 0) ∧
      ∀ f ∈ 𝓕, f ∈ Van (S : Set (Mat C N)) := by
  obtain ⟨𝓕, h𝓕⟩ := hD C N n
  refine ⟨𝓕, h𝓕, fun f hf x hx => ?_⟩
  rw [← aeval_self_eq_ev]
  exact (h𝓕 C x).1 (hS x hx) f hf

lemma tan_deg (hE : ExpVan) (hD : DegPoly) [CharZero C] {N n : ℕ} (S : Submonoid (Mat C N))
    (hS : ∀ x ∈ S, Deg n x) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) : Deg n Y := by
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  let F := FractionRing (PowerSeries C)
  let ι : PowerSeries C →+* F := algebraMap (PowerSeries C) F
  let alg : Algebra C F := (ι.comp (algebraMap C (PowerSeries C))).toAlgebra
  have hιinj : Function.Injective ι := IsFractionRing.injective (PowerSeries C) F
  have hmap : ∀ (M : Matrix (Fin N) (Fin N) (PowerSeries C)) (f : MP C N),
      @MvPolynomial.aeval C F _ _ _ alg (fun p : Fin N × Fin N => (M.map ι) p.1 p.2) f
        = ι (MvPolynomial.aeval (fun p : Fin N × Fin N => M p.1 p.2) f) := by
    intro M f
    rw [map_aeval_ring (S := F) ι rfl]
    rfl
  have hUF : Deg n ((U Y).map ι) := by
    refine (@h𝓕 F _ alg ((U Y).map ι)).2 fun f hf => ?_
    rw [hmap]
    have := hE C N S Y hY f (hvan f hf)
    simp only [U] at this ⊢
    rw [this, map_zero]
  set s : F := ι PowerSeries.X with hsdef
  have hs : s ≠ 0 := (map_ne_zero_iff ι hιinj).2 PowerSeries.X_ne_zero
  have hUZ : (U Y).map ι = 1 + s • (Z Y).map ι := by
    rw [U_eq]; ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      Matrix.one_apply, hsdef]
    split_ifs <;> simp
  have hZF : Deg n ((Z Y).map ι) := by
    obtain ⟨q, hq0, hqd, hqx⟩ := hUF
    refine ⟨q.comp (Polynomial.C s * Polynomial.X + Polynomial.C 1), ?_, ?_, ?_⟩
    · intro h
      rcases Polynomial.comp_eq_zero_iff.1 h with h | ⟨_, h⟩
      · exact hq0 h
      · have := congrArg Polynomial.natDegree h
        rw [Polynomial.natDegree_linear hs, Polynomial.natDegree_C] at this
        exact one_ne_zero this
    · rw [Polynomial.natDegree_comp, Polynomial.natDegree_linear hs, mul_one]; exact hqd
    · rw [Polynomial.aeval_comp]
      convert hqx using 2
      rw [hUZ]
      simp [Algebra.algebraMap_eq_smul_one, add_comm]
  have hZ0 : ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => Z Y p.1 p.2) f = 0 := by
    intro f hf
    have := (@h𝓕 F _ alg ((Z Y).map ι)).1 hZF f hf
    rw [hmap] at this
    exact (map_eq_zero_iff ι hιinj).1 this
  refine (h𝓕 C Y).2 fun f hf => ?_
  have hk : (PowerSeries.constantCoeff (R := C)).comp (algebraMap C (PowerSeries C)) = algebraMap C C := by
    ext c; simp
  have := congrArg PowerSeries.constantCoeff (hZ0 f hf)
  rw [map_aeval_ring _ hk, map_zero] at this
  convert this using 2
  congr 1
  funext p
  simp [constantCoeff_Z]

theorem TanDeg_of (hE : ExpVan) (hD : DegPoly) : TanDeg := by
  intro C _ _ N n S hS
  refine ⟨fun x hx => ?_, fun Y hY => tan_deg hE hD S hS Y hY⟩
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  refine (h𝓕 C x).2 fun f hf => ?_
  rw [aeval_self_eq_ev]
  exact hx f (hvan f hf)

end LateralTheory.DivDb.TangentDegree
