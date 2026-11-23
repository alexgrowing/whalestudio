import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DKillsPoly
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Algebra.MvPolynomial.Nilpotent

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem left_inv_of_jac {A E K : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing K] [Algebra A K]
    [Module.Finite A K] {m : ℕ} (s : Fin m → K) (z : Fin m → E) (hz : ∀ i, z i ∈ Ring.jacobson E) :
    ∃ v : K ⊗[A] E, v * (1 + ∑ i, s i ⊗ₜ z i) = 1 := by
  let w : E ⊗[A] K := ∑ i, z i ⊗ₜ s i
  have hw : ∀ y : E ⊗[A] K, y * w ∈ Module.jacobson E (E ⊗[A] K) := by
    intro y
    induction y with
    | zero => simp
    | add a b ha hb => rw [add_mul]; exact add_mem ha hb
    | tmul e a =>
      rw [Finset.mul_sum]
      refine Submodule.sum_mem _ fun i _ => Ring.jacobson_smul_top_le E _ ?_
      have : (e ⊗ₜ[A] a) * (z i ⊗ₜ[A] s i) = (e * z i) • ((1 : E) ⊗ₜ[A] (a * s i)) := by
        simp [smul_tmul']
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (hz i)) Submodule.mem_top
  let f : E ⊗[A] K →ₗ[E] E ⊗[A] K :=
    { toFun := fun y => y * (1 + w)
      map_add' := fun a b => add_mul _ _ _
      map_smul' := fun e y => smul_mul_assoc e y _ }
  have htop : LinearMap.range f = ⊤ := by
    rcases eq_top_or_exists_le_coatom (LinearMap.range f) with h | ⟨N, hN, hle⟩
    · exact h
    · exfalso
      refine hN.1 (eq_top_iff.2 fun y _ => ?_)
      have h1 : y * (1 + w) ∈ N := hle ⟨y, rfl⟩
      have h2 : y * w ∈ N := (sInf_le hN : Module.jacobson E (E ⊗[A] K) ≤ N) (hw y)
      have := N.sub_mem h1 h2
      rwa [mul_add, mul_one, add_sub_cancel_right] at this
  obtain ⟨v, hv⟩ : (1 : E ⊗[A] K) ∈ LinearMap.range f := htop ▸ Submodule.mem_top
  refine ⟨Algebra.TensorProduct.comm A E K v, ?_⟩
  have hv' : v * (1 + w) = 1 := hv
  have h := congrArg (Algebra.TensorProduct.comm A E K) hv'
  rw [map_mul, map_one] at h
  simpa [w, map_sum] using h

private theorem kills_of_jac {n : ℕ} {k R : Type} [Field k] [Ring R] [Algebra k R] (D : Det n k R) (x : R)
    (hx : x ∈ Ring.jacobson R) : D.Kills x := by
  refine UpperTheory.V.CA.d_kills_poly D x Set.univ (by simp) fun m h _ => ?_
  set P := D.D (MvPolynomial (Fin m) k) (1 + Det.gen h * (1 ⊗ₜ x)) with hP
  have key : ∀ (K : Type) [CommRing K] [Algebra k K] (φ : MvPolynomial (Fin m) k →ₐ[k] K),
      φ P = D.D K (1 + ∑ i, φ (MvPolynomial.X i) ⊗ₜ (h i * x)) := by
    intro K _ _ φ
    rw [hP, ← D.nat]
    congr 1
    simp [Det.gen, map_sum, Finset.sum_mul]
  have hu : IsUnit P := by
    by_contra hnu
    obtain ⟨M, hM, hPM⟩ := exists_max_ideal_of_mem_nonunits hnu
    letI := Ideal.Quotient.field M
    haveI : Module.Finite k (MvPolynomial (Fin m) k ⧸ M) := finite_of_finite_type_of_isJacobsonRing _ _
    obtain ⟨v, hv⟩ := left_inv_of_jac (A := k) (fun i => Ideal.Quotient.mkₐ k M (MvPolynomial.X i))
      (fun i => h i * x) (fun i => Ideal.mul_mem_left _ _ hx)
    have h1 := congrArg (D.D _) hv
    rw [map_mul, map_one, ← key, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hPM, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨c, -, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
  have h0 := key k (MvPolynomial.aeval fun _ => 0)
  rw [hc] at h0 ⊢
  simp at h0
  simp [h0]

theorem UpperTheory.V.CA.d_rad :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] (D : Det n A E), D.IsCH → ∀ x : E, (1 : ResidueField A) ⊗ₜ[A] x ∈ (D.baseChange (ResidueField A)).ker ↔ x ∈ Ring.jacobson E := by
  intro n A E _ _ _ _ D hCH x
  rw [(UpperTheory.V.CA.d_ker _ _).1]
  constructor
  · intro hx
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro y
    have h0 := hx (ResidueField A) (1 ⊗ₜ (1 ⊗ₜ y))
    rw [(UpperTheory.V.CA.d_bc D (ResidueField A)).1] at h0
    have h1 : algebraMap A (ResidueField A) (D.val (y * x + 1)) = 1 := by
      have := D.nat A (ResidueField A) (Algebra.ofId A _) (1 ⊗ₜ (y * x + 1))
      refine this.symm.trans (Eq.trans (congrArg _ ?_) h0)
      simp [Det.cancel_tmul, tmul_add, add_comm, Algebra.TensorProduct.one_def]
    have h2 : IsUnit (y * x + 1) :=
      ((UpperTheory.V.CA.d_unit D hCH).1 _).2
        ((residue_ne_zero_iff_isUnit _).1 fun h0 => one_ne_zero (h1.symm.trans h0))
    obtain ⟨u, hu⟩ := h2
    refine ⟨(↑u⁻¹ : E), ?_⟩
    have h3 : (↑u⁻¹ : E) * (y * x + 1) = 1 := by rw [← hu, Units.inv_mul]
    rw [Ideal.mem_bot, sub_eq_zero, ← h3, mul_add, mul_one, mul_assoc]
  · intro hx
    refine kills_of_jac _ _ ?_
    let f : E →+* ResidueField A ⊗[A] E :=
      (Algebra.TensorProduct.includeRight : E →ₐ[A] ResidueField A ⊗[A] E).toRingHom
    haveI : RingHomSurjective f := ⟨fun t => by
      induction t with
      | zero => exact ⟨0, map_zero _⟩
      | add a b ha hb =>
        obtain ⟨a, rfl⟩ := ha
        obtain ⟨b, rfl⟩ := hb
        exact ⟨a + b, map_add _ _ _⟩
      | tmul c e =>
        obtain ⟨a, rfl⟩ := residue_surjective c
        refine ⟨a • e, ?_⟩
        change (1 : ResidueField A) ⊗ₜ[A] (a • e) = _
        rw [← smul_tmul, ← Algebra.algebraMap_eq_smul_one]
        rfl⟩
    exact Ring.le_comap_jacobson f hx
