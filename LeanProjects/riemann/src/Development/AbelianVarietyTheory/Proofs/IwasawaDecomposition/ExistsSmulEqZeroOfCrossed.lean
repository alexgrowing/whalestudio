import Mathlib

set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.TransferCommutator

theorem exists_smul_eq_zero_of_crossed {G : Type} [Group G] [Finite G] {R : Type} [CommRing R] (ε : R →+* ℤ)
    (ρ : G → R) (hρ : ∀ g, ε (ρ g) = 1) {X : Type} [AddCommGroup X] [Module R X] (d : G → X)
    (hd : ∀ g h, d (g * h) = d g + ρ g • d h) :
    ∃ μ : R, (ε μ).natAbs = Nat.card (Abelianization G) ∧ ∀ g, μ • d g = 0 := by
  classical
  have := Fintype.ofFinite G
  let J : Submodule R X := (Submodule.pi Set.univ fun _ : G => RingHom.ker ε).map (Fintype.linearCombination R d)
  let ψ : G →* Multiplicative (X ⧸ J) := MonoidHom.mk' (fun g => Multiplicative.ofAdd (J.mkQ (d g))) fun g h => by
    rw [← ofAdd_add, ← map_add]
    congr 1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hd]
    refine ⟨Pi.single h (ρ g - 1), fun i _ => ?_, ?_⟩
    · by_cases hi : i = h
      · subst hi; simp [RingHom.mem_ker, hρ]
      · simp [hi]
    · rw [Fintype.linearCombination_apply_single, sub_smul, one_smul]; abel
  let ψ' : Additive (Abelianization G) →ₗ[ℤ] X ⧸ J :=
    (MonoidHom.toAdditiveLeft (Abelianization.lift ψ)).toIntLinearMap
  have hψ' : ∀ g, ψ' (Additive.ofMul (Abelianization.of g)) = J.mkQ (d g) := fun g => rfl
  let L : (G → ℤ) →ₗ[ℤ] Additive (Abelianization G) :=
    Fintype.linearCombination ℤ fun g => Additive.ofMul (Abelianization.of g)
  have hL : Function.Surjective L := fun q => by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s := commutator G) q.toMul
    exact ⟨Pi.single g 1, by rw [Fintype.linearCombination_apply_single, one_smul]; exact congrArg Additive.ofMul hg⟩
  have eq := L.quotKerEquivOfSurjective hL
  have hfin : Finite (Abelianization G) := inferInstanceAs (Finite (G ⧸ commutator G))
  have : Finite ((G → ℤ) ⧸ LinearMap.ker L) := Finite.of_equiv _ eq.symm.toEquiv
  let e : (G → ℤ) ≃ₗ[ℤ] LinearMap.ker L :=
    LinearEquiv.ofFinrankEq _ _ ((Submodule.finiteQuotient_iff _).1 this).symm
  have hdet := Submodule.natAbs_det_equiv (LinearMap.ker L) e
  have hrel : ∀ n : LinearMap.ker L, ∃ ν : G → R, (∀ i, ε (ν i) = n.1 i) ∧ ∑ i, ν i • d i = 0 := fun n => by
    have h0 : ∑ i, n.1 i • d i ∈ J := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      have := congrArg ψ' n.2
      rw [map_zero, Fintype.linearCombination_apply, map_sum] at this
      simpa only [map_zsmul, hψ'] using this
    obtain ⟨ν, hν, hs⟩ := h0
    refine ⟨fun i => (n.1 i : R) - ν i, fun i => ?_, ?_⟩
    · rw [map_sub, (RingHom.mem_ker).1 (hν i trivial)]; simp
    · simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul]
      rw [← hs, Fintype.linearCombination_apply, sub_self]
  choose ν hν hs using hrel
  let M : Matrix G G R := Matrix.of fun j i => ν (e (Pi.single j 1)) i
  refine ⟨M.det, ?_, fun k => ?_⟩
  · rw [RingHom.map_det, ← Matrix.det_transpose, ← Nat.card_congr (eq.toEquiv.trans Additive.toMul), ← hdet,
      ← LinearMap.det_toMatrix']
    congr 2
    ext i j
    simp [M, hν, LinearMap.toMatrix'_apply]
  · have h1 : M.det • d k = ∑ i, (M.adjugate * M) k i • d i := by
      rw [Matrix.adjugate_mul]
      simp [Matrix.one_apply]
    rw [h1]
    simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.smul_sum]
    exact (congrArg _ (hs _)).trans (smul_zero _)

theorem transfer_eq_one (G : Type) [Group G] [Finite G] (B : Type) [CommGroup B] (φ : commutator G →* B) :
    MonoidHom.transfer φ = 1 := by
  classical
  let Q := Abelianization G
  have hfin : Finite Q := inferInstanceAs (Finite (G ⧸ commutator G))
  let : Fintype Q := (commutator G).fintypeQuotientOfFiniteIndex
  let R := MonoidAlgebra ℤ Q
  let T : (commutator G).LeftTransversal := default
  let α : Q → G := fun q => (T.2.leftQuotientEquiv q : G)
  have hα : ∀ q, Abelianization.of (α q) = q := fun q => T.2.leftQuotientEquiv.symm_apply_apply q
  have hmem : ∀ g q, (α q)⁻¹ * g * α ((Abelianization.of g)⁻¹ * q) ∈ commutator G := fun g q => by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    simp [hα]
  let b : G → Q → Additive B := fun g q => Additive.ofMul (φ ⟨_, hmem g q⟩)
  have hb : ∀ g h q, b (g * h) q = b g q + b h ((Abelianization.of g)⁻¹ * q) := fun g h q => by
    simp only [b]
    rw [← ofMul_mul, ← map_mul]
    congr 2
    ext
    simp [mul_assoc]
  let s : Q →* R := MonoidAlgebra.of ℤ Q
  let ε : R →ₐ[ℤ] ℤ := MonoidAlgebra.lift ℤ ℤ Q 1
  let d : G → (R ⊗[ℤ] Additive B) × R := fun g => (∑ q, s q ⊗ₜ b g q, s (Abelianization.of g) - 1)
  obtain ⟨μ, hμ, h0⟩ := exists_smul_eq_zero_of_crossed (ε : R →+* ℤ) (fun g => s (Abelianization.of g))
    (fun g => MonoidAlgebra.lift_of _ _) d fun g h => by
      refine Prod.ext ?_ ?_
      · simp only [d, Prod.fst_add, Prod.smul_fst, hb, TensorProduct.tmul_add, Finset.sum_add_distrib,
          Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]
        congr 1
        exact (Fintype.sum_equiv (Equiv.mulLeft (Abelianization.of g)) _ _ fun q => by simp).symm
      · simp only [d, Prod.snd_add, Prod.smul_snd, map_mul, smul_eq_mul]; ring
  have hinv : ∀ q, μ * s q = μ := fun q => by
    have := congrArg Prod.snd (h0 (α q))
    simp only [d, Prod.smul_snd, hα, smul_eq_mul, mul_sub, mul_one, Prod.snd_zero] at this
    exact sub_eq_zero.1 this
  have hc : ∀ q, μ.coeff q = μ.coeff 1 := fun q => by
    have := MonoidAlgebra.coeff_mul_single_apply μ 1 q⁻¹ 1
    rw [show μ * MonoidAlgebra.single q⁻¹ 1 = μ from hinv q⁻¹] at this
    rw [inv_inv, one_mul, mul_one] at this
    exact this.symm
  have hε : ε μ = (Nat.card Q : ℤ) * μ.coeff 1 := by
    simp only [ε]
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [hc]
  have hu : (μ.coeff 1).natAbs = 1 := by
    rw [show (ε : R →+* ℤ) μ = _ from hε, Int.natAbs_mul, Int.natAbs_natCast] at hμ
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (hμ.trans (mul_one _).symm)
  let c : R →ₗ[ℤ] ℤ := Finsupp.lapply (1 : Q) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℤ (S := ℤ) (M := Q)).toLinearMap
  ext g
  have h1 := congrArg Prod.fst (h0 g)
  simp only [d, Prod.smul_fst, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, hinv, Prod.fst_zero,
    ← TensorProduct.tmul_sum] at h1
  have h2 := congrArg (fun x => TensorProduct.lid ℤ _ (c.rTensor _ x)) h1
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h2
  have h3 : ∑ q, b g q = 0 := by
    rcases Int.natAbs_eq_iff.1 hu with h | h
    · rw [show c μ = _ from h] at h2; simpa using h2
    · rw [show c μ = _ from h] at h2; simpa using h2
  rw [MonoidHom.transfer_def φ T, MonoidHom.one_apply]
  have h4 : ∏ q, (b g q).toMul = 1 := by rw [← toMul_sum, h3, toMul_zero]
  refine Eq.trans (Finset.prod_congr rfl fun q _ => congrArg φ (Subtype.ext ?_)) h4
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_assoc]
  rfl

end GlobalTheory.TransferCommutator
