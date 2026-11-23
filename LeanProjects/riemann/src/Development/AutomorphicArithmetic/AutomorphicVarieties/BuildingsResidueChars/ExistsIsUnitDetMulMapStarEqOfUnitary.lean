import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

namespace UpperTheory.V.T.UnitaryGeneratorRelations

variable {K : Type} [Field K] [CharZero K] {Δ : K}

private def om (K : Type) [Field K] (Δ : K) : Lsq K Δ := ⟨0, 1⟩

private theorem star_om : star (om K Δ) = - om K Δ := by
  ext <;> simp [om]

private theorem om_om (v : Fin 3 → Lsq K Δ) : om K Δ • om K Δ • v = Δ • v := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ext <;> simp [om]

private theorem star_smulK (r : K) (z : Lsq K Δ) : star (r • z) = r • star z := by
  ext <;> simp

private def S (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) : (Fin 3 → Lsq K Δ) →ₗ[K] (Fin 3 → Lsq K Δ) where
  toFun v := B *ᵥ star v
  map_add' x y := by rw [star_add, mulVec_add]
  map_smul' r x := by
    have : star (r • x) = r • star x := by
      funext i
      exact star_smulK r (x i)
    rw [this, RingHom.id_apply, mulVec_smul]

private theorem S_apply (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v) : S B v = B *ᵥ star v := rfl

private theorem star_mulVec' (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ) :
    star (M *ᵥ v) = M.map star *ᵥ star v := by
  funext i
  simp [mulVec, dotProduct, star_sum, mul_comm]

private theorem S_S {B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : B * B.map star = 1) (v) : S B (S B v) = v := by
  rw [S_apply, S_apply, star_mulVec', star_star, mulVec_mulVec, h, one_mulVec]

private theorem S_om (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v) : S B (om K Δ • v) = - (om K Δ • S B v) := by
  have e : star (om K Δ • v) = -(om K Δ • star v) := by
    funext i
    simp only [Pi.star_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, star_mul', star_om]
    ring
  rw [S_apply, S_apply, e, mulVec_neg, mulVec_smul]

end UpperTheory.V.T.UnitaryGeneratorRelations

open UpperTheory.V.T.UnitaryGeneratorRelations in
theorem UpperTheory.exists_isUnit_det_mul_map_star_eq_of_unitary :
    ∀ (K : Type) [Field K] [CharZero K] (Δ : K), Δ ≠ 0 → ∀ B : Matrix (Fin 3) (Fin 3) (Lsq K Δ), B * B.map star = 1 →
        ∃ Q : Matrix (Fin 3) (Fin 3) (Lsq K Δ), IsUnit Q.det ∧ B * Q.map star = Q := by
  intro K _ _ Δ hΔ B hB
  have dec : ∀ v : Fin 3 → Lsq K Δ, ∃ w1 w2, S B w1 = w1 ∧ S B w2 = w2 ∧ v = w1 + om K Δ • w2 := by
    intro v
    refine ⟨(1/2 : K) • (v + S B v), (1/(2*Δ) : K) • om K Δ • (v - S B v), ?_, ?_, ?_⟩
    · rw [map_smul, map_add, S_S hB, add_comm]
    · rw [map_smul, S_om, map_sub, S_S hB, ← smul_neg, neg_sub]
    · rw [smul_comm (om K Δ) (1/(2*Δ) : K), om_om, smul_smul]
      have h2 : 1/(2*Δ) * Δ = (1/2 : K) := by field_simp
      rw [h2, ← smul_add]
      module
  have uniq : ∀ w1 w2 : Fin 3 → Lsq K Δ, S B w1 = w1 → S B w2 = w2 → w1 + om K Δ • w2 = 0 → w1 = 0 ∧ w2 = 0 := by
    intro w1 w2 h1 h2 h
    have hs : w1 - om K Δ • w2 = 0 := by
      have := congrArg (S B) h
      rwa [map_add, S_om, h1, h2, map_zero, ← sub_eq_add_neg] at this
    have e1 : w1 = 0 := by
      have : (2 : K) • w1 = 0 := by rw [two_smul]; linear_combination (exp := 1) h + hs
      simpa using this
    refine ⟨e1, ?_⟩
    rw [e1, zero_add] at h
    have : Δ • w2 = 0 := by rw [← om_om, h, smul_zero]
    exact (smul_eq_zero.mp this).resolve_left hΔ
  have hV : Module.finrank K (Fin 3 → Lsq K Δ) = 6 := by
    rw [Module.finrank_pi_fintype, Module.finrank_eq_card_basis (QuadraticAlgebra.basis Δ 0)]
    simp
  let W : Submodule K (Fin 3 → Lsq K Δ) := LinearMap.ker (S B - LinearMap.id)
  have memW : ∀ w, w ∈ W ↔ S B w = w := by
    intro w
    simp [W, sub_eq_zero]
  let f : (W × W) →ₗ[K] (Fin 3 → Lsq K Δ) := W.subtype.coprod (om K Δ • W.subtype)
  have fapp : ∀ p : W × W, f p = (p.1 : Fin 3 → Lsq K Δ) + om K Δ • (p.2 : Fin 3 → Lsq K Δ) := fun p => rfl
  have fbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      rw [fapp] at hp
      obtain ⟨a, b⟩ := uniq _ _ ((memW _).mp p.1.2) ((memW _).mp p.2.2) hp
      exact Prod.ext (Subtype.ext a) (Subtype.ext b)
    · intro v
      obtain ⟨w1, w2, h1, h2, rfl⟩ := dec v
      exact ⟨(⟨w1, (memW _).mpr h1⟩, ⟨w2, (memW _).mpr h2⟩), rfl⟩
  have h3 : Module.finrank K W = 3 := by
    have := (LinearEquiv.ofBijective f fbij).finrank_eq
    rw [Module.finrank_prod, hV] at this
    omega
  let bW := Module.finBasisOfFinrankEq K W h3
  have inW : ∀ j, S B (bW j : Fin 3 → Lsq K Δ) = bW j := fun j => (memW _).mp (bW j).2
  let Q : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of fun i j => (bW j : Fin 3 → Lsq K Δ) i
  have span : ∀ w (hw : w ∈ W), w = ∑ j, (bW.repr ⟨w, hw⟩ j) • (bW j : Fin 3 → Lsq K Δ) := by
    intro w hw
    have := congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at this
    simpa using this.symm
  refine ⟨Q, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w1, w2, h1, h2, rfl⟩ := dec v
    have s1 := span w1 ((memW _).mpr h1)
    have s2 := span w2 ((memW _).mpr h2)
    set c := bW.repr ⟨w1, (memW _).mpr h1⟩
    set d := bW.repr ⟨w2, (memW _).mpr h2⟩
    refine ⟨fun j => algebraMap K (Lsq K Δ) (c j) + om K Δ * algebraMap K (Lsq K Δ) (d j), ?_⟩
    rw [s1, s2]
    funext i
    simp only [mulVec, dotProduct, Q, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      Algebra.smul_def, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun j _ => by simp only [Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]; ring
  · refine Matrix.ext fun i j => ?_
    have := congrFun (inW j) i
    rw [S_apply] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct, Q] using this
