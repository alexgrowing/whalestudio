import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.SelfTwist

open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem quadratic_twist_charpoly_eq {K G : Type} [Field K] [Group G] (h2 : (2 : K) ≠ 0)
    (r : G →* Matrix (Fin 4) (Fin 4) K) (S : Subgroup G) (φ : G →* Kˣ)
    (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (h1 : φ ≠ 1) (hS : S ≤ φ.ker) (hsq : ∀ g, φ g * φ g = 1)
    (he : ∀ g v, r g *ᵥ e v = (φ g : K) • e (r g *ᵥ v)) :
    ∃ η : G →* ℤˣ, η ≠ 1 ∧ S ≤ η.ker ∧
      ∀ g, (r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • r g).charpoly := by
  classical
  let ι : ℤˣ →* Kˣ := Units.map (Int.castRingHom K).toMonoidHom
  have hι : ∀ u : ℤˣ, ((ι u : Kˣ) : K) = ((u : ℤ) : K) := fun u => rfl
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro u hu
    rcases Int.units_eq_one_or u with h | h
    · exact h
    · exfalso
      have := congrArg Units.val hu
      rw [hι, h] at this
      apply hneg
      simpa using this
  have hex : ∀ g, ∃ u : ℤˣ, ι u = φ g := by
    intro g
    have h : (φ g : K) * (φ g : K) = 1 := by
      rw [← Units.val_mul, hsq, Units.val_one]
    rcases mul_self_eq_one_iff.mp h with h | h
    · exact ⟨1, Units.ext (by rw [hι, h]; simp)⟩
    · exact ⟨-1, Units.ext (by rw [hι, h]; simp)⟩
  choose η hη using hex
  let η' : G →* ℤˣ := MonoidHom.mk' η (fun a b => hinj (by rw [map_mul, hη, hη, hη, map_mul]))
  have hη' : ∀ g, η' g = η g := fun g => rfl
  refine ⟨η', ?_, ?_, ?_⟩
  · intro h
    apply h1
    ext1 g
    rw [← hη, ← hη', h]
    simp
  · intro g hg
    rw [MonoidHom.mem_ker]
    apply hinj
    rw [hη', hη, map_one]
    exact hS hg
  · intro g
    rw [hη', ← hι, hη]
    have hc : e.conj (Matrix.toLin' ((φ g : K) • r g)) = Matrix.toLin' (r g) := by
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := e.surjective v
      rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply, Matrix.toLin'_apply,
        Matrix.toLin'_apply, he, Matrix.smul_mulVec, map_smul]
    rw [← Matrix.charpoly_toLin', ← hc, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']

theorem UpperTheory.V.Ws.exists_sign_twist_charpoly_of_not_irreducible_restriction :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G], (2 : K) ≠ 0 → ∀ r : G →* Matrix (Fin 4) (Fin 4) K, U3.MatIrr ⊤ r →
      ∀ S : Subgroup G, commutator G ≤ S → S.index ∣ 4 → ¬ U3.MatIrr S r →
      ∃ η : G →* ℤˣ, η ≠ 1 ∧ S ≤ η.ker ∧ ∀ g, (r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • r g).charpoly := by
  intro K G _ _ _ h2 r hirr S hcomm hidx hred
  have hab : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S := fun a b =>
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  haveI hN : S.Normal := ⟨fun n hn g => by
    have := S.mul_mem (hab g n) hn
    simpa using this⟩
  have h4 : ((4 : ℕ) : K) ≠ 0 := by
    have : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  obtain ⟨m, hm⟩ := hidx
  have hiK : (S.index : K) ≠ 0 := by
    intro h
    apply h4
    rw [hm, Nat.cast_mul, h, zero_mul]
  have hfi : S.FiniteIndex := ⟨fun h => hiK (by rw [h, Nat.cast_zero])⟩
  let ρ : Representation K G (Fin 4 → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin 4)).toMonoidHom.comp r
  have hρ : ∀ g v, ρ g v = r g *ᵥ v := fun g v => Matrix.toLinAlgEquiv'_apply _ _
  unfold U3.MatIrr at hirr hred
  push Not at hred
  obtain ⟨φ, e, h1, hS, he⟩ := UpperTheory.V.Pr.T.selfTwist ρ S hfi hiK hab
    (fun W hW => hirr W (fun g _ v hv => hρ g v ▸ hW g v hv))
    (by
      obtain ⟨W, hW, hb, ht⟩ := hred
      exact ⟨W, fun g hg v hv => (hρ g v).symm ▸ hW g hg v hv, hb, ht⟩)
  simp only [hρ] at he
  by_cases hsq : ∀ g, φ g * φ g = 1
  · exact quadratic_twist_charpoly_eq h2 r S φ e h1 hS hsq he
  · refine quadratic_twist_charpoly_eq h2 r S (φ * φ) (e.trans e) ?_ ?_ ?_ ?_
    · intro h
      apply hsq
      intro g
      exact DFunLike.congr_fun h g
    · intro g hg
      have : φ g = 1 := hS hg
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, this, one_mul]
    · intro g
      have h : φ (g ^ S.index) = 1 := hS (S.pow_index_mem g)
      have h' : φ g ^ 4 = 1 := by rw [hm, pow_mul, ← map_pow, h, one_pow]
      rw [MonoidHom.mul_apply, ← h']
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    · intro g v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, he, map_smul, smul_smul,
        MonoidHom.mul_apply, Units.val_mul]
