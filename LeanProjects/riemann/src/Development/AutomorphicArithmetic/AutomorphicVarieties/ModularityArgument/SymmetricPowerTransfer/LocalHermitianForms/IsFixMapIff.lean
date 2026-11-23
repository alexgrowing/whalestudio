import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WTrans

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem sigL_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by ext <;> simp [sigL] <;> ring

theorem sigL_sigL (x : EL Δ τ) : sigL (sigL x) = x := by ext <;> simp [sigL]

theorem sigL_one : sigL (1 : EL Δ τ) = 1 := by ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem sigL_star (x : EL Δ τ) : sigL (star x) = star (sigL x) := by ext <;> simp [sigL]

theorem sigL_ofE (x : Etau K τ) : sigL (ofE Δ x) = ofE Δ x := by ext <;> simp [sigL, ofE]

theorem ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by ext <;> simp [ofE]

theorem ofE_one : ofE Δ (1 : Etau K τ) = 1 := by ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem ofE_star (x : Etau K τ) : ofE Δ (star x) = star (ofE Δ x) := by ext <;> simp [ofE]

theorem quo_mul_star (z : (Etau K τ)ˣ) : quo z * star (quo z) = 1 := by
  rw [quo, star_mul', star_star]
  calc _ = ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * star ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
        rw [star_mul']; ring
    _ = 1 := by simp

variable (O) in

def mulE (y : (EL Δ τ)ˣ) : Sp Δ τ ≃ₗ[O] Sp Δ τ where
  toFun x := (x.1, y * x.2)
  invFun x := (x.1, (y⁻¹ : (EL Δ τ)ˣ) * x.2)
  map_add' a b := by simp [mul_add]
  map_smul' a b := by
    refine Prod.ext rfl ?_
    change (y : EL Δ τ) * (a • b.2) = a • ((y : EL Δ τ) * b.2)
    rw [← algebraMap_smul K a b.2, ← algebraMap_smul K a, mul_smul_comm]
  left_inv x := by simp
  right_inv x := by simp

theorem isFix_map {c : K} {d m d' m' : EL Δ τ} (ψ : Sp Δ τ ≃ₗ[O] Sp Δ τ) (h1 : ∀ x y, herm c m (ψ x) (ψ y) = herm c m' x y)
    (h2 : ∀ x, semi d (ψ x) = ψ (semi d' x)) {S : Set (Sp Δ τ)} (h : IsFix O c d' m' S) : IsFix O c d m (ψ '' S) := by
  classical
  refine ⟨?_, fun y => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := h.fg
    refine ⟨s.image ψ, ?_⟩
    rw [Finset.coe_image, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.map_coe]
  · obtain ⟨y, rfl⟩ := ψ.surjective y
    rw [ψ.injective.mem_set_image, h.dual, Set.forall_mem_image]
    simp only [h1]
  · rw [← Set.image_comp]
    conv_rhs => rw [← h.stab, ← Set.image_comp]
    exact congrArg (· '' S) (funext h2)

theorem isFix_map_iff {c : K} {d m d' m' : EL Δ τ} (ψ : Sp Δ τ ≃ₗ[O] Sp Δ τ) (h1 : ∀ x y, herm c m (ψ x) (ψ y) = herm c m' x y)
    (h2 : ∀ x, semi d (ψ x) = ψ (semi d' x)) (S : Set (Sp Δ τ)) : IsFix O c d m (ψ '' S) ↔ IsFix O c d' m' S := by
  refine ⟨fun h => ?_, isFix_map ψ h1 h2⟩
  have := isFix_map (d := d') (m := m') ψ.symm (fun x y => by rw [← h1]; simp) (fun x => ψ.injective (by rw [← h2]; simp)) h
  rwa [← Set.image_comp, show (ψ.symm ∘ ψ : Sp Δ τ → Sp Δ τ) = id from funext ψ.symm_apply_apply, Set.image_id] at this

theorem isFix_mulE (c : K) (d m : EL Δ τ) (y : (EL Δ τ)ˣ) (S : Set (Sp Δ τ)) : IsFix O c d m (mulE O y '' S) ↔
    IsFix O c (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) (m * (y : EL Δ τ) * star (sigL (y : EL Δ τ))) S := by
  refine isFix_map_iff _ (fun a b => ?_) (fun a => Prod.ext rfl ?_) S
  · change herm c m (a.1, (y : EL Δ τ) * a.2) (b.1, (y : EL Δ τ) * b.2) = _
    simp only [herm, sigL_mul, star_mul']
    congr 2
    ring
  · change d * sigL ((y : EL Δ τ) * a.2) = (y : EL Δ τ) * (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL a.2)
    rw [sigL_mul]
    linear_combination (-d * sigL (y : EL Δ τ) * sigL a.2) * y.mul_inv

theorem isFix_tor (c : K) (d m : EL Δ τ) (z : (Etau K τ)ˣ) (S : Set (Sp Δ τ)) : IsFix O c d m (tor Δ z '' S) ↔ IsFix O c d m S := by
  have h : ofE Δ (quo z) * star (ofE Δ (quo z)) = 1 := by rw [← ofE_star, ← ofE_mul, quo_mul_star, ofE_one]
  let Y : (EL Δ τ)ˣ := Units.mkOfMulEqOne _ _ h
  have := isFix_mulE (O := O) c d m Y S
  rw [show sigL (Y : EL Δ τ) = Y from sigL_ofE _, mul_assoc d, Units.mul_inv, mul_one, mul_assoc m,
    show (Y : EL Δ τ) * star (Y : EL Δ τ) = 1 from h, mul_one] at this
  exact this

end UpperTheory.V.Z.Sym.Loc
