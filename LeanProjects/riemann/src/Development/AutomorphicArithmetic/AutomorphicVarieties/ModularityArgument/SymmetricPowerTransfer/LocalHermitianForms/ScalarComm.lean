import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem orb_congr {T G G' : Type} [CommGroup T] [Group G] [Group G'] (ι : T →* G) (ι' : T →* G') (C : Subgroup T) (θ : G →* G) (θ' : G' →* G')
    (U : Subgroup G) (U' : Subgroup G') (f : G → ℂ) (f' : G' → ℂ) (δ : G) (δ' : G') (e : G ≃ G') (h1 : ∀ t y, e (ι t * y) = ι' t * e y)
    (h2 : ∀ y y', y⁻¹ * y' ∈ U ↔ (e y)⁻¹ * e y' ∈ U') (h3 : ∀ y, f (y⁻¹ * δ * θ y) = f' ((e y)⁻¹ * δ' * θ' (e y)))
    (h4 : ∀ y y', y⁻¹ * y' ∈ U → f (y⁻¹ * δ * θ y) = f (y'⁻¹ * δ * θ y')) (h5 : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) :
    orb ι C θ U f δ = orb ι' C θ' U' f' δ' := by
  classical
  letI : MulAction T (G ⧸ U) := MulAction.compHom (G ⧸ U) ι
  letI : MulAction T (G' ⧸ U') := MulAction.compHom (G' ⧸ U') ι'
  have sm : ∀ (t : T) (y : G), t • (y : G ⧸ U) = ((ι t * y : G) : G ⧸ U) := fun _ _ => rfl
  have sm' : ∀ (t : T) (y : G'), t • (y : G' ⧸ U') = ((ι' t * y : G') : G' ⧸ U') := fun _ _ => rfl
  have kmk : ∀ y : G, f ((Quotient.out (y : G ⧸ U))⁻¹ * δ * θ (Quotient.out (y : G ⧸ U))) =
      f (y⁻¹ * δ * θ y) := by
    intro y
    apply h4
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have kmk' : ∀ y : G, f' ((Quotient.out ((e y : G') : G' ⧸ U'))⁻¹ * δ' *
      θ' (Quotient.out ((e y : G') : G' ⧸ U'))) = f (y⁻¹ * δ * θ y) := by
    intro y
    have hy : (e.symm (Quotient.out ((e y : G') : G' ⧸ U')))⁻¹ * y ∈ U := by
      rw [h2, e.apply_symm_apply, ← QuotientGroup.eq, QuotientGroup.out_eq']
    rw [← e.apply_symm_apply (Quotient.out ((e y : G') : G' ⧸ U')), ← h3, h4 _ _ hy]
  have conj : ∀ (t : T) (y : G), f ((ι t * y)⁻¹ * δ * θ (ι t * y)) = f (y⁻¹ * δ * θ y) := by
    intro t y
    rw [show (ι t * y)⁻¹ * δ * θ (ι t * y) = y⁻¹ * ((ι t)⁻¹ * δ * θ (ι t)) * θ y by
      rw [map_mul]
      group, h5]
  have hsurj : ∀ q' : G' ⧸ U', ∃ y : G, ((e y : G') : G' ⧸ U') = q' := by
    intro q'
    refine QuotientGroup.induction_on q' fun y' => ?_
    exact ⟨e.symm y', by rw [e.apply_symm_apply]⟩
  unfold orb
  refine wTrans T (G ⧸ U) (G' ⧸ U') C _ _
    (fun q q' => ∃ y : G, (y : G ⧸ U) = q ∧ ((e y : G') : G' ⧸ U') = q') ?_ ?_ ?_ ?_ ?_ ?_
  · intro t q
    refine QuotientGroup.induction_on q fun y => ?_
    rw [sm, kmk, kmk, conj]
  · intro t q'
    obtain ⟨y, rfl⟩ := hsurj q'
    rw [sm', ← h1, kmk', kmk', conj]
  · rintro t q q' ⟨y, rfl, rfl⟩
    exact ⟨ι t * y, sm t y, by rw [sm', h1]⟩
  · rintro q q' ⟨y, rfl, rfl⟩
    rw [kmk, kmk']
  · intro q _
    refine ⟨((e (Quotient.out q) : G') : G' ⧸ U'), ⟨Quotient.out q, QuotientGroup.out_eq' q, rfl⟩, ?_⟩
    rintro q'' ⟨y, hy, rfl⟩
    apply QuotientGroup.eq.mpr
    rw [← h2, ← QuotientGroup.eq, hy, QuotientGroup.out_eq']
  · intro q' _
    obtain ⟨y0, hy0⟩ := hsurj q'
    refine ⟨(y0 : G ⧸ U), ⟨y0, rfl, hy0⟩, ?_⟩
    rintro q ⟨y, rfl, hy⟩
    apply QuotientGroup.eq.mpr
    rw [h2, ← QuotientGroup.eq, hy, hy0]

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K] in
theorem scalar_comm (z : Kˣ) (g : GL (Fin 2) K) : Matrix.GeneralLinearGroup.scalar (Fin 2) z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, mul_comm]

theorem fZK_conj (L : IsLoc O Δ) {χ : Kˣ →* ℂˣ} (hχ : Unr O χ) {u : GL (Fin 2) K} (hu : u ∈ ZK O K) (g : GL (Fin 2) K) :
    fZK O χ (u⁻¹ * g * u) = fZK O χ g := by
  obtain ⟨hout, hin⟩ := fzkLaw O K Δ L χ hχ
  obtain ⟨z, k, rfl⟩ := mem_ZK.mp hu
  by_cases hg : g ∈ ZK O K
  · obtain ⟨w, k', rfl⟩ := mem_ZK.mp hg
    have e1 : Matrix.GeneralLinearGroup.map (algebraMap O K) k' * Matrix.GeneralLinearGroup.scalar (Fin 2) z =
        Matrix.GeneralLinearGroup.scalar (Fin 2) z * Matrix.GeneralLinearGroup.map (algebraMap O K) k' :=
      (scalar_comm z _).symm
    have e2 : (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) w *
        Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm z⁻¹ w, mul_assoc, inv_mul_cancel, mul_one]
    have e3 : (Matrix.GeneralLinearGroup.map (algebraMap O K) k)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) w =
        Matrix.GeneralLinearGroup.scalar (Fin 2) w * (Matrix.GeneralLinearGroup.map (algebraMap O K) k)⁻¹ :=
      (scalar_comm w _).symm
    have key : (Matrix.GeneralLinearGroup.scalar (Fin 2) z * Matrix.GeneralLinearGroup.map (algebraMap O K) k)⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) w * Matrix.GeneralLinearGroup.map (algebraMap O K) k') *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * Matrix.GeneralLinearGroup.map (algebraMap O K) k) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) w * Matrix.GeneralLinearGroup.map (algebraMap O K) (k⁻¹ * k' * k) := by
      rw [mul_inv_rev, map_mul, map_mul, map_inv]
      calc _ = (Matrix.GeneralLinearGroup.map (algebraMap O K) k)⁻¹ *
            ((Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) w *
            (Matrix.GeneralLinearGroup.map (algebraMap O K) k' * Matrix.GeneralLinearGroup.scalar (Fin 2) z)) *
            Matrix.GeneralLinearGroup.map (algebraMap O K) k := by
            simp only [mul_assoc]
        _ = (Matrix.GeneralLinearGroup.map (algebraMap O K) k)⁻¹ *
            ((Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) w *
            Matrix.GeneralLinearGroup.scalar (Fin 2) z) * Matrix.GeneralLinearGroup.map (algebraMap O K) k' *
            Matrix.GeneralLinearGroup.map (algebraMap O K) k := by
            rw [e1]
            simp only [mul_assoc]
        _ = _ := by
            rw [e2, e3]
            simp only [mul_assoc]
    rw [key, hin w _ ⟨_, rfl⟩, hin w _ ⟨_, rfl⟩]
  · have hg' : (Matrix.GeneralLinearGroup.scalar (Fin 2) z * Matrix.GeneralLinearGroup.map (algebraMap O K) k)⁻¹ * g *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * Matrix.GeneralLinearGroup.map (algebraMap O K) k) ∉ ZK O K := by
      intro h
      apply hg
      have := (ZK O K).mul_mem ((ZK O K).mul_mem hu h) ((ZK O K).inv_mem hu)
      simpa [mul_assoc] using this
    rw [hout _ hg', hout _ hg]

end UpperTheory.V.Z.Sym.Loc
