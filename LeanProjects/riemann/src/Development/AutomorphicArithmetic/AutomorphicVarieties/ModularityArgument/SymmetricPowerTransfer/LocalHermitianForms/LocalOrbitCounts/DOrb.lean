import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ScalarComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.MemRangeIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.dOrb : UpperTheory.V.Z.Sym.Loc.DOrb := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j h1 h2
  haveI := L.frac
  obtain ⟨φ, p1, p2, p3, p4⟩ := dIso O K Δ L
  obtain ⟨j', q1, q2, q3⟩ := p4 τ γ j h1 h2
  have sc : ∀ z : Kˣ, IsScal z (φ.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) := fun z => (p2 _ _).2 (by simp)
  have hZ : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := fun g => by
    constructor
    · intro h
      refine (sup_le ?_ ?_ : ZD Δ ⊔ KD Δ O ≤ (ZK O K).comap φ.toMonoidHom) h
      · rintro s ⟨z, hz⟩
        exact Subgroup.mem_sup_left ⟨z, ((p2 z s).1 (congrArg Units.val hz).symm).symm⟩
      · exact fun k hk => Subgroup.mem_sup_right ((p1 k).2 hk)
    · intro h
      obtain ⟨z, k, e⟩ := mem_ZK.1 h
      rw [← φ.symm_apply_apply g, e, map_mul]
      exact mul_mem (Subgroup.mem_sup_left ⟨z, Units.ext (sc z).symm⟩) (Subgroup.mem_sup_right ((p1 _).1 (by rw [φ.apply_symm_apply]; exact ⟨k, rfl⟩)))
  have hf : ∀ χ : Kˣ →* ℂˣ, Unr O χ → ∀ g, fZD O χ g = fZK O χ (φ g) := fun χ hχ g => by
    by_cases h : φ g ∈ ZK O K
    · obtain ⟨z, k, e⟩ := mem_ZK.1 h
      rw [e, (fzkLaw O K Δ L χ hχ).2 z _ ⟨k, rfl⟩, ← φ.symm_apply_apply g, e, map_mul]
      exact (fzdLaw O K Δ L χ hχ).2 z _ _ (sc z) ((p1 _).1 (by rw [φ.apply_symm_apply]; exact ⟨k, rfl⟩))
    · rw [(fzkLaw O K Δ L χ hχ).1 _ h, (fzdLaw O K Δ L χ hχ).1 _ fun h' => h ((hZ g).1 h')]
  have main : ∀ (χ : Kˣ →* ℂˣ), Unr O χ → ∀ (f : DX Δ → ℂ) (z : (Etau K τ)ˣ), (∀ y, f (y⁻¹ * j z * y) = fZK O χ (φ (y⁻¹ * j z * y))) →
      orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) f (j z) = gOrb O j' χ z := fun χ hχ f z H => by
    refine orb_congr j (jU j') _ _ _ _ _ _ _ _ _ φ.toEquiv (fun t y => ?_) (fun y y' => ?_) (fun y => ?_) (fun y y' h => ?_) fun t => ?_
    · simp [q3]
    · simp [hZ]
    · change f (y⁻¹ * j z * y) = fZK O χ ((φ y)⁻¹ * jU j' z * φ y)
      rw [H, map_mul, map_mul, map_inv, q3]
    · change f (y⁻¹ * j z * y) = f (y'⁻¹ * j z * y')
      rw [H, H, ← fZK_conj L hχ ((hZ _).1 h)]; simp [mul_assoc]
    · change _ * j z * j t = j z
      rw [mul_assoc, ← map_mul, mul_comm z, map_mul, inv_mul_cancel_left]
  refine ⟨j', q2, fun a ha => ?_, fun χ hχ z => main χ hχ _ z fun y => hf χ hχ _⟩
  have ea : j a = γ := φ.injective (by rw [q3]; exact Units.ext (by rw [← q1, ← ha]; rfl))
  rw [dS, ← ea]
  refine main 1 (fun _ => rfl) _ a fun y => ?_
  have F := fzkLaw O K Δ L 1 fun _ => rfl
  by_cases h : φ (y⁻¹ * j a * y) ∈ ZK O K
  · obtain ⟨z, k, e⟩ := mem_ZK.1 h
    have hd : (1 : K) = (z : K) ^ 2 * algebraMap O K (k : Matrix (Fin 2) (Fin 2) O).det := by
      have e1 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det) e
      simp only [map_mul, map_inv, q3, Units.val_mul] at e1
      rw [Matrix.det_units_conj', Matrix.det_mul] at e1
      have e2 : ((jU j' a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        change (j' a).det = 1
        rw [ha, j_det_omega j' q2]
      rw [← e2, e1, RingHom.map_det]
      congr 1
      change (Matrix.scalar (Fin 2) (z : K)).det = _
      simp [Matrix.det_fin_two, sq]
    have hu : IsUnit (k : Matrix (Fin 2) (Fin 2) O).det := (Matrix.GeneralLinearGroup.det k).isUnit
    obtain ⟨i, hi⟩ := hu.exists_right_inv
    have hi' := congrArg (algebraMap O K) hi
    rw [map_mul, map_one] at hi'
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : O, algebraMap O K z₀ = z := IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [show (z : K) ^ 2 = algebraMap O K i by linear_combination (-algebraMap O K i) * hd - (z : K) ^ 2 * hi']
      exact isIntegral_algebraMap))
    have hz1 : z₀ * (z₀ * (k : Matrix (Fin 2) (Fin 2) O).det) = 1 := IsFractionRing.injective O K (by
      rw [map_mul, map_mul, hz₀, map_one, hd]; ring)
    have hk : φ (y⁻¹ * j a * y) ∈ KG O K := by
      rw [e]
      refine mul_mem ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mkOfMulEqOne _ _ hz1), Units.ext ?_⟩ ⟨k, rfl⟩
      ext s t
      by_cases hst : s = t <;> simp [hst, hz₀]
    rw [e, F.2 z _ ⟨k, rfl⟩]
    exact (if_pos ((p1 _).1 hk)).trans (by simp)
  · rw [F.1 _ h]
    exact if_neg fun h' => h (Subgroup.mem_sup_right ((p1 _).2 h'))
