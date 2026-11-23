import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MapThetaLie

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem grp_id {H : Type*} [Group H] (a b c ab bc abc : H) :
    (a * b * ab⁻¹) * (ab * c * abc⁻¹) = (a * (b * c * bc⁻¹) * a⁻¹) * (a * bc * abc⁻¹) := by
  group

theorem UpperTheory.V.Fr.borelProjection_isTwoCocycle :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ s t r, (B.bar O).ad s ((D.co u).1 (t, r)) + (D.co u).1 (s, t * r) = (D.co u).1 (s * t, r) + (D.co u).1 (s, t) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK s t r
  have hKm : RingHom.ker p ≤ maximalIdeal C' := by
    intro y hy
    rw [← res_eq_zero_iff O C', ← res_map p y, RingHom.mem_ker.mp hy, map_zero]
  obtain ⟨hom, -, -, -⟩ := pr_omk hF O C' C p B D hK
  obtain ⟨x, hx⟩ : ∃ x : F.Γ → GG n C', ∀ a, x a = ⟨D.r a, F.del a⟩ := ⟨_, fun _ => rfl⟩
  have hW : ∀ a b, x a * x b * (x (a * b))⁻¹ =
      GG.ofGL (D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹) := by
    intro a b
    rw [hx, hx, hx]
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
        SemidirectProduct.inv_right, SemidirectProduct.left_inl, GG.ofGL]
      rw [← MulAut.mul_apply, ← map_mul, map_mul F.del a b, mul_inv_cancel, map_one, MulAut.one_apply]
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.right_inl,
        GG.ofGL, map_mul, mul_inv_cancel, mul_one]
  have hz : ∀ a b, ((D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹ : GL (Fin n) C') :
      Matrix (Fin n) (Fin n) C') = 1 + D.om (a, b) := by
    intro a b
    simp [SetLift.om]
  have hbar : (B.bar O).r s = GG.map (res O C' : C' →+* ResidueField O) (x s) := by
    rw [hx]
    apply SemidirectProduct.ext
    · ext i j
      simp [Box.map, GG.map, ← D.r_map s, res_map]
    · simp [Box.map, GG.map, B.nu]
  have key : ∀ a b : GG n C', a.right = 1 → (a * b).mat = a.mat * b.mat := by
    intro a b ha
    simp only [GG.mat, SemidirectProduct.mul_left, ha, map_one, MulAut.one_apply, Units.val_mul]
  have hofr : ∀ w : GL (Fin n) C', (GG.ofGL w).right = 1 := fun w => rfl
  have hmat : ∀ w : GL (Fin n) C', (GG.ofGL w).mat = (w : Matrix (Fin n) (Fin n) C') := fun w => rfl
  have hW' : x s * x (t * r) * (x (s * t * r))⁻¹ =
      GG.ofGL (D.r s * sgnAct n C' (F.del s) (D.r (t * r)) * (D.r (s * (t * r)))⁻¹) := by
    rw [mul_assoc s t r]
    exact hW s (t * r)
  have h := grp_id (x s) (x t) (x r) (x (s * t)) (x (t * r)) (x (s * t * r))
  rw [hW s t, hW (s * t) r, hW t r, hW'] at h
  have hyr : (x s * GG.ofGL (D.r t * sgnAct n C' (F.del t) (D.r r) * (D.r (t * r))⁻¹) * (x s)⁻¹).right
      = 1 := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, GG.ofGL,
      SemidirectProduct.right_inl, mul_one, mul_inv_cancel]
  have hM := congrArg GG.mat h
  rw [key _ _ (hofr _), key _ _ hyr, hmat, hmat, hmat] at hM
  obtain ⟨-, -, hE3⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (t, r)) (hom (t, r))
  obtain ⟨hAK, hAmap, hconj⟩ := hE3 (x s)
  rw [hconj _ (hz t r), hz s t, hz (s * t) r, hz s (t * r)] at hM
  obtain ⟨h1, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (s, t)) (hom (s, t))
  obtain ⟨h12, h12add, -⟩ := h1 (D.om (s * t, r)) (hom _)
  obtain ⟨hA, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm ((x s).adFun (D.om (t, r))) hAK
  obtain ⟨hA4, hA4add, -⟩ := hA (D.om (s, t * r)) (hom _)
  have hsum : D.om (s, t) + D.om (s * t, r) = (x s).adFun (D.om (t, r)) + D.om (s, t * r) := by
    have e1 : (1 + D.om (s, t)) * (1 + D.om (s * t, r)) = 1 + (D.om (s, t) + D.om (s * t, r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, h12]
      abel
    have e2 : (1 + (x s).adFun (D.om (t, r))) * (1 + D.om (s, t * r)) =
        1 + ((x s).adFun (D.om (t, r)) + D.om (s, t * r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, hA4]
      abel
    rw [e1, e2] at hM
    exact add_left_cancel hM
  change ((B.bar O).r s).adFun ((D.om (t, r)).map (evK (RingHom.ker p) u)) +
      (D.om (s, t * r)).map (evK (RingHom.ker p) u) =
      (D.om (s * t, r)).map (evK (RingHom.ker p) u) + (D.om (s, t)).map (evK (RingHom.ker p) u)
  rw [hbar, ← hAmap, ← hA4add, add_comm ((D.om (s * t, r)).map _), ← h12add, hsum]
