import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneAd

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.Mix

theorem PositivityTheory.Mix.unitary_fixing_isotropic_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), B.IsGood σ → H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ u : UA σ X.J, mat u *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      ∀ (m m' : UA σ X.J) (t : ℕ),
      mat m *ᵥ incV F H.x = (2 : AE F E) • incV F H.x → (2 : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      mat m' *ᵥ incV F H.x = (t : AE F E) • incV F H.x → (t : AE F E) • (mat m' *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → AE F E, mat m' *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) * m'⁻¹ = (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hH hX hX₁ u hux huι m m' t hmx hmy hmι hm'x hm'y hm'ι
  obtain ⟨ε, hP⟩ := planeOK_herm hB hH hX
  obtain ⟨cc, ee, ce, herm, xx, yy, xy, ix, iy, span, nd⟩ := hP
  set vx := incV F H.x with hvx
  set vy := incV F H.y with hvy
  set ιM := incM F H.ι with hιM
  set c := (cA σ).toRingHom with hc
  set J := incM F X.J with hJ
  have hact : ∀ (g h : UA σ X.J) (v : Fin n → AE F E), mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
    intro g h v
    rw [Matrix.mulVec_mulVec]
    rfl
  have hinv : ∀ (g : UA σ X.J) (v : Fin n → AE F E), mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
    intro g v
    rw [← hact, inv_mul_cancel]
    exact Matrix.one_mulVec v
  have hinv' : ∀ (g : UA σ X.J) (v w : Fin n → AE F E), mat g *ᵥ w = v → mat g⁻¹ *ᵥ v = w := by
    intro g v w h
    rw [← h, hinv]
  have h2 : IsUnit (2 : AE F E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AE F E))
    rwa [map_ofNat] at this
  choose a ha using huι
  obtain ⟨s₀, r₀, z₀, huy⟩ := span (mat u *ᵥ vy)
  have hpres : ∀ v w, bf c J (mat u *ᵥ v) (mat u *ᵥ w) = bf c J v w := by
    intro v w
    have hU : (mat u)ᵀ * J * (mat u).map c = J := u.2
    have e1 : (fun i => c ((mat u *ᵥ w) i)) = (mat u).map c *ᵥ (fun i => c (w i)) := by
      funext i
      exact RingHom.map_mulVec c (mat u) w i
    unfold PositivityTheory.Mix.bf
    rw [e1, ← Matrix.vecMul_transpose (mat u) v, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hU]
  have hsym : ∀ v w, c (bf c J v w) = ε * bf c J w v := by
    intro v w
    simp only [PositivityTheory.Mix.bf, dotProduct, Matrix.mulVec, map_sum, map_mul, cc, herm, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hyx : bf c J vy vx = ε := by
    have h := hsym vx vy
    rw [xy, map_one] at h
    calc bf c J vy vx = ε * (ε * bf c J vy vx) := by rw [← mul_assoc, ee, one_mul]
      _ = ε := by rw [← h, mul_one]
  have hlin : ∀ (p q : AE F E) (v₁ v₂ v₃ w : Fin n → AE F E),
      bf c J (p • v₁ + v₂ + q • v₃) w = p * bf c J v₁ w + bf c J v₂ w + q * bf c J v₃ w := by
    intro p q v₁ v₂ v₃ w
    simp only [PositivityTheory.Mix.bf, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hr : r₀ = 1 := by
    have h1 := hpres vy vx
    rw [hux, huy, hlin, xx, ix, hyx] at h1
    have h1' : r₀ * ε = ε := by simpa using h1
    calc r₀ = r₀ * ε * ε := by rw [mul_assoc, ee, mul_one]
      _ = 1 := by rw [h1', ee]
  have hUix : mat u⁻¹ *ᵥ vx = vx := hinv' u vx vx hux
  have hUiι : ∀ z, mat u⁻¹ *ᵥ (ιM *ᵥ z) = ιM *ᵥ z - a z • vx := by
    intro z
    apply hinv'
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha, hux]
    abel
  have hUiy : mat u⁻¹ *ᵥ vy = vy - s₀ • vx - ιM *ᵥ z₀ + a z₀ • vx := by
    apply hinv'
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, huy, hr, ha, hux, one_smul]
    abel
  set Am := mat (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) with hAm
  have hAact : ∀ v, Am *ᵥ v = mat u⁻¹ *ᵥ (mat u⁻¹ *ᵥ (mat m *ᵥ (mat u *ᵥ (mat m⁻¹ *ᵥ v)))) := by
    intro v
    rw [hAm]
    simp only [hact]
  have hAx : Am *ᵥ vx = vx := by
    have h : Am *ᵥ (mat m *ᵥ vx) = mat m *ᵥ vx := by
      rw [hAact, hinv m, hux, hmx, Matrix.mulVec_smul, Matrix.mulVec_smul, hUix, hUix]
    rw [hmx, Matrix.mulVec_smul] at h
    exact h2.smul_left_cancel.1 h
  have hAι : ∀ z, Am *ᵥ (ιM *ᵥ z) = ιM *ᵥ z := by
    intro z
    have h : Am *ᵥ (mat m *ᵥ (ιM *ᵥ z)) = ιM *ᵥ z := by
      rw [hAact, hinv m, ha, Matrix.mulVec_add, hmι, Matrix.mulVec_smul, hmx]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hUiι, hUix]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rwa [hmι] at h
  set c₀ := 2 * s₀ - a z₀ with hc₀
  have hAy : Am *ᵥ vy = vy + c₀ • vx := by
    have e : Am *ᵥ vy = (2 : AE F E) • (mat u⁻¹ *ᵥ (mat u⁻¹ *ᵥ (mat m *ᵥ (mat u *ᵥ vy)))) := by
      conv_lhs => rw [← hmy, Matrix.mulVec_smul, hAact, hinv m]
    have e2 : (2 : AE F E) • (mat m *ᵥ (mat u *ᵥ vy)) = (2 * s₀ * 2) • vx + (2 : AE F E) • (ιM *ᵥ z₀) + vy := by
      simp only [huy, hr, Matrix.mulVec_add, Matrix.mulVec_smul, hmx, hmι, one_smul, smul_add, hmy]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, e2]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hUiι, hUix, hUiy]
    rw [hc₀]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  by_cases ht0 : t = 0
  · subst ht0
    have hy0 : vy = 0 := by simpa using hm'y.symm
    have h01 : (0 : AE F E) = 1 := by
      rw [← xy, hy0]
      unfold PositivityTheory.Mix.bf
      simp only [Pi.zero_apply, map_zero]
      rw [show (fun _ : Fin n => (0 : AE F E)) = 0 from rfl, Matrix.mulVec_zero, dotProduct_zero]
    haveI : Subsingleton (AE F E) := subsingleton_of_zero_eq_one h01
    apply matH_inj (σ := σ) X.J
    ext i j
    exact Subsingleton.elim _ _
  have ht : IsUnit (t : AE F E) := by
    have := (IsUnit.mk0 (t : F) (Nat.cast_ne_zero.2 ht0)).map (algebraMap F (AE F E))
    rwa [map_natCast] at this
  have hpow : ∀ k : ℕ, Am ^ k *ᵥ vx = vx ∧ (∀ w, Am ^ k *ᵥ (ιM *ᵥ w) = ιM *ᵥ w) ∧
      Am ^ k *ᵥ vy = vy + ((k : AE F E) * c₀) • vx := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨h1, h2', h3⟩ := ih
      refine ⟨?_, fun w => ?_, ?_⟩
      · rw [pow_succ, ← Matrix.mulVec_mulVec, hAx, h1]
      · rw [pow_succ, ← Matrix.mulVec_mulVec, hAι, h2']
      · rw [pow_succ, ← Matrix.mulVec_mulVec, hAy, Matrix.mulVec_add, Matrix.mulVec_smul, h3, h1]
        push_cast
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
  have hext : ∀ P Q : Matrix (Fin n) (Fin n) (AE F E), (∀ v, P *ᵥ v = Q *ᵥ v) → P = Q := by
    intro P Q h
    ext i j
    simpa using congrFun (h (Pi.single j 1)) i
  have key : mat m' * Am = Am ^ (t ^ 2) * mat m' := by
    apply hext
    intro v
    obtain ⟨p, q, w, hv⟩ := span v
    have ex : (mat m' * Am) *ᵥ vx = (Am ^ (t ^ 2) * mat m') *ᵥ vx := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAx, hm'x, Matrix.mulVec_smul, (hpow _).1]
    have eι : (mat m' * Am) *ᵥ (ιM *ᵥ w) = (Am ^ (t ^ 2) * mat m') *ᵥ (ιM *ᵥ w) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAι, hm'ι, (hpow _).2.1]
    have ey : (mat m' * Am) *ᵥ vy = (Am ^ (t ^ 2) * mat m') *ᵥ vy := by
      have hL : (t : AE F E) • ((mat m' * Am) *ᵥ vy) = vy + ((t : AE F E) * t * c₀) • vx := by
        rw [← Matrix.mulVec_mulVec, hAy, Matrix.mulVec_add, Matrix.mulVec_smul, hm'x, smul_add, hm'y]
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hR : (t : AE F E) • ((Am ^ (t ^ 2) * mat m') *ᵥ vy) = vy + ((t : AE F E) * t * c₀) • vx := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hm'y, (hpow _).2.2]
        congr 2
        push_cast
        ring
      exact ht.smul_left_cancel.1 (hL.trans hR.symm)
    rw [hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ex, eι, ey]
  rw [mul_inv_eq_iff_eq_mul]
  apply matH_inj (σ := σ) X.J
  calc matH σ X.J (m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹))) = mat m' * Am := map_mul _ _ _
    _ = Am ^ (t ^ 2) * mat m' := key
    _ = matH σ X.J ((u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) * m') := by
      rw [map_mul, map_pow]
      rfl
