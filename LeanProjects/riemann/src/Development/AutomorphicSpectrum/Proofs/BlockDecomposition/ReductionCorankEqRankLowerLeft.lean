import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedRank

theorem rank_add_rank_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ} {ϖ : O}
    (hϖ : Irreducible ϖ) (d E : Matrix (Fin n) (Fin n) O) (hdE : d * E = ϖ • (1 : Matrix (Fin n) (Fin n) O))
    (hEd : E * d = ϖ • (1 : Matrix (Fin n) (Fin n) O)) :
    (d.map (IsLocalRing.residue O)).rank + (E.map (IsLocalRing.residue O)).rank = n := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self ϖ
  have hzero : d.map (IsLocalRing.residue O) * E.map (IsLocalRing.residue O) = 0 := by
    rw [← Matrix.map_mul, hdE]
    ext i j
    simp [hres]
  have hker : LinearMap.ker (d.map (IsLocalRing.residue O)).mulVecLin =
      LinearMap.range (E.map (IsLocalRing.residue O)).mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : (d.map (IsLocalRing.residue O)) *ᵥ x = 0 := by simpa using hx
      choose x₀ hx₀ using fun i => IsLocalRing.residue_surjective (x i)
      have hxc : (IsLocalRing.residue O) ∘ x₀ = x := funext hx₀
      have hmem : ∀ i, ∃ y : O, y * ϖ = (d *ᵥ x₀) i := by
        intro i
        have h0 : IsLocalRing.residue O ((d *ᵥ x₀) i) = 0 := by
          rw [RingHom.map_mulVec, hxc, hx']
          rfl
        rw [IsLocalRing.residue_eq_zero_iff, hmax] at h0
        exact Ideal.mem_span_singleton'.1 h0
      choose y hy using hmem
      have hdx : d *ᵥ x₀ = ϖ • y := by
        ext i
        simp [← hy i, mul_comm]
      have hEx : ϖ • x₀ = ϖ • (E *ᵥ y) := by
        have h1 : E *ᵥ (d *ᵥ x₀) = ϖ • x₀ := by
          rw [Matrix.mulVec_mulVec, hEd, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [← h1, hdx, Matrix.mulVec_smul]
      have hxE : x₀ = E *ᵥ y := smul_right_injective _ hϖ.ne_zero hEx
      refine ⟨(IsLocalRing.residue O) ∘ y, ?_⟩
      ext i
      simp only [Matrix.mulVecLin_apply]
      rw [← RingHom.map_mulVec, ← hxE]
      exact hx₀ i
    · rintro ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hzero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (d.map (IsLocalRing.residue O)).mulVecLin
  rw [hker] at hrn
  simpa [Matrix.rank] using hrn

theorem low_rows {R : Type} [CommRing R] {n : ℕ} (g : GL (Ix n) R) :
    lowerLeftBlock g * (g⁻¹).1.toBlocks₁₂ + dBlk g * (g⁻¹).1.toBlocks₂₂ = 1 := by
  have h : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul]; simp
  have e : fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂ *
      fromBlocks (g⁻¹).1.toBlocks₁₁ (g⁻¹).1.toBlocks₁₂ (g⁻¹).1.toBlocks₂₁ (g⁻¹).1.toBlocks₂₂ = 1 := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, ← fromBlocks_one] at e
  exact (Matrix.fromBlocks_inj.1 e).2.2.2

theorem scM_val {L : Type} [Field L] {n : ℕ} (w : Lˣ) : (scM (n := n) w).1 = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
  ext i j
  simp [scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem low_eq {L : Type} [Field L] {n : ℕ} (x : L) (X Y : Matrix (Ix n) (Ix n) L) (a b d : Matrix (Fin n) (Fin n) L)
    (h : X * fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) = fromBlocks a b 0 d * Y) :
    X.toBlocks₂₁ = d * Y.toBlocks₂₁ ∧ x • X.toBlocks₂₂ = d * Y.toBlocks₂₂ := by
  have e : fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂ *
        fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) =
      fromBlocks a b 0 d * fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, fromBlocks_multiply] at e
  obtain ⟨-, -, h3, h4⟩ := Matrix.fromBlocks_inj.1 e
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.zero_mul, Matrix.mul_smul] at h3 h4
  exact ⟨h3, h4⟩

theorem exists_integral {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (hι : Function.Injective ι) {n : ℕ} (ϖ : O)
    (C D C' D' Bi Di Bi' Di' : Matrix (Fin n) (Fin n) O) (h1 : C * Bi + D * Di = 1) (h2 : C' * Bi' + D' * Di' = 1)
    (dL dLi : Matrix (Fin n) (Fin n) L) (hd : dL * dLi = 1) (hd' : dLi * dL = 1)
    (hC : C.map ι = dL * C'.map ι) (hD : ι ϖ • D.map ι = dL * D'.map ι) :
    (C * Bi' + ϖ • (D * Di')) * (ϖ • (C' * Bi) + D' * Di) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    (ϖ • (C' * Bi) + D' * Di) * (C * Bi' + ϖ • (D * Di')) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    C = (C * Bi' + ϖ • (D * Di')) * C' ∧ (ϖ • (C' * Bi) + D' * Di) * D = D' := by
  have hinj : Function.Injective (ι.mapMatrix (m := Fin n)) := fun A B h => by
    ext i j
    exact hι (congrFun (congrFun h i) j)
  have hs : ∀ M : Matrix (Fin n) (Fin n) O, ι.mapMatrix (ϖ • M) = ι ϖ • ι.mapMatrix M := by
    intro M; ext i j; simp
  have hC' : ι.mapMatrix C = dL * ι.mapMatrix C' := hC
  have hD' : ι ϖ • ι.mapMatrix D = dL * ι.mapMatrix D' := hD
  have h1' : ι.mapMatrix C * ι.mapMatrix Bi + ι.mapMatrix D * ι.mapMatrix Di = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, h1, map_one]
  have h2' : ι.mapMatrix C' * ι.mapMatrix Bi' + ι.mapMatrix D' * ι.mapMatrix Di' = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, h2, map_one]
  have hCi : ι.mapMatrix C' = dLi * ι.mapMatrix C := by
    rw [hC', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hDi : ι.mapMatrix D' = ι ϖ • (dLi * ι.mapMatrix D) := by
    rw [← Matrix.mul_smul, hD', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hF : ι.mapMatrix (C * Bi' + ϖ • (D * Di')) = dL := by
    rw [map_add, hs, map_mul, map_mul, hC', ← Matrix.smul_mul, hD', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
      h2', Matrix.mul_one]
  have hG : ι.mapMatrix (ϖ • (C' * Bi) + D' * Di) = ι ϖ • dLi := by
    rw [map_add, hs, map_mul, map_mul, hCi, hDi, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← smul_add,
      ← Matrix.mul_add, h1', Matrix.mul_one]
  refine ⟨hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩
  · rw [map_mul, hF, hG, hs, map_one, Matrix.mul_smul, hd]
  · rw [map_mul, hF, hG, hs, map_one, Matrix.smul_mul, hd']
  · rw [map_mul, hF, hC']
  · rw [map_mul, hG, Matrix.smul_mul, hDi]

theorem iD_eq_rank : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw κ h hred
  obtain ⟨a, d, b, κ', hEq, rfl⟩ := hred
  have hv := congrArg Units.val hEq
  have hlow := low_eq (w : L) (κ.1.map (algebraMap O L)) (κ'.1.map (algebraMap O L)) a.1 b d.1 (by
    have : (tauM (n := n) w).1 = fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
      simp [tauM, pM, scM_val]
    rw [← this]
    exact hv)
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨e1, e2, e3, e4⟩ := exists_integral (algebraMap O L) (IsFractionRing.injective O L) ϖ
    (lowerLeftBlock κ) (dBlk κ) (lowerLeftBlock κ') (dBlk κ') (κ⁻¹).1.toBlocks₁₂ (κ⁻¹).1.toBlocks₂₂ (κ'⁻¹).1.toBlocks₁₂ (κ'⁻¹).1.toBlocks₂₂
    (low_rows κ) (low_rows κ') d.1 (d⁻¹).1 (by rw [← Units.val_mul]; simp) (by rw [← Units.val_mul]; simp)
    hlow.1 (by rw [← hw]; exact hlow.2)
  have hn := rank_add_rank_eq hϖ _ _ e1 e2
  set R := (IsLocalRing.residue O).mapMatrix (m := Fin n) with hR
  have hsz : ∀ M : Matrix (Fin n) (Fin n) O, R (ϖ • M) = 0 := by
    intro M; ext i j; simp [hR, hres]
  have hd0 : (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) =
      R (lowerLeftBlock κ) * R (κ'⁻¹).1.toBlocks₁₂ := by
    change R _ = _
    rw [map_add, hsz, add_zero, map_mul]
  have hE0 : (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) =
      R (dBlk κ') * R (κ⁻¹).1.toBlocks₂₂ := by
    change R _ = _
    rw [map_add, hsz, zero_add, map_mul]
  have r1 : ((lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O)).rank
      = (R (lowerLeftBlock κ)).rank := by
    apply le_antisymm
    · rw [hd0]; exact Matrix.rank_mul_le_left _ _
    · have : R (lowerLeftBlock κ) = (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) *
          R (lowerLeftBlock κ') := by
        conv_lhs => rw [e3]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  have r2 : ((ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O)).rank
      = (R (dBlk κ')).rank := by
    apply le_antisymm
    · rw [hE0]; exact Matrix.rank_mul_le_left _ _
    · have : R (dBlk κ') = (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) *
          R (dBlk κ) := by
        conv_lhs => rw [← e4]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  rw [r1, r2] at hn
  have hc : lowerLeftBlock (resK κ) = R (lowerLeftBlock κ) := rfl
  have hdd : dBlk (resK κ') = R (dBlk κ') := rfl
  unfold iD
  rw [hc, hdd]
  omega

end GlobalTheory.CompanionTheory.Jp.RedRank

end
