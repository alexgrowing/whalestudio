import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKA

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_smul {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (r : R) (M : Matrix m p R) :
    cj s (r • M) = s r • cj s M := by
  ext i j; simp [cj]

theorem map_cj {R S : Type} [CommRing R] [CommRing S] (σ : R →+* R) (s : S →+* S) (π : R →+* S)
    (h : ∀ x, π (σ x) = s (π x)) {m p : Type} (M : Matrix m p R) : (cj σ M).map π = cj s (M.map π) := by
  ext i j; simp [cj, h]

theorem det_jacobi {R : Type} [CommRing R] (σ : R →+* R) (a b0 c d b : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (hb : cj σ b = b) :
    (fromBlocks a (a * b + b0) c (d + c * b)).det * (cj σ (d + c * b)).det = (d + c * b).det := by
  have hu : cj σ (d + c * b) = cj σ d + b * cj σ c := by rw [cj_add, cj_mul, hb]
  have e : fromBlocks a (a * b + b0) c (d + c * b) * fromBlocks (cj σ (d + c * b)) 0 (-cj σ c) 1 =
      fromBlocks 1 (a * b + b0) 0 (d + c * b) := by
    rw [fromBlocks_multiply, hu]
    congr 1
    · rw [← R1]; noncomm_ring
    · simp
    · calc c * (cj σ d + b * cj σ c) + (d + c * b) * -cj σ c = c * cj σ d - d * cj σ c := by noncomm_ring
        _ = 0 := by rw [R2, sub_self]
    · simp
  have := congrArg Matrix.det e
  rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] at this
  simpa using this

theorem core {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔭 : Ideal R) [h𝔭 : 𝔭.IsMaximal]
    (h2 : IsUnit (2 : R)) (hU : ∀ x, x ∉ 𝔭 → σ x ∉ 𝔭 → IsUnit x) (a b0 c d : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (R3 : d * cj σ a - c * cj σ b0 = 1) :
    ∃ b : Matrix n n R, cj σ b = b ∧ IsUnit (d + c * b).det := by
  letI : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  set π : R →+* R ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  set lift : R ⧸ 𝔭 → R := Function.surjInv hsurj with hlift
  have hl : ∀ y, π (lift y) = y := Function.surjInv_eq hsurj
  have hXY : c * (-cj σ b0) + d * cj σ a = 1 := by rw [← R3]; noncomm_ring
  have hXY' : c.map π * (-cj σ b0).map π + d.map π * (cj σ a).map π = 1 := by
    have := congrArg π.mapMatrix hXY
    simpa only [map_add, map_mul, map_one, RingHom.mapMatrix_apply] using this
  have key : ∃ b : Matrix n n R, cj σ b = b ∧ (d + c * b).det ∉ 𝔭 := by
    have hdet : ∀ b : Matrix n n R, ((d + c * b).map π).det ≠ 0 → (d + c * b).det ∉ 𝔭 := by
      intro b hb hm
      apply hb
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hm
      rw [← hm, RingHom.map_det]; rfl
    by_cases hst : ∀ x ∈ 𝔭, σ x ∈ 𝔭
    · set s : R ⧸ 𝔭 →+* R ⧸ 𝔭 := Ideal.quotientMap 𝔭 σ (fun x hx => hst x hx) with hs
      have hsπ : ∀ x, π (σ x) = s (π x) := fun x => (Ideal.quotientMap_mk).symm
      have hss : ∀ y, s (s y) = y := by
        intro y; obtain ⟨x, rfl⟩ := hsurj y; rw [← hsπ, ← hsπ, hσ]
      have hlag : c.map π * cj s (d.map π) = d.map π * cj s (c.map π) := by
        rw [← map_cj σ s π hsπ, ← map_cj σ s π hsπ]
        have := congrArg π.mapMatrix R2
        simpa only [map_mul, RingHom.mapMatrix_apply] using this
      obtain ⟨B, hBh, hBd⟩ := fieldA s hss _ _ _ _ hXY' hlag
      set B' := B.map lift with hB'
      refine ⟨(↑h2.unit⁻¹ : R) • (B' + cj σ B'), ?_, hdet _ ?_⟩
      · have hinv : σ (↑h2.unit⁻¹ : R) = ↑h2.unit⁻¹ := by
          have e1 : σ (↑h2.unit⁻¹ : R) * 2 = 1 := by
            have : σ ((↑h2.unit⁻¹ : R) * 2) = 1 := by
              rw [show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl, Units.inv_mul, map_one]
            rwa [map_mul, map_ofNat] at this
          calc σ (↑h2.unit⁻¹ : R) = σ (↑h2.unit⁻¹ : R) * (2 * ↑h2.unit⁻¹) := by
                rw [show (2 : R) * ↑h2.unit⁻¹ = ↑h2.unit * ↑h2.unit⁻¹ from rfl, Units.mul_inv, mul_one]
            _ = ↑h2.unit⁻¹ := by rw [← mul_assoc, e1, one_mul]
        rw [cj_smul, cj_add, cj_cj σ hσ, hinv, add_comm]
      · have hmap : ((↑h2.unit⁻¹ : R) • (B' + cj σ B')).map π = B := by
          ext i j
          have hij := congrFun (congrFun hBh i) j
          rw [cj_apply] at hij
          have h2π : π (↑h2.unit⁻¹ : R) * 2 = 1 := by
            rw [← map_ofNat π 2, ← map_mul, show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl,
              Units.inv_mul, map_one]
          simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_mul, map_add, cj_apply,
            hB', hsπ, hl, hij]
          linear_combination (B i j) * h2π
        have : (d + c * ((↑h2.unit⁻¹ : R) • (B' + cj σ B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add, Matrix.map_mul]
        rw [this]; exact hBd
    · push_neg at hst
      obtain ⟨y, hy, hσy⟩ := hst
      obtain ⟨r, i, hi, hri⟩ := h𝔭.exists_inv hσy
      obtain ⟨B, hBd⟩ := fieldB _ _ _ _ hXY'
      set B' := B.map lift with hB'
      set x := r * σ y with hx
      have hπx : π x = 1 := by
        have : π (x + i) = 1 := by rw [hx, hri, map_one]
        rwa [map_add, (Ideal.Quotient.eq_zero_iff_mem).2 hi, add_zero] at this
      have hπσx : π (σ x) = 0 := by
        rw [hx, map_mul, hσ, map_mul, (Ideal.Quotient.eq_zero_iff_mem).2 hy, mul_zero]
      refine ⟨x • B' + cj σ (x • B'), ?_, hdet _ ?_⟩
      · rw [cj_add, cj_cj σ hσ, add_comm]
      · have hmap : (x • B' + cj σ (x • B')).map π = B := by
          ext i j
          simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cj_apply, map_add, map_mul,
            hπx, hπσx, hB', hl]
          ring
        have : (d + c * (x • B' + cj σ (x • B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add, Matrix.map_mul]
        rw [this]; exact hBd
  obtain ⟨b, hb, hb𝔭⟩ := key
  refine ⟨b, hb, hU _ hb𝔭 fun hσ𝔭 => hb𝔭 ?_⟩
  rw [← det_jacobi σ a b0 c d b R1 R2 hb, det_cj]
  exact Ideal.mul_mem_left _ _ hσ𝔭

end PositivityTheory.Rg.Rsw.L.LGenK
