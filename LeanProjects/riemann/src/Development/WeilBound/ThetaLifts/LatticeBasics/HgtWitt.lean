import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasIwasawaOfFrame

noncomputable section

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.CompanionTheory.IwaDbl.FrameCore GlobalTheory.CompanionTheory.WittOrbit GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.Hgt

section Generic

variable {S : Type} [CommRing S] {c : S →ₐ[ℤ] S} {A : Subring S} {ε : S}

theorem form_star' {l m n : Type} [Fintype m] (hc : ∀ z, c (c z) = z) {H : Matrix m m S} (hH : (H.map c)ᵀ = ε • H)
    (X : Matrix m l S) (Y : Matrix m n S) : ((Xᵀ * H * Y.map c).map c)ᵀ = ε • (Yᵀ * H * X.map c) := by
  rw [map_mul', map_mul', map_map_eq hc, transpose_mul, transpose_mul, hH, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
  rfl

theorem exists_partner' {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (hc : ∀ z, c (c z) = z)
    (hε : IsUnit ε) (hs : ∀ z ∈ A, c z ∈ A) {w : S} (hw : w ∈ A) (htr : w + c w = 1) {H H' : Matrix m m S}
    (hH : (H.map c)ᵀ = ε • H) (hHA : ∀ i j, H i j ∈ A) (hH'A : ∀ i j, H' i j ∈ A) (hHH : H * H' = 1) {J J' : Matrix n n S}
    (hJ : (J.map c)ᵀ = ε • J) (hJA : ∀ i j, J i j ∈ A) (hJ'A : ∀ i j, J' i j ∈ A) (hJJ : J * J' = 1) {C : Matrix m n S}
    {N : Matrix n m S} (hCA : ∀ i j, C i j ∈ A) (hNA : ∀ i j, N i j ∈ A) (hN : N * C = 1) (hC : Cᵀ * H * C.map c = 0) :
    ∃ D : Matrix m n S, (∀ i j, D i j ∈ A) ∧ Cᵀ * H * D.map c = J ∧ Dᵀ * H * C.map c = J ∧ Dᵀ * H * D.map c = 0 := by
  have can : ∀ {X Y : Matrix n n S}, ε • X = ε • Y → X = Y := fun h => (hε.smul_left_cancel).1 h
  obtain ⟨D₁, hD₁A, h1⟩ : ∃ D₁ : Matrix m n S, (∀ i j, D₁ i j ∈ A) ∧ Cᵀ * H * D₁.map c = J := by
    refine ⟨(H' * Nᵀ * J).map c, int_map hs (int_mul (int_mul hH'A fun i j => hNA j i) hJA), ?_⟩
    rw [map_map_eq hc]
    calc Cᵀ * H * (H' * Nᵀ * J) = Cᵀ * (H * H') * Nᵀ * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hHH, Matrix.mul_one, ← transpose_mul, hN, transpose_one, Matrix.one_mul]
  have h2 : D₁ᵀ * H * C.map c = J := can (by rw [← form_star' hc hH, h1, hJ])
  set G := D₁ᵀ * H * D₁.map c with hG
  have hGA : ∀ i j, G i j ∈ A := int_mul (int_mul (fun i j => hD₁A j i) hHA) (int_map hs hD₁A)
  have hGs : (G.map c)ᵀ = ε • G := form_star' hc hH _ _
  obtain ⟨T, hTA, hT⟩ : ∃ T : Matrix n n S, (∀ i j, T i j ∈ A) ∧ J * T.map c = w • G := by
    refine ⟨(w • (J' * G)).map c, int_map hs fun i j => mul_mem hw (int_mul hJ'A hGA i j), ?_⟩
    rw [map_map_eq hc, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hT' : Tᵀ * J = c w • G := can (by
    have := congrArg (fun X : Matrix n n S => (X.map c)ᵀ) hT
    simp only [map_mul', map_map_eq hc, transpose_mul, hJ, Matrix.mul_smul] at this
    rw [this, smul_comm, ← hGs]
    ext i j; simp)
  have hm : (D₁ - C * T).map c = D₁.map c - C.map c * T.map c := by
    rw [← map_mul']; ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have h3 : Cᵀ * H * (D₁ - C * T).map c = J := by
    rw [hm, Matrix.mul_sub, h1, ← Matrix.mul_assoc, hC, Matrix.zero_mul, sub_zero]
  refine ⟨D₁ - C * T, fun i j => sub_mem (hD₁A i j) (int_mul hCA hTA i j), h3, can ?_, ?_⟩
  · rw [← form_star' hc hH, h3, hJ]
  · rw [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc Tᵀ, Matrix.mul_assoc Tᵀ, h3, hT', hm,
      Matrix.mul_sub, ← Matrix.mul_assoc, h2, hT, ← hG, sub_sub, ← add_smul, htr, one_smul, sub_self]

variable {β : Type} [Fintype β] [DecidableEq β]

theorem exists_int_iso (hc : ∀ z, c (c z) = z) (hε : IsUnit ε) (hs : ∀ z ∈ A, c z ∈ A) {w₀ : S} (hw : w₀ ∈ A)
    (htr : w₀ + c w₀ = 1) {J J' : Matrix β β S} (hJ : (J.map c)ᵀ = ε • J) (hJA : ∀ i j, J i j ∈ A) (hJ'A : ∀ i j, J' i j ∈ A)
    (hJJ : J * J' = 1) {C : Matrix (β ⊕ β) β S} {N : Matrix β (β ⊕ β) S} (hCA : ∀ i j, C i j ∈ A) (hNA : ∀ i j, N i j ∈ A)
    (hN : N * C = 1) (hC : Cᵀ * dbl J * C.map c = 0) :
    ∃ k : GL (β ⊕ β) S, k.1ᵀ * dbl J * k.1.map c = dbl J ∧ (∀ i j, k.1 i j ∈ A) ∧ (∀ i j, (k⁻¹).1 i j ∈ A) ∧
      k.1 * diagCols β = C := by
  have hdA : ∀ {X : Matrix β β S}, (∀ i j, X i j ∈ A) → ∀ i j, dbl X i j ∈ A := by
    rintro X hX (i | i) (j | j)
    · exact hX i j
    · exact zero_mem _
    · exact zero_mem _
    · exact neg_mem (hX i j)
  have hJ1 : ∀ i j, c (J j i) = ε * J i j := fun i j => congrFun (congrFun hJ i) j
  have hH : ((dbl J).map c)ᵀ = ε • dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, hJ1]
  have hHH : dbl J * dbl J' = 1 := by
    simp [dbl, fromBlocks_multiply, hJJ]
  obtain ⟨X, hXA, h1, h2, h3⟩ := exists_partner' hc hε hs hw htr hH (hdA hJA) (hdA hJ'A) hHH hJ hJA hJ'A hJJ hCA hNA hN hC
  set K : Matrix (β ⊕ β) (β ⊕ β) S := fromCols (c w₀ • C + X) (w₀ • C - X) with hK
  have hKA : ∀ i j, K i j ∈ A := by
    rintro i (j | j)
    · exact add_mem (mul_mem (hs _ hw) (hCA i j)) (hXA i j)
    · exact sub_mem (mul_mem hw (hCA i j)) (hXA i j)
  have hKm : K.map c = fromCols (w₀ • C.map c + X.map c) (c w₀ • C.map c - X.map c) := by
    ext i (j | j) <;> simp [hK, hc]
  have hU : Kᵀ * dbl J * K.map c = dbl J := by
    rw [hKm, hK, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols]
    simp only [transpose_add, transpose_sub, transpose_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, hC, h1, h2, h3, smul_zero, zero_add, add_zero, zero_sub, sub_zero]
    have e : c w₀ = 1 - w₀ := by rw [← htr]; ring
    rw [e]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> module
  have hL : (dbl J' * Kᵀ * dbl J).map c * K = 1 := by
    have : dbl J' * Kᵀ * dbl J * K.map c = 1 := by
      rw [Matrix.mul_assoc (dbl J'), Matrix.mul_assoc (dbl J'), hU, mul_eq_one_comm.mp hHH]
    have := congrArg (fun Y : Matrix (β ⊕ β) (β ⊕ β) S => Y.map c) this
    simp only [map_mul' _ (K.map c), map_map_eq hc] at this
    rw [this]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  refine ⟨⟨K, (dbl J' * Kᵀ * dbl J).map c, mul_eq_one_comm.mp hL, hL⟩, hU, hKA, ?_, ?_⟩
  · exact int_map hs (int_mul (int_mul (hdA hJ'A) fun i j => hKA j i) (hdA hJA))
  · show K * diagCols β = C
    refine (fromCols_mul_fromRows _ _ _ _).trans ?_
    rw [Matrix.mul_one, Matrix.mul_one, add_add_sub_cancel, ← add_smul, add_comm, htr, one_smul]

omit [Fintype β] [DecidableEq β] in
theorem dbl_smul (l : S) (H : Matrix β β S) : dbl (l • H) = l • dbl H := by
  simp [dbl, fromBlocks_smul]

theorem lagr_orbit' (hc : ∀ z, c (c z) = z) (hs : ∀ z ∈ A, c z ∈ A) {w₀ : S} (hw : w₀ ∈ A)
    (htr : w₀ + c w₀ = 1) {H H' : Matrix β β S} (hH : (H.map c)ᵀ = H) (l : Sˣ) (hHA : ∀ i j, l.1 * H i j ∈ A)
    (hH'A : ∀ i j, H' i j ∈ A) (hHH : (l.1 • H) * H' = 1) (hS : HasSat A β) (y y' : Matrix (β ⊕ β) (β ⊕ β) S)
    (hyy : y' * y = 1) (hy : yᵀ * dbl H * y.map c = dbl H) :
    ∃ k : GL (β ⊕ β) S, k.1ᵀ * dbl H * k.1.map c = dbl H ∧ (∀ i j, k.1 i j ∈ A) ∧ (∀ i j, (k⁻¹).1 i j ∈ A) ∧
      ∃ t : Matrix β β S, k.1 * diagCols (E := S) β = y * diagCols (E := S) β * t := by
  have hN : ((Matrix.fromCols (1 : Matrix β β S) (0 : Matrix β β S) : Matrix β (β ⊕ β) S) * y') *
      (y * diagCols (E := S) β) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc y', hyy, Matrix.one_mul, diagCols, Matrix.fromCols_mul_fromRows]
    simp
  obtain ⟨t, t', D, M, -, h2, h3, h4, h5⟩ := hS _ _ hN
  have hN' : M.toRows₁ * (y * diagCols (E := S) β * t) = 1 := by
    rw [← fromRows_toRows M, fromRows_mul_fromCols, ← fromBlocks_one] at h5
    exact (fromBlocks_inj.mp h5).1
  obtain ⟨κ, k1, k2, k3, k4⟩ := exists_int_iso (ε := c l * (l⁻¹).1) (J := l.1 • H) hc ((l.isUnit.map c).mul (l⁻¹).isUnit) hs hw htr
    (by
      rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]
      conv_rhs => rw [← hH]
      ext i j; simp) hHA hH'A hHH h2 (N := M.toRows₁) (fun i j => h4 _ _) hN'
    (by
      rw [dbl_smul, Matrix.mul_smul, Matrix.smul_mul, map_mul', map_mul', Matrix.transpose_mul, Matrix.transpose_mul]
      calc _ = l.1 • (tᵀ * ((diagCols β : Matrix (β ⊕ β) β S)ᵀ * (yᵀ * dbl H * y.map c) *
            (diagCols β : Matrix (β ⊕ β) β S).map c) * t.map c) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hy, diagCols_isotropic, Matrix.mul_zero, Matrix.zero_mul, smul_zero])
  rw [dbl_smul, Matrix.mul_smul, Matrix.smul_mul] at k1
  exact ⟨κ, l.isUnit.smul_left_cancel.1 k1, k2, k3, t, k4⟩

end Generic

theorem hasIwasawa_of_frame' {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {n : ℕ}
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (hJ : ∀ i j, σ (J j i) = J i j) (A : Subring (R ⊗[F] E)) (w₀ : R ⊗[F] E)
    (hw : w₀ ∈ A) (htr : w₀ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ w₀ = 1) (hst : ∀ z ∈ A, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ z ∈ A)
    (b : GL (Fin n) (R ⊗[F] E)) (l : (R ⊗[F] E)ˣ) (hint : ∀ i j, l.1 * locGram σ J b i j ∈ A)
    (hinv : ∃ J' : Matrix (Fin n) (Fin n) (R ⊗[F] E), (∀ i j, J' i j ∈ A) ∧ J' * (l.1 • locGram σ J b) = 1)
    (hS : HasSat A (Fin n)) (K : Subgroup (HA R σ Q))
    (hK : ∀ k : HA R σ Q,
      (∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * matHom R σ Q k * blkGL finSumFinEquiv (b, b)).1 i j ∈ A) →
      (∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * (matHom R σ Q k)⁻¹ * blkGL finSumFinEquiv (b, b)).1 i j ∈ A) → k ∈ K) :
    HasIwasawa σ Q K := by
  intro g
  obtain ⟨J', hJ'A, hJJ'⟩ := hinv
  have hB := gram_blk (R := R) σ hQ b
  set B := blkGL finSumFinEquiv (b, b) with hBdef
  set J₀ := locGram σ J b with hJ₀
  set s := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ
  let ca : (R ⊗[F] E) →ₐ[ℤ] (R ⊗[F] E) := s.toIntAlgHom
  have hca : ∀ z, ca (ca z) = z := fun z => GlobalTheory.Doubling.sigR_invol hσ z
  have hherm := cT_locGram (R := R) σ hσ hJ b
  rw [← hJ₀] at hherm
  have hg : cT s ((matHom R σ Q g)⁻¹).1 * JR R Q * ((matHom R σ Q g)⁻¹).1 = JR R Q := (g⁻¹).2
  have hx := FrameCore.conj_iso s B hB hg
  set x := B⁻¹ * (matHom R σ Q g)⁻¹ * B with hxdef
  obtain ⟨κ, hκ0, hκ1, hκ2, t, hκ⟩ := lagr_orbit' (c := ca) (H := J₀ᵀ) (H' := J'ᵀ) hca hst hw htr
    (congrArg transpose hherm) l (fun i j => hint j i) (fun i j => hJ'A j i)
    (by rw [← transpose_smul, ← transpose_mul, hJJ', transpose_one]) hS
    (x.1.submatrix finSumFinEquiv finSumFinEquiv) ((x⁻¹).1.submatrix finSumFinEquiv finSumFinEquiv)
    (by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv])
    ((iso_iff s J₀ x.1).1 hx)
  set Y : GL (Fin (n + n)) (R ⊗[F] E) := reGL finSumFinEquiv κ with hYdef
  have hYs : Y.1.submatrix finSumFinEquiv finSumFinEquiv = κ.1 := by
    simp [hYdef, reGL]
  have hY : cT s Y.1 * dblGram finSumFinEquiv J₀ * Y.1 = dblGram finSumFinEquiv J₀ :=
    (iso_iff s J₀ Y.1).2 (by rw [hYs]; exact hκ0)
  have hk : B * Y * B⁻¹ ∈ HR R σ Q := by
    have := FrameCore.conj_iso s B⁻¹ (FrameCore.conj_back s B hB) hY
    rwa [inv_inv] at this
  let kk : HA R σ Q := ⟨B * Y * B⁻¹, hk⟩
  have hkm : matHom R σ Q kk = B * Y * B⁻¹ := rfl
  have h1 : B⁻¹ * matHom R σ Q kk * B = Y := by rw [hkm]; group
  have h2 : B⁻¹ * (matHom R σ Q kk)⁻¹ * B = Y⁻¹ := by rw [hkm]; group
  have hkK : kk ∈ K := hK kk (fun i j => by rw [h1]; exact hκ1 _ _) (fun i j => by rw [h2]; exact hκ2 _ _)
  refine ⟨⟨g * kk, ?_⟩, kk⁻¹, K.inv_mem hkK, (mul_inv_cancel_right g kk).symm⟩
  refine mem_siegelOf.2 ?_
  rw [map_mul, hkm]
  exact keepsDiag_of_frame (matHom R σ Q g) b Y t (by rw [hYs]; exact hκ)

end GlobalTheory.ThK.Dbl.Hgt

end
