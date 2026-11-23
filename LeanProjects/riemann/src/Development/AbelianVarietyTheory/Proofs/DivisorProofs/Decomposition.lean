import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open Matrix

namespace GlobalTheory.UnipotentCongruenceInverse

section Ring
variable {R M : Type} [CommRing R] [Ring M] [Algebra R M]

theorem cong_mul {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hy : (1 - e) • (y - 1) = 0) :
    (1 - e) • (x * y - 1) = 0 := by
  have h1 : x * y - 1 = (x - 1) * y + (y - 1) := by noncomm_ring
  rw [h1, smul_add, ← smul_mul_assoc, hx, zero_mul, zero_add, hy]

theorem cong_inv {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hxy : y * x = 1) :
    (1 - e) • (y - 1) = 0 := by
  have h1 : y - 1 = -(y * (x - 1)) := by rw [mul_sub, hxy, mul_one]; abel
  rw [h1, smul_neg, ← mul_smul_comm, hx, mul_zero, neg_zero]

theorem key {e : R} {k K h h' a b : M} (hKk : K * k = 1) (hh : h' * h = 1)
    (hK : (1 - e) • (K - 1) = 0) (hhe : (1 - e) • (h - 1) = 0)
    (ha : (1 - k) * a = e • (1 : M)) (hb : b * (1 - h') = e • (1 : M)) :
    (K - 1) * (1 - (b - a) * (h - 1)) = h - 1 := by

  have hu : e • (K - 1) = K - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hK; exact hK.symm
  have hv : e • (h - 1) = h - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hhe; exact hhe.symm
  have hua : (K - 1) * a = e • K := by
    have hK1 : K - 1 = K * (1 - k) := by rw [mul_sub, mul_one, hKk]
    rw [hK1, mul_assoc, ha, mul_smul_comm, mul_one]
  have hbv : b * (h - 1) = e • h := by
    have hh1 : h - 1 = (1 - h') * h := by rw [sub_mul, one_mul, hh]
    rw [hh1, ← mul_assoc, hb, smul_mul_assoc, one_mul]
  calc (K - 1) * (1 - (b - a) * (h - 1))
      = (K - 1) - (K - 1) * (b * (h - 1)) + ((K - 1) * a) * (h - 1) := by noncomm_ring
    _ = (K - 1) - (e • (K - 1)) * h + K * (e • (h - 1)) := by
        rw [hbv, hua]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = h - 1 := by rw [hu, hv]; noncomm_ring

end Ring

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {β : Type} [Fintype β] [DecidableEq β]

theorem cayley (c : A →ₐ[R] A) {J k a : Matrix β β A} {e : R} (hk : kᵀ * J * k.map c = J) (hea : e • a = a)
    (ha : (1 - k) * a = e • (1 : Matrix β β A)) (he : e * e = e) : aᵀ * J + J * a.map c = e • J := by
  have hT : aᵀ * (1 - k)ᵀ = e • (1 : Matrix β β A) := by
    rw [← transpose_mul, ha, transpose_smul, transpose_one]
  have hac : (1 - k.map c) * a.map c = e • (1 : Matrix β β A) := by
    have h1 := congrArg c.mapMatrix ha
    rwa [map_mul, map_sub, map_one, map_smul, map_one, AlgHom.mapMatrix_apply,
      AlgHom.mapMatrix_apply] at h1
  have heac : e • a.map c = a.map c := by
    have h1 := congrArg c.mapMatrix hea
    rwa [map_smul, AlgHom.mapMatrix_apply] at h1
  have heaT : e • aᵀ = aᵀ := by rw [← transpose_smul, hea]

  have hid : (1 - k)ᵀ * J * (1 - k.map c) = (1 - k)ᵀ * J + J * (1 - k.map c) := by
    rw [transpose_sub, transpose_one]
    have e1 : (1 - kᵀ) * J * (1 - k.map c)
        = (1 - kᵀ) * J + J * (1 - k.map c) + (kᵀ * J * k.map c - J) := by noncomm_ring
    rw [e1, hk, sub_self, add_zero]
  have main : aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c = e • J := by
    calc aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c
        = (aᵀ * (1 - k)ᵀ) * J * ((1 - k.map c) * a.map c) := by simp only [Matrix.mul_assoc]
      _ = e • J := by
          rw [hT, hac, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_one, smul_smul, he]
  have t1 : aᵀ * ((1 - k)ᵀ * J) * a.map c = J * a.map c := by
    rw [← Matrix.mul_assoc, hT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
      ← Matrix.mul_smul, heac]
  have t2 : aᵀ * (J * (1 - k.map c)) * a.map c = aᵀ * J := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hac, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_smul, ← Matrix.smul_mul, heaT]
  rw [hid, Matrix.mul_add, Matrix.add_mul, t1, t2] at main
  rw [add_comm]
  exact main

def unip (N : Matrix β β A) : GL (β ⊕ β) A where
  val := fromBlocks (1 + N) (-N) N (1 - N)
  inv := fromBlocks (1 - N) N (-N) (1 + N)
  val_inv := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring
  inv_val := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring

theorem unip_mem (c : A →ₐ[R] A) {J N : Matrix β β A} (hN : Nᵀ * J + J * N.map c = 0) :
    unip N ∈ GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) := by
  show ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * GlobalTheory.WeilM.dbl J *
      ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A).map c = GlobalTheory.WeilM.dbl J
  have hU : ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) =
      fromBlocks (1 + N) (-N) N (1 - N) := rfl
  have hm1 : (1 + N).map c = 1 + N.map c := by
    have h := map_add c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  have hm2 : (-N).map c = -N.map c := map_neg c.mapMatrix N
  have hm3 : (1 - N).map c = 1 - N.map c := by
    have h := map_sub c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  rw [hU, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [transpose_add, transpose_sub, transpose_neg, transpose_one, hm1, hm2, hm3]

  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · calc _ = J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = J := by rw [hN, add_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = -J := by rw [hN, add_zero]

theorem cong_block {e : R} {x : Matrix β β A} (hx : (1 - e) • (x - 1) = 0) :
    (1 - e) • (fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1) = 0 := by
  have h1 : fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1 =
      fromBlocks (x - 1) 0 0 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, fromBlocks_smul, hx]
  simp

theorem decomposition : ∀ (R A : Type) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (c : A →ₐ[R] A) (β : Type) [inst_3 : Fintype β] [inst_4 : DecidableEq β] (J : Matrix β β A), IsUnit (Matrix.det J) →
    ∀ (e : R), e * e = e →
    ∀ (g k : ↥(GlobalTheory.WeilM.UG c J)), ((1 : R) - e) • ((↑(↑g : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ((1 : R) - e) • ((↑(↑k : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ∀ (a b : Matrix β β A), e • a = a →
    e • b = b →
    a * ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ (gd kd : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))), (↑(↑gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑g : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    (↑(↑kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑k : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    ∃ (p₁ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (p₂ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (t₁ : GL β A) (t₂ : GL β A), ((1 : R) - e) • ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((1 : R) - e) • ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₁ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₂ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    gd = kd * p₁ * kd⁻¹ * p₂ := by
  intro R A _ _ _ c β _ _ J _ e he g k hg hk a b hea heb hak hka hbh hhb gd kd hgd hkd
  obtain ⟨Km, hKm⟩ : ∃ Km : Matrix β β A, Km = (((k : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  obtain ⟨gi, hgi⟩ : ∃ gi : Matrix β β A, gi = (((g : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  have hKk : Km * ((k : GL β A) : Matrix β β A) = 1 := by rw [hKm]; exact Units.inv_mul _
  have hkK : ((k : GL β A) : Matrix β β A) * Km = 1 := by rw [hKm]; exact Units.mul_inv _
  have hgig : gi * ((g : GL β A) : Matrix β β A) = 1 := by rw [hgi]; exact Units.inv_mul _
  have hggi : ((g : GL β A) : Matrix β β A) * gi = 1 := by rw [hgi]; exact Units.mul_inv _
  have hhgk : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = gi * ((k : GL β A) : Matrix β β A) := by rw [hgi]; rfl

  have hh : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) * (Km * ((g : GL β A) : Matrix β β A)) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((k : GL β A) : Matrix β β A) Km, hkK, Matrix.one_mul, hgig]
  have hh2 : Km * ((g : GL β A) : Matrix β β A) * (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((g : GL β A) : Matrix β β A) gi, hggi, Matrix.one_mul, hKk]
  have hKc : (1 - e) • (Km - 1) = 0 := cong_inv hk hKk
  have hhc : (1 - e) • (Km * ((g : GL β A) : Matrix β β A) - 1) = 0 := cong_mul hKc hg
  have key1 := key hKk hh hKc hhc hka hbh
  have key2 := key hh2 hkK hhc hKc hhb hak

  have hca := cayley c (J := J) (k := ((k : GL β A) : Matrix β β A)) (a := a) k.2 hea hka he
  have hcb := cayley c (J := J) (k := (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A)) (a := b) (g⁻¹ * k).2 heb hhb he
  have hskew : (a - b)ᵀ * J + J * (a - b).map c = 0 := by
    have hmap : (a - b).map c = a.map c - b.map c := by ext i j; simp
    rw [transpose_sub, hmap, Matrix.sub_mul, Matrix.mul_sub]
    calc aᵀ * J - bᵀ * J + (J * a.map c - J * b.map c)
        = (aᵀ * J + J * a.map c) - (bᵀ * J + J * b.map c) := by abel
      _ = 0 := by rw [hca, hcb, sub_self]
  obtain ⟨u, hu⟩ : ∃ u : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J),
      ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 + (a - b)) (-(a - b)) (a - b) (1 - (a - b)) ∧
      (((u⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 - (a - b)) (a - b) (-(a - b)) (1 + (a - b)) :=
    ⟨⟨unip (a - b), unip_mem c hskew⟩, rfl, rfl⟩
  have h2 : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = 1 := Units.inv_mul _
  have hkdinv : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks Km 0 0 1 := by
    have h1 : ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1 = 1 := by
      rw [hkd, fromBlocks_multiply, hkK]; simp [fromBlocks_one]
    calc (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1) := by rw [h1, Matrix.mul_one]
      _ = fromBlocks Km 0 0 1 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hblk : ∀ P Q S T : Matrix β β A,
      fromBlocks P Q S T - 1 = fromBlocks (P - 1) Q S (T - 1) := by
    intro P Q S T
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  have hN0 : (1 - e) • (a - b) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hN0' : (1 - e) • (b - a) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hkdc : (1 - e) • (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hkd]; exact cong_block hk
  have hgdc : (1 - e) • (((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hgd]; exact cong_block hg
  have hkdic : (1 - e) • ((((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := cong_inv hkdc h2
  have huc : (1 - e) • (((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by
    rw [hu.1, hblk, fromBlocks_smul]; simp [hN0, hN0']

  have ht : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) = 1 := by
    have e1 : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) =
        (1 - (a - b) * (Km - 1)) - (b - a) * ((Km * ((g : GL β A) : Matrix β β A) - 1) * (1 - (a - b) * (Km - 1))) := by
      noncomm_ring
    rw [e1, key2]
    noncomm_ring
  have hK2 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) = (1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b) := by
    have e1 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) =
        (Km - 1) * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) + (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) := by
      noncomm_ring
    rw [e1, key1]
    noncomm_ring
  have hfin : ((k : GL β A) : Matrix β β A) * ((1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b)) = 1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1) := by
    rw [← hK2, ← Matrix.mul_assoc, hkK, Matrix.one_mul]
  have hv : (((kd * u * kd⁻¹ * gd : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) :
      Matrix (β ⊕ β) (β ⊕ β) A) = ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) := rfl
  refine ⟨u⁻¹, kd * u * kd⁻¹ * gd, 1,
    ⟨1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1), 1 - (a - b) * (Km - 1), ht, mul_eq_one_comm.mp ht⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.2, hblk, fromBlocks_smul]; simp [hN0, hN0']
  · rw [hv]; exact cong_mul (cong_mul (cong_mul hkdc huc) hkdic) hgdc
  · rw [hu.2, GlobalTheory.WeilM.diagCols]
    simp only [fromBlocks_mul_fromRows, fromRows_mul, Units.val_one, Matrix.mul_one,
      Matrix.one_mul]
    rw [fromRows_ext_iff]
    constructor <;> abel
  · rw [hv, hkd, hu.1, hkdinv, hgd, GlobalTheory.WeilM.diagCols]
    simp only [Matrix.mul_assoc, fromBlocks_mul_fromRows, fromRows_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Units.val_mk]
    rw [fromRows_ext_iff]
    constructor
    · refine Eq.trans ?_ (hfin.trans ?_) <;> noncomm_ring
    · noncomm_ring
  · group

end GlobalTheory.UnipotentCongruenceInverse
