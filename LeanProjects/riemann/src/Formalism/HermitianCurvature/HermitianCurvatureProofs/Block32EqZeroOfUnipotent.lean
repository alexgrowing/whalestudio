import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Minors

namespace Formalism.FourierDecayAlt.P.S3x9

open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)

def revRows (A : Type) (r : ℕ) : Matrix (Fin r) (Fin r) A ≃ Matrix (Fin r) (Fin r) A where
  toFun X := X.submatrix Fin.rev id
  invFun X := X.submatrix Fin.rev id
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp

theorem cornerCount (K : Type) [Field K] [Fintype K] (r : ℕ) :
    Nat.card {X : Matrix (Fin r) (Fin r) K // ∀ (l : ℕ) (hl : l ≤ r), cm X l hl ≠ 0} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by
  rw [← Formalism.FourierDecayAlt.P.leading_minors_count K r]
  exact Nat.card_congr ((revRows K r).subtypeEquiv fun X => Iff.rfl)

theorem block31_add {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x + y) = b31 x + b31 y := rfl

theorem block31_sub {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x - y) = b31 x - b31 y := rfl

theorem block31_smul {A : Type} [CommRing A] {r k : ℕ} (c : A) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (c • x) = c • b31 x := rfl

theorem block31_mul {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  simp [b31, b11, b32, b21, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_mul {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  simp [b31, b12, b32, b22, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_levi_embedding {A : Type} [CommRing A] {r k : ℕ} (h : Matrix (Fin k) (Fin k) A) :
    b32 (hEmb r h) = 0 := by
  ext a b
  simp [b32, hEmb]

theorem block32_eq_zero_of_unipotent {A : Type} [CommRing A] {r k : ℕ} {x : Matrix (Idx r k) (Idx r k) A}
    (hx : IsNU x) : b32 x = 0 := by
  obtain ⟨n, u, hn, ⟨u', -, rfl⟩, rfl⟩ := hx
  obtain ⟨-, -, -, -, h31, h32⟩ := hn
  rw [block32_mul, h31, h32, block32_levi_embedding]
  simp

theorem block32_map {A B : Type} {r k : ℕ} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

def lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) : Matrix (Idx r k) (Idx r k) A :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inr (Sum.inr a), Sum.inl b => Y a b
    | _, _ => 0

theorem block31_lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) :
    b31 (lowerLeftBlockMatrix r k Y) = Y := rfl

def splitEquiv (A : Type) [CommRing A] (r k : ℕ) (P : Matrix (Fin r) (Fin r) A → Prop) :
    {M : Matrix (Idx r k) (Idx r k) A // P (b31 M)} ≃
      {Y : Matrix (Fin r) (Fin r) A // P Y} × {Z : Matrix (Idx r k) (Idx r k) A // b31 Z = 0} where
  toFun M := (⟨b31 M.1, M.2⟩, ⟨M.1 - lowerLeftBlockMatrix r k (b31 M.1), by rw [block31_sub, block31_lowerLeftBlockMatrix, sub_self]⟩)
  invFun p := ⟨p.2.1 + lowerLeftBlockMatrix r k p.1.1, by
    rw [block31_add, block31_lowerLeftBlockMatrix, p.2.2, zero_add]; exact p.1.2⟩
  left_inv M := by
    apply Subtype.ext
    simp
  right_inv p := by
    obtain ⟨⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := p
    have h : b31 (Z + lowerLeftBlockMatrix r k Y) = Y := by rw [block31_add, block31_lowerLeftBlockMatrix, hZ, zero_add]
    apply Prod.ext
    · exact Subtype.ext h
    · apply Subtype.ext
      simp [h]

noncomputable def affEquiv {A : Type} [CommRing A] {r : ℕ} (X₀ u : Matrix (Fin r) (Fin r) A)
    (hu : IsUnit u.det) : Matrix (Fin r) (Fin r) A ≃ Matrix (Fin r) (Fin r) A where
  toFun Y := X₀ + u * Y
  invFun X := u⁻¹ * (X - X₀)
  left_inv Y := by
    simp only [add_sub_cancel_left]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul u hu, Matrix.one_mul]
  right_inv X := by
    simp only
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv u hu, Matrix.one_mul, add_sub_cancel]

end Formalism.FourierDecayAlt.P.S3x9

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix in
theorem Formalism.FourierDecayAlt.P.cornerMinorsCount_true : Formalism.FourierDecayAlt.S3.CornerMinorsCount :=
  fun K _ _ r => cornerCount K r

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix in
theorem Formalism.FourierDecayAlt.P.unit_stratum_coset : Formalism.FourierDecayAlt.S3.UnitStratumCoset := by
  intro o _ _ _ ϖ hϖ r k j₀ M X₀ hj h31
  have hres : IsLocalRing.residue o ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hϖ.not_isUnit
  have h32 : (b32 j₀).map (IsLocalRing.residue o) = 0 := by
    rw [← block32_map]; exact block32_eq_zero_of_unipotent hj.2
  refine ⟨X₀ + b31 (j₀ * M), ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, block31_add, block31_smul, h31, smul_add]
  · rw [block31_mul, h31]
    have e : ∀ a b : Matrix (Fin r) (Fin r) o,
        (a + b).map (IsLocalRing.residue o) = a.map (IsLocalRing.residue o) + b.map (IsLocalRing.residue o) :=
      fun a b => Matrix.map_add (IsLocalRing.residue o) (map_add _) a b
    have z1 : ((ϖ • X₀) * b11 M).map (IsLocalRing.residue o) = 0 := by
      rw [Matrix.smul_mul]
      ext a b
      simp [hres]
    have z2 : (b32 j₀ * b21 M).map (IsLocalRing.residue o) = 0 := by
      rw [Matrix.map_mul, h32, Matrix.zero_mul]
    rw [e, e, e, e, z1, z2]
    simp

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix in
theorem Formalism.FourierDecayAlt.P.unit_stratum_share : Formalism.FourierDecayAlt.S3.UnitStratumShare := by
  intro K _ _ r k X₀ u hu
  classical
  set q := Fintype.card K with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  set κ := Nat.card {Z : Matrix (Idx r k) (Idx r k) K // b31 Z = 0} with hκ
  have c1 : Nat.card {M : Matrix (Idx r k) (Idx r k) K //
        ∀ (l : ℕ) (hl : l ≤ r), cm (X₀ + u * b31 M) l hl ≠ 0} =
      (q ^ (r ^ 2 - r) * (q - 1) ^ r) * κ := by
    rw [Nat.card_congr (splitEquiv K r k
      (fun Y => ∀ (l : ℕ) (hl : l ≤ r), cm (X₀ + u * Y) l hl ≠ 0)), Nat.card_prod,
      ← cornerCount K r]
    congr 1
    exact Nat.card_congr ((affEquiv X₀ u hu).subtypeEquiv fun Y => Iff.rfl)
  have c2 : Nat.card (Matrix (Idx r k) (Idx r k) K) = q ^ (r ^ 2) * κ := by
    have h0 : Nat.card (Matrix (Idx r k) (Idx r k) K) =
        Nat.card {M : Matrix (Idx r k) (Idx r k) K // (fun _ => True) (b31 M)} :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial).symm
    rw [h0, Nat.card_congr (splitEquiv K r k (fun _ => True)), Nat.card_prod,
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)]
    congr 1
    show Nat.card (Fin r → Fin r → K) = _
    simp [← pow_mul, sq, hq]
  rw [c1, c2]
  have hr : r ^ 2 = (r ^ 2 - r) + r := by
    have : r ≤ r ^ 2 := by nlinarith [Nat.zero_le r]
    omega
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hq1]
  conv_rhs => rw [hr, pow_add]
  have : (1 - 1 / (q : ℝ)) ^ r * (q : ℝ) ^ r = ((q : ℝ) - 1) ^ r := by
    rw [← mul_pow]; congr 1; field_simp
  calc (q : ℝ) ^ (r ^ 2 - r) * ((q : ℝ) - 1) ^ r * κ
      = (q : ℝ) ^ (r ^ 2 - r) * ((1 - 1 / (q : ℝ)) ^ r * (q : ℝ) ^ r) * κ := by rw [this]
    _ = _ := by ring

theorem Formalism.FourierDecayAlt.P.unit_stratum_mass : Formalism.FourierDecayAlt.S3.UnitStratumMass := by
  intro volNo volJH volKpp volOm cUk c J h1 h2 h3 h4 hc hJ
  subst hc; subst hJ
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
