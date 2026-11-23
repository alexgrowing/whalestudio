import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.TransportBack

open Matrix

theorem map_mul_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k p : Type*} [Fintype k]
    (X : Matrix m k R) (Y : Matrix k p R) : (X * Y).map f = X.map f * Y.map f := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_mulVec_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*} [Fintype k]
    (X : Matrix m k R) (a : k → R) : X.map f *ᵥ (fun i => f (a i)) = fun i => f ((X *ᵥ a) i) := by
  ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem map_add_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*}
    (X Y : Matrix m k R) : (X + Y).map f = X.map f + Y.map f := by
  ext i j; simp

theorem map_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (1 : Matrix n n R).map ι = ι 1 • (1 : Matrix n n S) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_neg_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (-1 : Matrix n n R).map ι = -(ι 1 • (1 : Matrix n n S)) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem assoc_a {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (D : Matrix d e R) :
    A * B * C * D = A * (B * (C * D)) := by simp only [Matrix.mul_assoc]

theorem assoc_b {R : Type*} [CommRing R] {a b c d : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (P₁ Y Q₁ P₂ : Matrix d d R) :
    A * B * C * (P₁ * Y * Q₁) * P₂ = A * (B * (C * (P₁ * (Y * (Q₁ * P₂))))) := by
  simp only [Matrix.mul_assoc]

theorem smul_mid_of {R : Type*} [CommRing R] {a b d : Type*} [Fintype b] [DecidableEq b]
    (s : R) (A : Matrix a b R) (B : Matrix b b R) (C : Matrix b d R) (h : s • B = s • 1) :
    s • (A * B * C) = s • (A * C) := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem smul_last_of {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (s : R) (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (Z : Matrix d e R) (h : s • Z = 0) :
    s • (A * B * C * Z) = 0 := by
  rw [← Matrix.mul_smul, h, Matrix.mul_zero]

end GlobalTheory.TransportBack

namespace GlobalTheory.TransportBack
open Matrix

theorem transport_back : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl F) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* AE F E)
    (P Q : Matrix (Fin n) (Fin n) (AE F E)) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ n X v O _ c ι P Q JL hAe he hc hPQ hQP heP heQ hJ hlat M G ZL hM hMG hZL hN
  have heι : ∀ x, ι 1 * ι x = ι x := fun x => by rw [← map_mul, one_mul]
  have hιe : ∀ x, ι x * ι 1 = ι x := fun x => by rw [← map_mul, mul_one]
  have hee : ι 1 * ι 1 = ι 1 := heι 1
  have hce : cA σ (ι 1) = ι 1 := by rw [hc, map_one]
  have hmapE : ∀ {m k : Type} (Y : Matrix m k O), ι 1 • Y.map ι = Y.map ι := by
    intro m k Y; ext i j; simp [heι]
  have hePY : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n) k (AE F E)), ι 1 • (P * Y) = P * Y := by
    intro k _ Y; rw [← Matrix.smul_mul, heP]
  have hZP : P * ZL.map ι * Q * P = P * ZL.map ι := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_smul, Matrix.mul_one, hePY]
  have hvec : ∀ a : Fin n → O, Q *ᵥ (P *ᵥ fun i => ι (a i)) = fun i => ι (a i) := by
    intro a; rw [Matrix.mulVec_mulVec, hQP, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp [heι]

  have hAtZ : At (evFin F v) (P * ZL.map ι * Q) := by
    intro u hu
    have hu' : u • Q = 0 := by rw [← heQ, ← smul_assoc, hAe u hu, zero_smul]
    rw [← Matrix.mul_smul, hu', Matrix.mul_zero]

  have hlatZ : ∀ z ∈ GlobalTheory.InertSph.latAt X v, (P * ZL.map ι * Q) *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
    intro z hz
    obtain ⟨a, rfl⟩ := (hlat z).1 hz
    refine (hlat _).2 ⟨ZL *ᵥ a, ?_⟩
    rw [Matrix.mulVec_mulVec, hZP, ← Matrix.mulVec_mulVec, map_mulVec_gen]

  have hPcQc : P.map (cA σ) * Q.map (cA σ) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← map_mul_gen, hPQ]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h, hce]
  have h1 : Pᵀ * incM F X.J = JL.map ι * Q.map (cA σ) := by
    calc Pᵀ * incM F X.J = ι 1 • (Pᵀ * incM F X.J) := by
            rw [← Matrix.smul_mul, ← Matrix.transpose_smul, heP]
      _ = Pᵀ * incM F X.J * (P.map (cA σ) * Q.map (cA σ)) := by
            rw [hPcQc, Matrix.mul_smul, Matrix.mul_one]
      _ = JL.map ι * Q.map (cA σ) := by rw [← Matrix.mul_assoc, hJ]
  have hPc : ι 1 • P.map (cA σ) = P.map (cA σ) := by
    conv_rhs => rw [← heP]
    ext i j; simp [hce]
  have h2 : incM F X.J * P.map (cA σ) = Qᵀ * JL.map ι := by
    calc incM F X.J * P.map (cA σ) = ι 1 • (incM F X.J * P.map (cA σ)) := by
            rw [← Matrix.mul_smul, hPc]
      _ = (P * Q)ᵀ * incM F X.J * P.map (cA σ) := by
            rw [hPQ, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.smul_mul,
              Matrix.one_mul]
      _ = Qᵀ * JL.map ι := by
            rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hJ]
  have hmapc : (ZL.map ι).map (cA σ) = (ZL.map c).map ι := by
    rw [Matrix.map_map, Matrix.map_map]; congr 1; funext x; exact hc x
  have hJZ : (P * ZL.map ι * Q)ᵀ * incM F X.J + incM F X.J * (P * ZL.map ι * Q).map (cA σ) = 0 := by
    have hz0 : (ZLᵀ * JL + JL * ZL.map c).map ι = 0 := by rw [hZL]; ext i j; simp
    rw [map_add_gen, map_mul_gen, map_mul_gen, Matrix.transpose_map] at hz0
    rw [map_mul_gen, map_mul_gen, hmapc, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc (incM F X.J), h2]
    calc _ = Qᵀ * ((ZL.map ι)ᵀ * JL.map ι + JL.map ι * (ZL.map c).map ι) * Q.map (cA σ) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hz0]; simp

  set N := ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL with hNdef
  set K := (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * ZL.map ι * Q) with hK
  have hNab : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (-(ι 1 • 1)) := by
    rw [Matrix.fromRows_map, map_one_eq, map_neg_one_eq]
  have hDel : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (ι 1 • 1) := by
    rw [Matrix.fromRows_map, map_one_eq]
  have hanti : GlobalTheory.DblVac.antiCols (F := F) (E := E) n * P = Matrix.fromBlocks P 0 0 P * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι := by
    rw [hNab, GlobalTheory.DblVac.antiCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hdiag : ∀ Y : Matrix (Fin n) (Fin n) (AE F E), (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * Y) = Matrix.fromBlocks P 0 0 P * ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDel, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hantiT : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * (Matrix.fromBlocks P 0 0 P * Y) = P * (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι)ᵀ * Y) := by
    intro k _ Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNab, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_fromRows,
      Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols]
    simp [Matrix.mul_smul, heP]
  have hMG' : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), M * (Matrix.fromBlocks P 0 0 P * Y) = Matrix.fromBlocks P 0 0 P * (G.map ι * Y) := by
    intro k _ Y; rw [← Matrix.mul_assoc, hMG, Matrix.mul_assoc]
  have hQPι : ZL.map ι * (Q * P) = ZL.map ι := by rw [hQP, Matrix.mul_smul, Matrix.mul_one, hmapE]
  have hKP : K * P = P * N.map ι := by
    rw [hK, Matrix.add_mul]
    refine (congrArg₂ (· + ·) (assoc_a _ _ _ _) (assoc_b _ _ _ _ _ _ _)).trans ?_
    rw [hanti, hQPι, hdiag, hMG', hMG', hantiT, hantiT, hNdef]
    simp only [map_add_gen, map_mul_gen, Matrix.transpose_map, Matrix.mul_add, Matrix.mul_assoc]

  have hN1 : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN
  have h2inv : algebraMap F (AE F E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (AE F E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hMe : ι 1 • (M - 1) = M - 1 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    apply he
    intro u hu
    have := congrFun (congrFun (hM u hu) i) j
    simpa using this
  have hM1 : (1 - ι 1) • M = (1 - ι 1) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [sub_smul, one_smul, sub_smul, one_smul, ← sub_eq_zero,
      show M - ι 1 • M - (1 - ι 1 • 1) = (M - 1) - (ι 1 • M - ι 1 • 1) by abel, ← smul_sub, hMe, sub_self]
  have hZe : (1 - ι 1) • (P * ZL.map ι * Q) = 0 := by
    rw [sub_smul, one_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, heP, sub_self]
  have hAA : (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.antiCols n = (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows]
    refine (Matrix.fromCols_mul_fromRows _ _ _ _).trans ?_
    simp [two_smul]
  have hKe : (1 - ι 1) • K = (1 - ι 1) • ((2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hK, smul_add]
    refine (congrArg₂ (· + ·) (smul_mid_of _ _ _ _ hM1) (smul_last_of _ _ _ _ _ hZe)).trans ?_
    rw [add_zero]
    exact congrArg _ hAA
  set R := (algebraMap F (AE F E) 2⁻¹ * (1 - ι 1)) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + P * N⁻¹.map ι * Q with hR
  have hKR : K * R = 1 := by
    have hsec : K * (P * N⁻¹.map ι * Q) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKP, Matrix.mul_assoc P, ← map_mul_gen, hN1, map_one_eq,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ, smul_smul, hee]
    rw [hR, Matrix.mul_add, hsec, Matrix.mul_smul, Matrix.mul_one, mul_smul, hKe, smul_smul, smul_smul, ← add_smul,
      show algebraMap F (AE F E) 2⁻¹ * (1 - ι 1) * 2 + ι 1 = (1 - ι 1) * (algebraMap F (AE F E) 2⁻¹ * 2) + ι 1 by ring,
      h2inv, mul_one, sub_add_cancel, one_smul]
  have hPz : ∀ w : Fin n → AE F E, (1 - ι 1) • (P *ᵥ w) = 0 := by
    intro w; rw [← Matrix.smul_mulVec, sub_smul, one_smul, heP, sub_self, Matrix.zero_mulVec]
  refine ⟨P * ZL.map ι * Q, hAtZ, hlatZ, hJZ, Matrix.isUnit_det_of_right_inverse hKR, ?_⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (hlat z).1 hz
  rw [Matrix.inv_eq_right_inv hKR]
  refine (hlat _).2 ⟨N⁻¹ *ᵥ a, ?_⟩
  rw [hR, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mul_smul, hPz, smul_zero, zero_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvec, map_mulVec_gen]

end GlobalTheory.TransportBack
