import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WProof
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.TransitiveOverLocalRings
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SaturatedSplitLattice

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section FieldW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def fA {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Z : Fin m → Fin n → Fv F v ⊗[F] E) : Matrix (Fin n) (Fin m) (Fv F v) :=
  Matrix.of fun i a => D.π₁ (Z a i)

def fB {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Z : Fin m → Fin n → Fv F v ⊗[F] E) : Matrix (Fin n) (Fin m) (Fv F v) :=
  Matrix.of fun i a => D.π₂ (Z a i)

theorem witt_genF {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) (Q : GL (Fin n) (Fv F v ⊗[F] E))
    (hQh : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
        ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i)
    {m : ℕ} (Z0 Z : Fin m → Fin n → Fv F v ⊗[F] E)
    (hA0 : ∃ L : Matrix (Fin m) (Fin n) (Fv F v), L * fA D Z0 = 1)
    (hB0 : ∃ L : Matrix (Fin m) (Fin n) (Fv F v), L * fB D Z0 = 1)
    (hA1 : ∃ L : Matrix (Fin m) (Fin n) (Fv F v), L * fA D Z = 1)
    (hB1 : ∃ L : Matrix (Fin m) (Fin n) (Fv F v), L * fB D Z = 1)
    (hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b)) :
    ∃ k : HA (Fv F v) σ J, ∀ a,
      (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Z0 a) =
        (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Z a := by
  classical
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have hgram : (fA D Z0)ᵀ * fB D Z0 = (fA D Z)ᵀ * fB D Z := by
    refine Matrix.ext fun a b => ?_
    have := congrArg D.π₂ (hstd a b)
    rw [D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, fA, fB, Matrix.of_apply]
    simp only [dotProduct] at this
    exact this.symm
  obtain ⟨k1, hk1u, hk1A, hk1B⟩ :=
    transitiveOverLocalRings (Fv F v) n m (fA D Z0) (fA D Z) (fB D Z0) (fB D Z) hA0 hA1 hB0 hB1 hgram
  have hdet : IsUnit k1.det := (Matrix.isUnit_iff_isUnit_det k1).1 hk1u
  have hki : k1 * k1⁻¹ = 1 := Matrix.mul_nonsing_inv k1 hdet
  have hik : k1⁻¹ * k1 = 1 := Matrix.nonsing_inv_mul k1 hdet
  have e1 : (k1⁻¹)ᵀᵀ * k1 = 1 := by rw [transpose_transpose, hik]
  have e2 : k1ᵀ * (k1⁻¹)ᵀ = 1 := by rw [← transpose_mul, hik, transpose_one]
  have e3 : (k1⁻¹)ᵀ * k1ᵀ = 1 := by rw [← transpose_mul, hki, transpose_one]
  set kstd := D.kS k1 (k1⁻¹)ᵀ with hkstd
  set kstd' := D.kS k1⁻¹ k1ᵀ with hkstd'
  have hkk : kstd * kstd' = 1 := by
    rw [hkstd, hkstd', SD.kS_mul, hki, e3, SD.kS_one]
  have hk'k : kstd' * kstd = 1 := mul_eq_one_comm.mp hkk
  have hkU : ∀ x y, stdH σ (kstd *ᵥ x) (kstd *ᵥ y) = stdH σ x y := fun x y =>
    D.stdH_kS _ _ e1 e2 x y
  have hkZ : ∀ a, kstd *ᵥ Z0 a = Z a := by
    intro a
    apply D.extV
    · intro i
      rw [hkstd, SD.fst_proj_split_matrix_mulVec]
      have := congrArg (fun M => M i a) hk1A
      simp only [Matrix.mul_apply, fA, Matrix.of_apply] at this
      simp only [mulVec, dotProduct]
      exact this
    · intro i
      have hB : (k1⁻¹)ᵀ * fB D Z0 = fB D Z := by
        rw [← hk1B, ← Matrix.mul_assoc, e3, Matrix.one_mul]
      rw [hkstd, SD.snd_proj_split_matrix_mulVec]
      have := congrArg (fun M => M i a) hB
      simp only [Matrix.mul_apply, fB, Matrix.of_apply] at this
      simp only [mulVec, dotProduct]
      exact this
  set kM := Qm * kstd * Qi with hkM
  set kMi := Qm * kstd' * Qi with hkMi
  have hkMM : kM * kMi = 1 := by
    rw [hkM, hkMi]
    calc Qm * kstd * Qi * (Qm * kstd' * Qi) = Qm * (kstd * (Qi * Qm) * kstd') * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQiQ, Matrix.mul_one, hkk, Matrix.mul_one, hQQi]
  have hkMM' : kMi * kM = 1 := mul_eq_one_comm.mp hkMM
  let kG : GL (Fin n) (Fv F v ⊗[F] E) := ⟨kM, kMi, hkMM, hkMM'⟩
  have hkx : ∀ x, kM *ᵥ x = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ x)) := by
    intro x; rw [hkM, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hmem : kG ∈ HR (Fv F v) σ J := by
    show Formalism.UG.cT (sigR (Fv F v) σ) kM * JR (Fv F v) J * kM = JR (Fv F v) J
    apply hform_ext (sigR (Fv F v) σ)
    intro x y
    rw [← hform_mulVec]
    show hR (Fv F v) σ J (kM *ᵥ x) (kM *ᵥ y) = hR (Fv F v) σ J x y
    rw [hkx, hkx, hQh, ← stdH, hkU, stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec,
      one_mulVec]
  let kH : HA (Fv F v) σ J := (⟨kG, hmem⟩ : HR (Fv F v) σ J)
  refine ⟨kH, fun a => ?_⟩
  show kM *ᵥ (Qm *ᵥ Z0 a) = Qm *ᵥ Z a
  rw [hkx, mulVec_mulVec (Z0 a) Qi Qm, hQiQ, one_mulVec, hkZ a]

theorem leftInv_mul_uMat {v : HeightOneSpectrum (𝓞 F)} {n r : ℕ}
    (π : Fv F v ⊗[F] E →+* Fv F v) (x : UIdx r → Fv F v ⊗[F] E)
    (A : Matrix (Fin n) (Fin (r + 1)) (Fv F v))
    (hA : ∃ L : Matrix (Fin (r + 1)) (Fin n) (Fv F v), L * A = 1) :
    ∃ L : Matrix (Fin (r + 1)) (Fin n) (Fv F v), L * (A * (uMat v x).map π) = 1 := by
  obtain ⟨L, hL⟩ := hA
  set U := (uMat v x).map π with hU
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => ?_)]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [hU, uMat]
    · have h1 : ¬ i = j := fun h => (lt_irrefl _ (h ▸ hij))
      have h2 : ¬ i < j := fun h => (lt_asymm h hij)
      simp [hU, uMat, h1, h2]
  have hu : IsUnit U.det := by rw [hdet]; exact isUnit_one
  refine ⟨U⁻¹ * L, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, Matrix.nonsing_inv_mul _ hu]

end FieldW

def GramU : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (T : F),
    StdHyp σ J ψ → P.IsStd σ J T → ∀ (x : UIdx r → Fv F v ⊗[F] E) (a b : Fin (r + 1)),
      hR (Fv F v) σ J (∑ c, uMat v x c a • ratV (F := F) (Fv F v) (F0 P c))
        (∑ c, uMat v x c b • ratV (F := F) (Fv F v) (F0 P c)) =
      hR (Fv F v) σ J (ratV (F := F) (Fv F v) (F0 P a)) (ratV (F := F) (Fv F v) (F0 P b))

def UnipSplitF : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) (T : F),
    StdHyp σ J ψ → P.IsStd σ J T → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    etaV (E := E) v = 1 → LocMassOrdW.IsLatLoc v Λ →
    IsPrim v Λ (locF v (ratTup (F := F) (Fv F v) (F0 P))) →
    ∀ x : UIdx r → Fv F v ⊗[F] E, ∃ g : HA (Fv F v) σ J, ∀ b,
      lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
        ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a)

theorem unipSplitF_of (hG : GramU) (hS : SplitR) (hLs : LatStd) : UnipSplitF := by
  classical
  intro F E _ _ _ _ _ σ n J ψ v r P Λ T hStd hP hSD hUn hEta hL hPr x
  obtain ⟨e, π₁, π₂, _he, _hσe, h1, h2, hπe1, hπe2, hπsc, hσ2, hσ1, hO⟩ := hS σ J ψ v hStd hUn hEta
  let D : SD σ v := ⟨e, π₁, π₂, h1, h2, hπe1, hπe2, hπsc, hσ1, hσ2, hO⟩
  obtain ⟨Q, hQΛ, hQh⟩ := hLs σ J ψ v Λ hStd hSD hUn hEta hL
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have memΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔ IntV v (Qi *ᵥ y) := by
    intro y
    rw [hQΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mulVec_mulVec, hQiQ, one_mulVec]
    · intro hy
      exact ⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩
  have linQ : ∀ {m : ℕ} (c : Fin m → Fv F v ⊗[F] E) (W : Fin m → Fin n → Fv F v ⊗[F] E),
      Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a) := by
    intro m c W
    show Matrix.mulVecLin Qi (∑ a, c a • W a) = _
    rw [map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply]
  have primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W →
      ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) →
        ∀ a, c a ∈ OEv (E := E) v := by
    intro W hW c hc
    apply hW.2 c
    rw [memΛ, linQ]
    exact hc
  set U := uMat v x with hU
  set Y0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => ratV (F := F) (Fv F v) (F0 P a) with hY0
  set Yu : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => ∑ a, U a b • Y0 a with hYu
  set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0
  set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => Qi *ᵥ Yu b with hZ
  have hZe : ∀ b i, Z b i = ∑ a, U a b * Z0 a i := by
    intro b i
    simp only [hZ, hYu, linQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hZ0]

  set Wl := locF v (ratTup (F := F) (Fv F v) (F0 P)) with hWl
  set Zl : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Wl a with hZl
  have hZlZ0 : ∀ a i, Zl a i = sc (E := E) v (alp v r a) * Z0 a i := by
    intro a i
    simp only [hZl, hWl, locF, hZ0, hY0, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  have hZlI : ∀ a, IntV v (Zl a) := fun a => (memΛ _).1 (hPr.1 a)
  have pZl := primT Wl hPr
  let Ao : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Zl a i), ((D.hO _).1 (hZlI a i)).1⟩
  let Bo : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Zl a i), ((D.hO _).1 (hZlI a i)).2⟩
  obtain ⟨LA, hLA⟩ := saturated_split_lattice v n (r + 1) Ao (fun t ht => D.sat₁ Zl pZl t ht)
  obtain ⟨LB, hLB⟩ := saturated_split_lattice v n (r + 1) Bo (fun t ht => D.sat₂ Zl pZl t ht)
  set f := (v.adicCompletionIntegers F).subtype with hf
  have hAo : Ao.map f = fA D Z0 * Matrix.diagonal (alp v r) := by
    refine Matrix.ext fun i a => ?_
    rw [Matrix.mul_diagonal]
    show D.π₁ (Zl a i) = D.π₁ (Z0 a i) * alp v r a
    rw [hZlZ0, map_mul, (D.hsc _).1, mul_comm]
  have hBo : Bo.map f = fB D Z0 * Matrix.diagonal (alp v r) := by
    refine Matrix.ext fun i a => ?_
    rw [Matrix.mul_diagonal]
    show D.π₂ (Zl a i) = D.π₂ (Z0 a i) * alp v r a
    rw [hZlZ0, map_mul, (D.hsc _).2, mul_comm]
  have lift : ∀ (M0 : Matrix (Fin n) (Fin (r + 1)) (Fv F v))
      (Mo : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F))
      (Lo : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F)),
      Lo * Mo = 1 → Mo.map f = M0 * Matrix.diagonal (alp v r) →
      ∃ L : Matrix (Fin (r + 1)) (Fin n) (Fv F v), L * M0 = 1 := by
    intro M0 Mo Lo hLo hMo
    have h0 : (Lo.map f * M0) * Matrix.diagonal (alp v r) = 1 := by
      rw [Matrix.mul_assoc, ← hMo, ← Matrix.map_mul, hLo, Matrix.map_one f (map_zero f) (map_one f)]
    refine ⟨Matrix.diagonal (alp v r) * Lo.map f, ?_⟩
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.mp h0
  have hA0 := lift _ _ _ hLA hAo
  have hB0 := lift _ _ _ hLB hBo
  have hAZ : fA D Z = fA D Z0 * U.map D.π₁ := by
    refine Matrix.ext fun i b => ?_
    simp only [fA, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hZe, map_sum, map_mul]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hBZ : fB D Z = fB D Z0 * U.map D.π₂ := by
    refine Matrix.ext fun i b => ?_
    simp only [fB, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hZe, map_sum, map_mul]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hA1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (Fv F v), L * fA D Z = 1 := by
    rw [hAZ]; exact leftInv_mul_uMat D.π₁ x _ hA0
  have hB1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (Fv F v), L * fB D Z = 1 := by
    rw [hBZ]; exact leftInv_mul_uMat D.π₂ x _ hB0
  have hstdR : ∀ y y' : Fin n → Fv F v ⊗[F] E, stdH σ (Qi *ᵥ y) (Qi *ᵥ y') = hR (Fv F v) σ J y y' := by
    intro y y'
    rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
  have hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b) := by
    intro a b
    rw [hZ, hZ0]
    simp only
    rw [hstdR, hstdR]
    exact hG σ J ψ v P T hStd hP x a b
  obtain ⟨k, hk⟩ := witt_genF (J := J) D Q hQh Z0 Z hA0 hB0 hA1 hB1 hstd
  refine ⟨k, fun b => ?_⟩
  have := hk b
  change (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ (Qm *ᵥ (Qi *ᵥ Y0 b)) =
    Qm *ᵥ (Qi *ᵥ Yu b) at this
  rw [mulVec_mulVec (Y0 b) Qm Qi, mulVec_mulVec (Yu b) Qm Qi, hQQi, one_mulVec, one_mulVec] at this
  show (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y0 b = Yu b
  exact this

end PI.LocMassTypW
