import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImagesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.UnipCrd

section Ring

variable {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)

theorem cT_add' {p q : Type} (M N : Matrix p q R) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_sub' {p q : Type} (M N : Matrix p q R) : cT s (M - N) = cT s M - cT s N := by
  ext i k; simp [cT]

def gr {p q : ℕ} (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) : Matrix (Fin p) (Fin q) R :=
  cT s X * A * Y

variable {p q k : ℕ}

theorem gr_add_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X + X') Y = gr s A X Y + gr s A X' Y := by
  simp [gr, cT_add', Matrix.add_mul]

theorem gr_sub_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X - X') Y = gr s A X Y - gr s A X' Y := by
  simp [gr, cT_sub', Matrix.sub_mul]

theorem gr_add_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y + Y') = gr s A X Y + gr s A X Y' := by
  simp [gr, Matrix.mul_add]

theorem gr_sub_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y - Y') = gr s A X Y - gr s A X Y' := by
  simp [gr, Matrix.mul_sub]

theorem gr_mul_left (X : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X * M) Y = cT s M * gr s A X Y := by
  simp [gr, Formalism.UG.cT_mul, Matrix.mul_assoc]

theorem gr_mul_right (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin q) R) :
    gr s A X (Y * M) = gr s A X Y * M := by
  simp [gr, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem cT_adMat {p q : Type} (X : Matrix p q E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

theorem gr_adMat {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E) :
    gr (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) = adMat F (cT (σ : E →+* E) X * J * Y) := by
  simp only [gr, cT_adMat, adMat, Matrix.map_mul]

theorem invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, invol σ h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cT_cT (h : IsCMExt F E σ) {p q : Type} (M : Matrix p q (AF F ⊗[F] E)) :
    cT (sigR (AF F) σ) (cT (sigR (AF F) σ) M) = M := by
  ext i k; simp [cT, sigR_invol σ h]

theorem cT_inv_herm {m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (h : IsHermND σ J₀) :
    cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := by
  have hJ : cT (σ : E →+* E) J₀ = J₀ := by
    ext i k; simp [cT, h.1]
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr h.2
  have e : cT (σ : E →+* E) J₀⁻¹ * J₀ = 1 := by
    calc cT (σ : E →+* E) J₀⁻¹ * J₀ = cT (σ : E →+* E) J₀⁻¹ * cT (σ : E →+* E) J₀ := by rw [hJ]
      _ = cT (σ : E →+* E) (J₀ * J₀⁻¹) := (Formalism.UG.cT_mul _ _ _).symm
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Formalism.UG.cT_one]
  exact (Matrix.inv_eq_left_inv e).symm

theorem exists_unipRad_crd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 → ∃ u ∈ unipRad σ J C, Crd σ J C D Z J₀ u b c := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF b c hc
  set s := sigR (AF F) σ with hs
  set p := plus σ J₀ b with hp
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have key : cT s p * adMat F J₀ = b := by
    rw [hp, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc, adMat,
      adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 0 := by
    intro p q X Y h; rw [gr_adMat, h]; simp
  have g1 : ∀ (X Y : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) X * J * Y = 1 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 1 := by
    intro X Y h; rw [gr_adMat, h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have gzz : gr s (adMat F J) (adMat F Z) (adMat F Z) = adMat F J₀ := by rw [gr_adMat, hF.zz]
  have hcc := g0 C C hF.cc
  have hdd := g0 D D hF.dd
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have hzc := g0 Z C hF.zc
  have hzd := g0 Z D hF.zd
  have hcd := g1 C D hF.cd
  have hdc := g1 D C hF.dc
  have Ecd : cT s (adMat F C) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 1 := by
    show gr s (adMat F J) _ _ = 1
    simp only [gr_add_right, gr_sub_right, gr_mul_right, hcd, hcz, hcc]
    simp
  have Ecz : cT s (adMat F C) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_mul_right, hcz, hcc]
    simp
  have Ezz : cT s (adMat F Z + adMat F C * b) * adMat F J * (adMat F Z + adMat F C * b) = adMat F J₀ := by
    show gr s (adMat F J) _ _ = _
    simp only [gr_add_right, gr_add_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz]
    simp
  have Edz : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hdz, hdc]
    simp [key]
  have Edd : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz,
      hdz, hdc, hcd, hdd, hzd]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_zero, zero_add, add_zero, zero_sub,
      sub_neg_eq_add, key]
    simp only [Matrix.neg_mul, sub_neg_eq_add]
    rw [← hc]
    abel
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D - adMat F Z * p + adMat F C * c)
    (adMat F Z + adMat F C * b) hcc Edd Ecd Ecz Edz Ezz
  exact ⟨g, (GlobalTheory.T.mem_isotropicUnipotentRadical_iff_frame F E σ n J j m C D Z J₀ hF g).mpr ⟨h1, b, h2⟩, h1, h2, h3⟩

end GlobalTheory.SphEis.UnipCrd
