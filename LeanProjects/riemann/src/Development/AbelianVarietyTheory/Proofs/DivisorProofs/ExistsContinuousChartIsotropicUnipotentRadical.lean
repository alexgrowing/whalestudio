import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

section Ring

variable {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) {a b c : ℕ}

theorem gram_comb (X₁ Y₁ : Matrix (Fin n) (Fin a) R) (X₂ Y₂ : Matrix (Fin n) (Fin b) R)
    (X₃ Y₃ : Matrix (Fin n) (Fin c) R) (R₁ : Matrix (Fin a) (Fin n) R) (R₂ : Matrix (Fin b) (Fin n) R)
    (R₃ : Matrix (Fin c) (Fin n) R)
    (h11 : gr s A Y₁ Y₁ = gr s A X₁ X₁) (h12 : gr s A Y₁ Y₂ = gr s A X₁ X₂) (h13 : gr s A Y₁ Y₃ = gr s A X₁ X₃)
    (h21 : gr s A Y₂ Y₁ = gr s A X₂ X₁) (h22 : gr s A Y₂ Y₂ = gr s A X₂ X₂) (h23 : gr s A Y₂ Y₃ = gr s A X₂ X₃)
    (h31 : gr s A Y₃ Y₁ = gr s A X₃ X₁) (h32 : gr s A Y₃ Y₂ = gr s A X₃ X₂) (h33 : gr s A Y₃ Y₃ = gr s A X₃ X₃) :
    gr s A (Y₁ * R₁ + Y₂ * R₂ + Y₃ * R₃) (Y₁ * R₁ + Y₂ * R₂ + Y₃ * R₃) =
      gr s A (X₁ * R₁ + X₂ * R₂ + X₃ * R₃) (X₁ * R₁ + X₂ * R₂ + X₃ * R₃) := by
  simp only [gr_add_left, gr_add_right, gr_mul_left, gr_mul_right, h11, h12, h13, h21, h22, h23, h31, h32, h33]

theorem comb_mul {p : ℕ} (Y₁ : Matrix (Fin n) (Fin a) R) (Y₂ : Matrix (Fin n) (Fin b) R)
    (Y₃ : Matrix (Fin n) (Fin c) R) (R₁ : Matrix (Fin a) (Fin n) R) (R₂ : Matrix (Fin b) (Fin n) R)
    (R₃ : Matrix (Fin c) (Fin n) R) (X : Matrix (Fin n) (Fin p) R) :
    (Y₁ * R₁ + Y₂ * R₂ + Y₃ * R₃) * X = Y₁ * (R₁ * X) + Y₂ * (R₂ * X) + Y₃ * (R₃ * X) := by
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem cT_smul' {p q : Type} (x : R) (M : Matrix p q R) : cT s (x • M) = s x • cT s M := by
  ext i k; simp [cT]

end Ring

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j m : ℕ} (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
  (J₀ : Matrix (Fin m) (Fin m) E)

def uMat (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  adMat F C * adMat F (cT (σ : E →+* E) D * J) +
    (adMat F Z + adMat F C * b) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
    (adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c) * adMat F (cT (σ : E →+* E) C * J)

variable {σ J C D Z J₀}

theorem adMat_mul' {p q r : ℕ} (X : Matrix (Fin p) (Fin q) E) (Y : Matrix (Fin q) (Fin r) E) :
    adMat F X * adMat F Y = adMat F (X * Y) := (Matrix.map_mul).symm

theorem adMat_add' {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) E) : adMat F X + adMat F Y = adMat F (X + Y) :=
  (Matrix.map_add _ (map_add _) X Y).symm

theorem adMat_one' {p : ℕ} : adMat F (1 : Matrix (Fin p) (Fin p) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_zero' {p q : ℕ} : adMat F (0 : Matrix (Fin p) (Fin q) E) = 0 := Matrix.map_zero _ (map_zero _)

theorem uMat_mul_C (hF : Fr σ J C D Z J₀) (b c) : uMat σ J C D Z J₀ b c * adMat F C = adMat F C := by
  have e1 : adMat F (cT (σ : E →+* E) D * J) * adMat F C = 1 := by rw [adMat_mul', hF.dc, adMat_one']
  have e2 : adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * adMat F C = 0 := by
    rw [adMat_mul', Matrix.mul_assoc, hF.zc, Matrix.mul_zero, adMat_zero']
  have e3 : adMat F (cT (σ : E →+* E) C * J) * adMat F C = 0 := by rw [adMat_mul', hF.cc, adMat_zero']
  rw [uMat, comb_mul, e1, e2, e3]; simp

theorem uMat_mul_Z (hF : Fr σ J C D Z J₀) (b c) :
    uMat σ J C D Z J₀ b c * adMat F Z = adMat F Z + adMat F C * b := by
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have e1 : adMat F (cT (σ : E →+* E) D * J) * adMat F Z = 0 := by rw [adMat_mul', hF.dz, adMat_zero']
  have e2 : adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * adMat F Z = 1 := by
    rw [adMat_mul', Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hu, adMat_one']
  have e3 : adMat F (cT (σ : E →+* E) C * J) * adMat F Z = 0 := by rw [adMat_mul', hF.cz, adMat_zero']
  rw [uMat, comb_mul, e1, e2, e3]; simp

theorem uMat_mul_D (hF : Fr σ J C D Z J₀) (b c) :
    uMat σ J C D Z J₀ b c * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c := by
  have e1 : adMat F (cT (σ : E →+* E) D * J) * adMat F D = 0 := by rw [adMat_mul', hF.dd, adMat_zero']
  have e2 : adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * adMat F D = 0 := by
    rw [adMat_mul', Matrix.mul_assoc, hF.zd, Matrix.mul_zero, adMat_zero']
  have e3 : adMat F (cT (σ : E →+* E) C * J) * adMat F D = 1 := by rw [adMat_mul', hF.cd, adMat_one']
  rw [uMat, comb_mul, e1, e2, e3]; simp

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ} {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E}
  {J₀ : Matrix (Fin m) (Fin m) E}

theorem uMat_unitary (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E))
    (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J * uMat σ J C D Z J₀ b c = adMat F J := by
  set s := sigR (AF F) σ with hs
  set p := plus σ J₀ b with hp
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have key : cT s p * adMat F J₀ = b := by
    rw [hp, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc, adMat_mul',
      Matrix.nonsing_inv_mul _ hu, adMat_one', Matrix.mul_one]
  have key2 : adMat F J₀ * p = cT s b := by
    rw [hp, plus, ← Matrix.mul_assoc, adMat_mul', Matrix.mul_nonsing_inv _ hu, adMat_one', Matrix.one_mul]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 0 := by
    intro p q X Y h; rw [gr_adMat, h]; exact adMat_zero'
  have g1 : ∀ (X Y : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) X * J * Y = 1 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 1 := by
    intro X Y h; rw [gr_adMat, h]; exact adMat_one'
  have gzz : gr s (adMat F J) (adMat F Z) (adMat F Z) = adMat F J₀ := by rw [gr_adMat, hF.zz]
  have hcc := g0 C C hF.cc
  have hdd := g0 D D hF.dd
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have hzc := g0 Z C hF.zc
  have hzd := g0 Z D hF.zd
  have hcd := g1 C D hF.cd
  have hdc := g1 D C hF.dc
  have hsum : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    rw [adMat_mul', adMat_mul', adMat_mul', adMat_add', adMat_add', hF.sum, adMat_one']
  have := gram_comb s (adMat F J) (adMat F C) (adMat F C) (adMat F Z) (adMat F Z + adMat F C * b)
    (adMat F D) (adMat F D - adMat F Z * p + adMat F C * c) (adMat F (cT (σ : E →+* E) D * J))
    (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))) (adMat F (cT (σ : E →+* E) C * J)) rfl
    (by simp only [gr_add_right, gr_mul_right, hcc, hcz]; simp)
    (by simp only [gr_add_right, gr_sub_right, gr_mul_right, hcc, hcz, hcd]; simp)
    (by simp only [gr_add_left, gr_mul_left, hcc, hzc]; simp)
    (by simp only [gr_add_right, gr_add_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz]; simp)
    (by
      simp only [gr_add_right, gr_add_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hzd, hcd]
      simp [key2])
    (by simp only [gr_add_left, gr_sub_left, gr_mul_left, hcc, hzc, hdc]; simp)
    (by
      simp only [gr_add_right, gr_add_left, gr_sub_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hdz, hdc]
      simp [key])
    (by
      simp only [gr_add_right, gr_add_left, gr_sub_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz,
        hdz, hdc, hcd, hdd, hzd]
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_zero, zero_add, add_zero, zero_sub,
        sub_neg_eq_add, key]
      simp only [Matrix.neg_mul, sub_neg_eq_add]
      rw [← hc]
      abel)
  rw [hsum] at this
  simpa [gr, uMat, hp, Formalism.UG.cT_one] using this

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ} {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E}
  {J₀ : Matrix (Fin m) (Fin m) E}

theorem uInv_mul (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    (adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J) * uMat σ J C D Z J₀ b c = 1 := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hF.herm.2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F J), uMat_unitary hF b c hc, adMat_mul',
    Matrix.nonsing_inv_mul _ hu, adMat_one']

def uPt (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
    (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) : GAd σ J :=
  let g : GL (Fin n) (AF F ⊗[F] E) :=
    ⟨uMat σ J C D Z J₀ b c, adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J,
      mul_eq_one_comm.mp (uInv_mul hF b c hc), uInv_mul hF b c hc⟩
  let x : HR (AF F) σ J := ⟨g, uMat_unitary hF b c hc⟩
  x

theorem uPt_mat (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    (matHom _ σ J (uPt hF b c hc)).1 = uMat σ J C D Z J₀ b c := rfl

theorem uPt_inv (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    ((matHom _ σ J (uPt hF b c hc))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 =
      adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J := rfl

theorem uPt_crd (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    Crd σ J C D Z J₀ (uPt hF b c hc) b c :=
  ⟨uMat_mul_C hF b c, uMat_mul_Z hF b c, uMat_mul_D hF b c⟩

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ} {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E}
  {J₀ : Matrix (Fin m) (Fin m) E}

theorem cT_mul_plus (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    cT (sigR (AF F) σ) (b * plus σ J₀ b) = b * plus σ J₀ b := by
  rw [Formalism.UG.cT_mul, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc]

theorem sigR_half : sigR (AF F) σ (inclR (F := F) (AF F) (2⁻¹ : E)) = inclR (F := F) (AF F) (2⁻¹ : E) := by
  have h : σ (2⁻¹ : E) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  simp [sigR, inclR, h]

theorem half_add_half : inclR (F := F) (AF F) (2⁻¹ : E) + inclR (F := F) (AF F) (2⁻¹ : E) = 1 := by
  rw [← map_add, show (2⁻¹ : E) + 2⁻¹ = 1 by norm_num, map_one]

theorem skew_crd (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (s : skewA σ j) :
    ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * plus σ J₀ b)) +
      cT (sigR (AF F) σ) ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * plus σ J₀ b)) +
      b * plus σ J₀ b = 0 := by
  have hs : (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s = 0 := mem_skewA.mp s.2
  rw [cT_sub', cT_smul', cT_mul_plus hF, sigR_half]
  have e : ∀ (S T X : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (h : AF F ⊗[F] E),
      S - h • X + (T - h • X) + X = (S + T) - (h + h) • X + X := by
    intro S T X h; rw [add_smul]; abel
  rw [e, hs, half_add_half, one_smul]; abel

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

theorem chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∃ φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × GlobalTheory.ResidueEisenstein.ModConj.skewA σ j → GAd σ J, Continuous φ ∧ ∀ b s, GlobalTheory.SphEis.Crd σ J C D Z J₀ (φ (b, s)) b ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * GlobalTheory.SphEis.plus σ J₀ b)) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsg : Continuous (sigR (AF F) σ) := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  have hcT : ∀ {X : Type} [TopologicalSpace X] {p q : ℕ} {f : X → Matrix (Fin p) (Fin q) (AF F ⊗[F] E)},
      Continuous f → Continuous fun x => cT (sigR (AF F) σ) (f x) := fun hf => (hf.matrix_map hsg).matrix_transpose
  let cF : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j → Matrix (Fin j) (Fin j) (AF F ⊗[F] E) := fun p =>
    (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (p.1 * plus σ J₀ p.1)
  refine ⟨fun p => uPt hF p.1 (cF p) (skew_crd hF p.1 p.2), ?_, fun b s => uPt_crd hF _ _ _⟩
  have hb : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => p.1 := continuous_fst
  have hpl : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => plus σ J₀ p.1 :=
    continuous_const.matrix_mul (hcT hb)
  have hbp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => p.1 * plus σ J₀ p.1 :=
    hb.matrix_mul hpl
  have hh : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j =>
      inclR (F := F) (AF F) (2⁻¹ : E) • (p.1 * plus σ J₀ p.1) := by
    have := hbp.const_smul (inclR (F := F) (AF F) (2⁻¹ : E)); exact this
  have hs : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j =>
      (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous cF := hs.sub hh
  have hM : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => uMat σ J C D Z J₀ p.1 (cF p) :=
    ((continuous_const.matrix_mul continuous_const).add
      ((continuous_const.add (continuous_const.matrix_mul hb)).matrix_mul continuous_const)).add
      (((continuous_const.sub (continuous_const.matrix_mul hpl)).add (continuous_const.matrix_mul hc)).matrix_mul
        continuous_const)
  have hMi : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j =>
      adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ p.1 (cF p)) * adMat F J :=
    (continuous_const.matrix_mul (hcT hM)).matrix_mul continuous_const
  rw [(isEmbedding_matHom (AF F) σ J).continuous_iff]
  exact Units.continuous_iff.mpr ⟨hM.congr fun p => (uPt_mat hF _ _ _).symm, hMi.congr fun p => (uPt_inv hF _ _ _).symm⟩

end GlobalTheory.ResidueEisenstein.ChartU
