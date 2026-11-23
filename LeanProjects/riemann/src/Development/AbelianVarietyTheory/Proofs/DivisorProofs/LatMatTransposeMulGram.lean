import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def latMat {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv b).toRingHom.comp (Module.toModuleEnd ℤ (S := 𝓞 E) Dw.La)

theorem latMat_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) (i j : Fin n) :
    latMat Dw b a i j = b.repr (a • b j) i := by
  simp [latMat, LinearMap.toMatrixAlgEquiv_apply]

def gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun m m' => Dw.EF (b m) (b m')

def chiAct {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ where
  toFun a := (latMat Dw b (H.bar a)).transpose
  map_one' := by simp
  map_mul' a a' := by
    show (latMat Dw b (H.bar (a * a'))).transpose = (latMat Dw b (H.bar a)).transpose * (latMat Dw b (H.bar a')).transpose
    rw [← Matrix.transpose_mul, ← map_mul (latMat Dw b), ← map_mul H.bar, mul_comm a' a]
  map_zero' := by simp
  map_add' a a' := by simp [Matrix.transpose_add]

def dualForm {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : Matrix (Fin n) (Fin n) ℤ := (gram Dw b)⁻¹.transpose

end Lattice

section Setup

variable {D : D7} (O : Setup D)

def cmSet : Set (D.host.E →+* D.what₂.LL) :=
  {σ | ((O.κ.e (σ (O.A.H.rt : D.host.E)) : O.κ.c.F) : ℂ) = O.A.H.rt0}

def letterEmb (l : ℕ) : D.host.E →+* D.what₂.LL :=
  match (letters O.S.Dw)[l]? with
  | some x => O.κ.e.symm.toRingHom.comp (x.1.codRestrict O.κ.c.F.toSubfield (O.κ.c.conj x.1))
  | none => D.embE

end Setup

end GlobalTheory.EqHalf

namespace GlobalTheory.EqHalf

section LatticeThm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem isUnit_det_gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : IsUnit (gram Dw b).det := by
  let e : Dw.La ≃ₗ[ℤ] Module.Dual ℤ Dw.La := LinearEquiv.ofBijective Dw.EF Dw.unimod
  have h := LinearEquiv.isUnit_det e b b.dualBasis
  have hm : LinearMap.toMatrix b b.dualBasis (e : Dw.La →ₗ[ℤ] Module.Dual ℤ Dw.La) = (gram Dw b).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply, gram, e]
  rw [hm, Matrix.det_transpose] at h
  exact h

theorem latMat_transpose_mul_gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) :
    (latMat Dw b a).transpose * gram Dw b = gram Dw b * latMat Dw b (H.bar a) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, latMat_apply, gram, Matrix.of_apply]
  have h1 : Dw.EF (a • b i) (b j) = ∑ m, b.repr (a • b i) m * Dw.EF (b m) (b j) := by
    conv_lhs => rw [← b.sum_repr (a • b i)]
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  have h2 : Dw.EF (b i) (H.bar a • b j) = ∑ m, Dw.EF (b i) (b m) * b.repr (H.bar a • b j) m := by
    conv_lhs => rw [← b.sum_repr (H.bar a • b j)]
    simp only [map_sum, map_zsmul, smul_eq_mul, mul_comm]
  rw [← h1, ← h2, Dw.adj]

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E (a : E)

theorem chiAct_adj {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) :
    (chiAct Dw b a).transpose * dualForm Dw b = dualForm Dw b * chiAct Dw b (H.bar a) := by
  have hG := isUnit_det_gram Dw b
  have key := latMat_transpose_mul_gram Dw b (H.bar a)
  rw [bar_bar] at key

  have k2 : (gram Dw b)⁻¹ * (latMat Dw b (H.bar a)).transpose = latMat Dw b a * (gram Dw b)⁻¹ := by
    calc (gram Dw b)⁻¹ * (latMat Dw b (H.bar a)).transpose
        = (gram Dw b)⁻¹ * ((latMat Dw b (H.bar a)).transpose * gram Dw b) * (gram Dw b)⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = latMat Dw b a * (gram Dw b)⁻¹ := by
          rw [key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]
  show (latMat Dw b (H.bar a)).transpose.transpose * (gram Dw b)⁻¹.transpose =
    (gram Dw b)⁻¹.transpose * (latMat Dw b (H.bar (H.bar a))).transpose
  rw [bar_bar, Matrix.transpose_transpose, ← Matrix.transpose_mul, ← k2, Matrix.transpose_mul,
    Matrix.transpose_transpose]

theorem isUnit_det_dualForm {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : IsUnit (dualForm Dw b).det := by
  rw [dualForm, Matrix.det_transpose]
  exact Matrix.isUnit_nonsing_inv_det _ (isUnit_det_gram Dw b)

end LatticeThm

section SetupThm

variable {D : D7} (O : Setup D)

theorem nonempty_basis : Nonempty (Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Coisotropic.lattice_rank D.host.E O.A.H O.S.Dw
  have hf := GlobalTheory.Proof.LetterConjugation.finrank_host D
  have hN := O.S.rank_eq
  refine ⟨Module.finBasisOfFinrankEq ℤ _ ?_⟩
  rw [h3, hf, Nat.mul_div_cancel_left _ two_pos, hN]
  ring

theorem bar_rt : O.A.H.bar O.A.H.rt = -O.A.H.rt := by
  have h1 : (O.A.H.bar O.A.H.rt) ^ 2 = O.A.H.rt ^ 2 := by rw [← map_pow, O.A.H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj D.host.E (O.A.H.rt : D.host.E) = (O.A.H.rt : D.host.E) := by rw [← O.A.H.bar_eq, h]
    have h3 := IsCMField.complexEmbedding_complexConj D.host.E φ (O.A.H.rt : D.host.E)
    rw [h2] at h3
    have h4 : (φ (O.A.H.rt : D.host.E)) ^ 2 = -(O.A.H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 D.host.E => φ (x : D.host.E)) O.A.H.rt_sq
      simpa using this
    have h5 : (φ (O.A.H.rt : D.host.E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
    have h6 := congrArg Complex.re h4
    simp [sq, h5] at h6
    have h7 : (0 : ℝ) < O.A.H.d := by exact_mod_cast O.A.H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (O.A.H.rt : D.host.E)).re]
  · exact h

theorem mem_cmSet_iff (σ τ : D.host.E →+* D.what₂.LL)
    (h : ∀ α : 𝓞 D.host.E, τ (α : D.host.E) = σ ((O.A.H.bar α : 𝓞 D.host.E) : D.host.E)) :
    σ ∈ cmSet O ↔ τ ∉ cmSet O := by
  simp only [cmSet, Set.mem_setOf_eq, O.κ.e_emb]
  have hrt : τ (O.A.H.rt : D.host.E) = -σ (O.A.H.rt : D.host.E) := by
    rw [h, bar_rt O]
    simp
  rw [hrt, map_neg]
  have hz : (D.what₂.embLL (σ (O.A.H.rt : D.host.E))) ^ 2 = O.A.H.rt0 ^ 2 := by
    rw [O.A.H.sqrt_neg_disc_sq]
    have := congrArg (fun x : 𝓞 D.host.E => D.what₂.embLL (σ (x : D.host.E))) O.A.H.rt_sq
    simpa using this
  have h0 : O.A.H.rt0 ≠ 0 := by
    intro h0
    have h5 := O.A.H.sqrt_neg_disc_sq
    have h6 := O.A.H.d_prime.ne_zero
    rw [h0] at h5
    simp at h5
    exact h6 (by exact_mod_cast h5)
  constructor
  · intro h1 h2
    apply h0
    linear_combination (-(1 : ℂ) / 2) * h1 + (-(1 : ℂ) / 2) * h2
  · intro h1
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hz with h2 | h2
    · exact h2
    · exact absurd (by rw [h2, neg_neg]) h1

end SetupThm

end GlobalTheory.EqHalf
