import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilParts GlobalTheory.VacuumCharacter
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactFockAction

section Blocks

variable {m n : ℕ}

def blockExt (ε : Fin n → Bool) (e : Bool) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if ε i = e then a i j else if i = j then 1 else 0

def IsBlock (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, ε i ≠ ε j → a i j = 0

theorem det_blockExt (ε : Fin n → Bool) (e : Bool) (a : Matrix (Fin n) (Fin n) ℂ) :
    (blockExt ε e a).det = signBlockDeterminant ε e a := by
  rw [Matrix.twoBlockTriangular_det (blockExt ε e a) (fun i => ε i = e) (fun i hi j hj => by
    have : i ≠ j := fun h => hi (h ▸ hj)
    simp [blockExt, hi, this])]
  have e1 : toSquareBlockProp (blockExt ε e a) (fun i => ¬ ε i = e) = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toSquareBlockProp_def, blockExt, hi, Matrix.one_apply]
  have e2 : toSquareBlockProp (blockExt ε e a) (fun i => ε i = e) =
      a.submatrix (Subtype.val : {a // ε a = e} → Fin n) (Subtype.val : {a // ε a = e} → Fin n) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toSquareBlockProp_def, blockExt, hi]
  rw [e1, e2, Matrix.det_one, mul_one]
  unfold signBlockDeterminant
  congr

theorem det_eq_signBlockDeterminant_mul_of_isSignBlockMatrix {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsBlock ε a) :
    a.det = signBlockDeterminant ε true a * signBlockDeterminant ε false a := by
  rw [← det_blockExt, ← det_blockExt, ← Matrix.det_mul]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  cases hi : ε i
  · rw [Finset.sum_eq_single i]
    · simp [blockExt, hi]
    · intro k _ hk
      simp [blockExt, hi, Ne.symm hk]
    · simp
  · rw [Finset.sum_eq_single j]
    · by_cases hj : ε j = false
      · simp [blockExt, hi, ha i j (by simp [hi, hj])]
      · simp [blockExt, hi, hj]
    · intro k _ hk
      by_cases hj : ε k = false
      · simp [blockExt, hi, ha i k (by simp [hi, hj])]
      · simp [blockExt, hj, hk]
    · simp

theorem signBlockDeterminant_mul_eq_one_of_mul_eq_one {ε : Fin n → Bool} (e : Bool) {a a' : Matrix (Fin n) (Fin n) ℂ} (ha : IsBlock ε a)
    (h : a * a' = 1) : signBlockDeterminant ε e a * signBlockDeterminant ε e a' = 1 := by
  rw [← det_blockExt, ← det_blockExt, ← Matrix.det_mul, ← Matrix.det_one (n := Fin n) (R := ℂ)]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : ε i = e
  · rw [← h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : ε k = e
    · simp [blockExt, hi, hk]
    · simp [blockExt, hi, ha i k (fun h' => hk (h' ▸ hi))]
  · rw [Finset.sum_eq_single i]
    · simp [blockExt, hi, Matrix.one_apply]
    · intro k _ hk
      simp [blockExt, hi, Ne.symm hk]
    · simp

theorem signBlockDeterminant_transpose_eq (ε : Fin n → Bool) (e : Bool) (a : Matrix (Fin n) (Fin n) ℂ) :
    signBlockDeterminant ε e aᵀ = signBlockDeterminant ε e a := by
  unfold signBlockDeterminant
  rw [← Matrix.det_transpose]
  rfl

theorem detPlus_block {ε : Fin n → Bool} {ε' : Fin m → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    {b : Matrix (Fin m) (Fin m) ℂ} (ha : IsBlock ε a) (hb : IsBlock ε' b) :
    detPlus (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') a b = (∏ i, signBlockDeterminant ε (ε' i) a) * ∏ j, signBlockDeterminant ε' (ε j) b := by
  have e : (1 / 2 : ℂ) • ((1 + Formalism.REAL.Jm ε' ⊗ₖ (Formalism.REAL.Jm ε)ᵀ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε' ⊗ₖ (Formalism.REAL.Jm ε)ᵀ) =
      (blockDiagonal fun i => blockExt ε (ε' i) aᵀ).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) *
        blockDiagonal fun j => blockExt ε' (ε j) b := by
    unfold Formalism.REAL.Jm
    rw [diagonal_transpose, diagonal_kronecker_diagonal, ← diagonal_one, diagonal_add, diagonal_sub]
    ext ⟨i, j⟩ ⟨l, k⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single (i, k)]
    · have h1 := ha k j
      have h2 := hb i l
      simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_mul, kroneckerMap_apply, transpose_apply,
        submatrix_apply, Equiv.prodComm_apply, Prod.swap, blockDiagonal_apply, blockExt, of_apply, diagonal_apply,
        Prod.mk.injEq, smul_eq_mul, if_true]
      by_cases h3 : ε j = ε' i
      · by_cases h4 : ε' i = ε k
        · rw [if_pos h3, if_pos h4, h3]
          cases ε' i <;> simp <;> ring
        · rw [if_pos h3, h1 (by rw [h3]; exact Ne.symm h4), h3]
          cases ε' i <;> simp
      · rw [if_neg h3]
        have h5 : (if ε' i = true then (1 : ℂ) else -1) * (if ε j = true then 1 else -1) = -1 := by
          cases h6 : ε j <;> cases h7 : ε' i <;> simp_all
        rw [h5]
        by_cases h4 : j = k
        · subst h4
          rw [if_neg (Ne.symm h3)]
          by_cases h6 : i = l <;> simp [h6]
          norm_num
        · simp [h4]
    · rintro ⟨i', k'⟩ _ hne
      simp only [submatrix_apply, Equiv.prodComm_apply, Prod.swap, blockDiagonal_apply]
      by_cases h1 : i = i'
      · subst h1
        rw [if_neg (show ¬ k' = k from fun h => hne (by rw [h])), mul_zero]
      · rw [if_neg h1, zero_mul]
    · simp
  unfold detPlus
  rw [e, Matrix.det_mul, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, Matrix.det_blockDiagonal]
  simp only [det_blockExt, signBlockDeterminant_transpose_eq]

theorem detPlus_conj {F F' : Matrix (Fin n) (Fin n) ℂ} {G G' : Matrix (Fin m) (Fin m) ℂ} (hF : F * F' = 1)
    (hG : G * G' = 1) (s a : Matrix (Fin n) (Fin n) ℂ) (t b : Matrix (Fin m) (Fin m) ℂ) :
    detPlus (F' * s * F) (G' * t * G) (F' * a * F) (G' * b * G) = detPlus s t a b := by
  have hP : (G ⊗ₖ F'ᵀ) * (G' ⊗ₖ Fᵀ) = 1 := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, hF, hG, Matrix.transpose_one, Matrix.one_kronecker_one]
  have hP' := mul_eq_one_comm.1 hP
  have e : ∀ x y, (G' * y * G) ⊗ₖ (F' * x * F)ᵀ = (G' ⊗ₖ Fᵀ) * (y ⊗ₖ xᵀ) * (G ⊗ₖ F'ᵀ) := fun x y => by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.mul_assoc Fᵀ]
  unfold detPlus
  rw [e, e]
  generalize G ⊗ₖ F'ᵀ = P at hP hP'
  generalize G' ⊗ₖ Fᵀ = P' at hP hP'
  generalize t ⊗ₖ sᵀ = X
  generalize b ⊗ₖ aᵀ = Y
  have e2 : (1 / 2 : ℂ) • ((1 + P' * X * P) * (P' * Y * P)) + (1 / 2 : ℂ) • (1 - P' * X * P) =
      P' * ((1 / 2 : ℂ) • ((1 + X) * Y) + (1 / 2 : ℂ) • (1 - X)) * P := by
    have : P' * X * P * (P' * Y * P) = P' * (X * Y) * P := by
      calc _ = P' * X * (P * P') * Y * P := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one, hP', this, smul_add, smul_sub]
  rw [e2, Matrix.det_mul_comm, ← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem prod_bool (ε : Fin n → Bool) (c : Bool → ℂ) :
    ∏ i, c (ε i) = c true ^ (Finset.univ.filter fun i => ε i = true).card *
      c false ^ (Finset.univ.filter fun i => ε i = false).card := by
  rw [← Finset.prod_fiberwise Finset.univ ε, Fintype.prod_bool]
  congr 1 <;> exact Finset.prod_eq_pow_card fun i hi => by rw [(Finset.mem_filter.1 hi).2]

theorem card_sign (ε : Fin n → Bool) (e : Bool) :
    ((Finset.univ.filter fun i => ε i = e).card : ℚ) = n / 2 + if e then idx ε / 2 else -(idx ε / 2) := by
  have hn : (n : ℚ) = ∑ _i : Fin n, (1 : ℚ) := by simp
  rw [Finset.card_filter, hn]
  unfold idx
  push_cast
  cases e
  · simp only [Bool.false_eq_true, if_false, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> norm_num
  · simp only [if_true, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> norm_num

end Blocks

variable {D : D7}

section Frames

variable {V : HSp D} (A : Fr V) (τ : D.what₂.Tau)

theorem fr_mul_inv : A.fr τ * (A.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))

theorem inv_mul_fr : (A.fr τ)⁻¹ * A.fr τ = 1 := mul_eq_one_comm.1 (fr_mul_inv A τ)

theorem cart_isCartanInv : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have h1 := fr_mul_inv A τ
  have h2 := inv_mul_fr A τ
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJ' := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hG : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ]; unfold Fr.cart
    calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : A.cart τ * A.cart τ = 1 := by
    unfold Fr.cart
    calc _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← A.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (A.fr_unit τ))

variable {τ} {h : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem unfr_mem (hh : h ∈ Formalism.REAL.Kset (A.ε τ)) : (A.fr τ)⁻¹ * h * A.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  show ((A.fr τ)⁻¹ * h * A.fr τ)ᴴ * gramAt D V τ * ((A.fr τ)⁻¹ * h * A.fr τ) = gramAt D V τ
  have h1 := fr_mul_inv A τ
  have h2 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have h3 : hᴴ * h = 1 := Matrix.mem_unitaryGroup_iff'.1 hh.1
  rw [← A.fr_gram τ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = (A.fr τ)ᴴ * (hᴴ * ((((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * h)) *
        A.fr τ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, ← hh.2, ← Matrix.mul_assoc hᴴ, h3, Matrix.one_mul]

open Classical in

def atPl {k : ℕ} (τ : D.what₂.Tau) (h : Matrix (Fin k) (Fin k) ℂ) (ρ : D.what₂.Tau) : Matrix (Fin k) (Fin k) ℂ :=
  if ρ = τ then h else 1

theorem atPl_mem (hh : h ∈ Formalism.REAL.Kset (A.ε τ)) (ρ : D.what₂.Tau) : atPl τ h ρ ∈ Formalism.REAL.Kset (A.ε ρ) := by
  unfold atPl
  split_ifs with e
  · rw [e]; exact hh
  · exact ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem compAt_elt {θ : InfFam D} (hθ : IsInfFam θ) (hh : h ∈ Formalism.REAL.Kset (A.ε τ)) (ρ : D.what₂.Tau) :
    compAt θ ρ (Formalism.L2.Theta.mt V (A.elt θ τ h)) = (A.fr ρ)⁻¹ * atPl τ h ρ * A.fr ρ := by
  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (unfr_mem A hh)
  unfold atPl
  split_ifs with e
  · rw [e]; exact hs.2.1
  · rw [Matrix.mul_one, inv_mul_fr]; exact hs.2.2 ρ e

theorem cart_comm (hh : h ∈ Formalism.REAL.Kset (A.ε τ)) :
    A.cart τ * ((A.fr τ)⁻¹ * h * A.fr τ) = (A.fr τ)⁻¹ * h * A.fr τ * A.cart τ := by
  unfold Fr.cart
  calc _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * h) * A.fr τ := by simp only [Matrix.mul_assoc]
    _ = (A.fr τ)⁻¹ * (h * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
      rw [fr_mul_inv, Matrix.mul_one, Matrix.mul_one, hh.2]
    _ = _ := by simp only [Matrix.mul_assoc]

end Frames

section Characters

variable {θ : InfFam D}

theorem isDetRoot_at (hθ : IsInfFam θ) (V : HSp D) {g : GA D V} (hg : g ∈ GinfC V) (x : (AE D)ˣ)
    (hf : finPart D (x : AE D) = 1) (hn : ∀ ρ, ‖θ ρ (infPart D (x : AE D))‖ = 1)
    (hd : ∀ ρ, θ ρ (infPart D (x : AE D)) ^ 2 = (compAt θ ρ (Formalism.L2.Theta.mt V g)).det) : IsDetRoot V g x := by
  refine adele_ext hθ ?_ fun τ => ?_
  · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
      have hg' : finHom V g = 1 := hg
      have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
      rw [RingHom.map_det]
      exact (congrArg Matrix.det this).trans Matrix.det_one
    rw [map_mul, hf]
    exact ((congrArg₂ (· * ·) hd (finPart_cA _ hf)).trans (one_mul 1)).symm
  · rw [map_mul, map_mul]
    have e1 := GlobalTheory.FockCompare.comp_cA hθ τ (x : AE D)
    have e2 := det_compAt θ τ (Formalism.L2.Theta.mt V g)
    refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
    have h1 := hn τ
    rw [← hd]
    generalize θ τ (infPart D (x : AE D)) = w at h1
    have : w * starRingEnd ℂ w = 1 := by rw [Complex.mul_conj', h1]; simp
    linear_combination (-w) * this

theorem exists_root_at (hθ : IsInfFam θ) (V : HSp D) {g : GA D V} (hg : g ∈ GinfC V) (τ : D.what₂.Tau) (w : ℂ)
    (hw : ‖w‖ = 1) (h1 : w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det)
    (h2 : ∀ ρ, ρ ≠ τ → (compAt θ ρ (Formalism.L2.Theta.mt V g)).det = 1) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (a : ℚ) (n : ℤ), HasInfExp D ν τ a → (n : ℚ) = 2 * a →
      ((ν x : Circle) : ℂ) = w ^ n := by
  classical
  obtain ⟨x, hx1, hx2⟩ := exists_idele_at hθ τ w fun h => by simp [h] at hw
  refine ⟨x, isDetRoot_at hθ V hg x hx1 (fun ρ => ?_) fun ρ => ?_, fun ν a n hν hn => ?_⟩
  · rw [hx2]; split_ifs
    exacts [hw, norm_one]
  · rw [hx2]; split_ifs with e
    · rw [e, h1]
    · rw [h2 ρ e, one_pow]
  · obtain ⟨n', hn', -, h⟩ := hν
    have e : n' = n := by exact_mod_cast hn'.trans hn.symm
    rw [h θ hθ x hx1 (fun ρ h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw, e]
    simp

theorem exp_int (hθ : IsInfFam θ) (V : HSp D) {ν : (AE D)ˣ →* Circle} (h0 : ResEta D ν 0) {τ : D.what₂.Tau} {a : ℚ}
    (ha : HasInfExp D ν τ a) : ∃ c : ℤ, (c : ℚ) = a := by
  have hc : ∀ ρ, (compAt θ ρ (Formalism.L2.Theta.mt V 1)).det = 1 := fun ρ => by
    rw [show compAt θ ρ (Formalism.L2.Theta.mt V 1) = 1 from GlobalTheory.PointAtPlaceHom.infMat_one _ (θ ρ), Matrix.det_one]
  obtain ⟨x, hx, hxv⟩ := exists_root_at hθ V (one_mem _) τ 1 norm_one (by rw [hc, one_pow]) fun ρ _ => hc ρ
  obtain ⟨y, hy, hyv⟩ := exists_root_at hθ V (one_mem _) τ (-1) (by simp) (by rw [hc]; norm_num)
    fun ρ _ => hc ρ
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℚ) = 2 * a := ⟨_, ha.choose_spec.1⟩
  obtain ⟨u, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D _).2.1 _ x y hx hy
  obtain ⟨η, hη⟩ := h0.1
  have e := hyv ν a n ha hn
  rw [map_mul, h0.2 η hη, pow_zero, mul_one, hxv ν a n ha hn, _root_.one_zpow] at e
  rcases Int.even_or_odd n with ⟨c, hc⟩ | ho
  · refine ⟨c, ?_⟩
    rw [hc] at hn
    push_cast at hn
    linarith
  · rw [ho.neg_one_zpow] at e
    norm_num at e

theorem exp_twist_int (hθ : IsInfFam θ) (V : HSp D) {χ η : (AE D)ˣ →* Circle} {k : ℕ} (hχ : ResEta D χ k) (hη : ResEta D η 1)
    {τ : D.what₂.Tau} {a : ℚ} (ha : HasInfExp D χ τ a) (he : HasInfExp D η τ (1 / 2)) :
    ∃ c : ℤ, (c : ℚ) = a - k / 2 := by
  refine exp_int hθ V ⟨hχ.1, fun e he a => ?_⟩ (hasInfExp_twist ha he k)
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, hχ.2 e he a, hη.2 e he a, pow_one,
    pow_zero, mul_inv_cancel]

theorem exists_root_elt (hθ : IsInfFam θ) {V : HSp D} (A : Fr V) {τ : D.what₂.Tau}
    {h : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hh : h ∈ Formalism.REAL.Kset (A.ε τ)) :
    ∃ x, IsDetRoot V (A.elt θ τ h) x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : ℤ), HasInfExp D ν τ c →
      ((ν x : Circle) : ℂ) = h.det ^ c := by
  have hd : ∀ ρ, (compAt θ ρ (Formalism.L2.Theta.mt V (A.elt θ τ h))).det = (atPl τ h ρ).det := fun ρ => by
    rw [compAt_elt A hθ hh, Matrix.det_mul_comm, ← Matrix.mul_assoc, fr_mul_inv, Matrix.one_mul]
  have hu : ‖h.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hh.1)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq h.det two_pos
  obtain ⟨x, hx, hv⟩ := exists_root_at hθ V (GlobalTheory.PointAtPlaceHom.atTau_mem V τ ((A.fr τ)⁻¹ * h * A.fr τ)) τ w
    ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, hw, hu]))
    (hw.trans ((hd τ).trans (by rw [atPl, if_pos rfl])).symm)
    fun ρ e => (hd ρ).trans (by rw [atPl, if_neg e, Matrix.det_one])
  refine ⟨x, hx, fun ν c hc => ?_⟩
  rw [hv ν c (2 * c) hc (by push_cast; rfl), ← hw, _root_.zpow_mul]
  simp

end Characters

section Fock

variable {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (A : Fr V) (B : Fr W)

theorem isBlock_of_mem {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    IsBlock ε k := fun _ _ h => GlobalTheory.FockSubst.kset_zero hk h

theorem Jm_single (τ : D.what₂.Tau) (a : Fin W.rank) (b : Fin V.rank) :
    cplxO (A.cart τ) (B.cart τ) (Datum.unitMap (A.onb τ) (B.onb τ) a b) =
      ((if decide (B.ε τ a = A.ε τ b) = true then 1 else -1 : ℂ) * Complex.I) •
        Datum.unitMap (A.onb τ) (B.onb τ) a b := by
  have e : Formalism.REAL.Jm (B.ε τ) * single a b (1 : ℂ) * Formalism.REAL.Jm (A.ε τ) =
      (if decide (B.ε τ a = A.ε τ b) = true then 1 else -1 : ℂ) • single a b (1 : ℂ) := by
    ext p q
    rw [Formalism.REAL.Jm, Formalism.REAL.Jm, mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : a = p ∧ b = q
    · rw [← h.1, ← h.2]
      cases B.ε τ a <;> cases A.ε τ b <;> simp
    · simp [h]
  unfold cplxO Datum.unitMap Fr.cart Fr.onb
  rw [Matrix.inv_eq_right_inv (inv_mul_fr A τ), mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc _ = (B.fr τ)⁻¹ * (Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) * single a b (1 : ℂ) * (A.fr τ * (A.fr τ)⁻¹) *
        Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [fr_mul_inv, fr_mul_inv, Matrix.mul_one, Matrix.mul_one, e, Matrix.mul_smul, Matrix.smul_mul]

theorem pureTensorO_move (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {h : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hh : h ∈ Formalism.REAL.Kset (A.ε τ))
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (B.ε τ)) {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (P : PolF D W.rank V.rank) :
    pureTensorO ψ θ V W A.cart B.cart (fun ρ => A.onb ρ * atPl τ h ρ) (fun ρ => B.onb ρ * atPl τ k ρ) f P =
      ptF ψ θ A B f (subst τ (A.ε τ) (B.ε τ) (h.map (starRingEnd ℂ)) k P) := by
  classical
  let c : FVar D W.rank V.rank → Fin W.rank × Fin V.rank → ℂ := fun v p =>
    if B.ε v.1 v.2.1 = A.ε v.1 v.2.2 then atPl τ k v.1 p.1 v.2.1 * star (atPl τ h v.1 p.2 v.2.2)
    else star (atPl τ k v.1 p.1 v.2.1 * star (atPl τ h v.1 p.2 v.2.2))
  have key : ∀ (v : FVar D W.rank V.rank) g, IsThetaFunO ψ V W g →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) (fun ρ => A.onb ρ * atPl τ h ρ)
        (fun ρ => B.onb ρ * atPl τ k ρ) v g =
      ∑ p, c v p • aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A.onb B.onb (v.1, p.1, p.2) g := by
    rintro ⟨ρ, i, j⟩ g hg
    simp only [aPlusAll]
    rw [GlobalTheory.FockBasis.unitMap_mul, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (Jm_single A B ρ a b)]
    congr 1
    have hu := atPl_mem A hh ρ
    have hv := atPl_mem B hk ρ
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu.1), Matrix.star_apply]
    simp only [c]
    by_cases h1 : B.ε ρ a = B.ε ρ i
    · by_cases h2 : A.ε ρ b = A.ε ρ j
      · rw [h1, h2]
        simp only [decide_eq_true_eq]
        rfl
      · simp [isBlock_of_mem hu b j h2]
    · simp [isBlock_of_mem hv a i h1]
  have hS := cart_isCartanInv A
  have hT := cart_isCartanInv B
  have e : MvPolynomial.aeval (fun v : FVar D W.rank V.rank =>
      ∑ p, c v p • (MvPolynomial.X (v.1, p.1, p.2) : PolF D W.rank V.rank)) =
      subst τ (A.ε τ) (B.ε τ) (h.map (starRingEnd ℂ)) k := by
    unfold subst
    congr 1
    funext ⟨ρ, i, j⟩
    by_cases hρ : ρ = τ
    · subst hρ
      simp only [c, atPl, if_true, Fintype.sum_prod_type, Matrix.map_apply]
      rfl
    · simp only [c, atPl, if_neg hρ]
      rw [Finset.sum_eq_single (i, j)]
      · simp
      · rintro ⟨a, b⟩ _ hne
        by_cases h1 : a = i
        · have h2 : b ≠ j := fun h2 => hne (by rw [h1, h2])
          simp [Matrix.one_apply_ne h2]
        · simp [Matrix.one_apply_ne h1]
      · simp
  rw [← e]
  unfold ptF pureTensorO
  have hA : ∀ X Y i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ X Y i f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (f + f') =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f +
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f' :=
    fun _ _ _ _ _ h h' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ X Y i (a : ℂ) f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (a • f) =
      a • aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f :=
    fun _ _ _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ X Y i j f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j f) =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ i j _ h => GlobalTheory.FockSubst.aPlus_comm (sS := A.cart) (sT := B.cart) hψ hθ i.1 _ hS hT j.1 _ h
  exact GlobalTheory.FockSubst.pure_subst (P := IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (hA _ _) (Ac _ _) (Aadd _ _) (Asm _ _) (hA _ _) (Ac _ _) (Aadd _ _)
    (Asm _ _) c (fun v p => (v.1, p.1, p.2)) key hf P

end Fock

theorem detPlus_one_one {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) :
    detPlus s t 1 1 = 1 := by
  unfold detPlus
  rw [Matrix.transpose_one, Matrix.one_kronecker_one, Matrix.mul_one, ← smul_add, add_add_sub_cancel, smul_add,
    ← add_smul]
  norm_num

theorem compactFockAll : ∀ D : D7, GlobalTheory.ChainFr.CompactFockAll D := by
  intro D V W A B θ ψ χS χT ω f τ aS aT hθ hW hS hT hf _
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  obtain ⟨cS, hcS⟩ := exp_twist_int hθ V hW.resS e3 hS (e2 τ)
  obtain ⟨cT, hcT⟩ := exp_twist_int hθ V hW.resT e3 hT (e2 τ)
  refine ⟨fun e => -cT - ((Finset.univ.filter fun i => B.ε τ i = e).card : ℕ),
    fun e => cS + ((Finset.univ.filter fun j => A.ε τ j = e).card : ℕ), fun j => ?_, fun i => ?_,
    fun h hh k hk P => ?_⟩
  · push_cast
    rw [card_sign, hcT, wtS]
    split_ifs <;> ring
  · push_cast
    rw [card_sign, hcS, wtT]
    split_ifs <;> ring
  obtain ⟨x, hx, hxv⟩ := exists_root_elt hθ A hh
  obtain ⟨y, hy, hyv⟩ := exists_root_elt hθ B hk
  have c1 : ∀ ρ, A.cart ρ * compAt θ ρ (Formalism.L2.Theta.mt V (A.elt θ τ h)) =
      compAt θ ρ (Formalism.L2.Theta.mt V (A.elt θ τ h)) * A.cart ρ := fun ρ => by
    rw [compAt_elt A hθ hh]; exact cart_comm A (atPl_mem A hh ρ)
  have c2 : ∀ ρ, B.cart ρ * compAt θ ρ (Formalism.L2.Theta.mt W (B.elt θ τ k)) =
      compAt θ ρ (Formalism.L2.Theta.mt W (B.elt θ τ k)) * B.cart ρ := fun ρ => by
    rw [compAt_elt B hθ hk]; exact cart_comm B (atPl_mem B hk ρ)
  have hvac := GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D ψ hW.std V W θ hθ χS χT ω η ⟨e1, e4, e3, e2⟩ hW A.cart B.cart (cart_isCartanInv A)
    (cart_isCartanInv B) (A.elt θ τ h) (GlobalTheory.PointAtPlaceHom.atTau_mem V τ _) (B.elt θ τ k)
    (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _) c1 c2 x y hx hy f hf.1 hf.2
  have hmove := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χS χT ω hW hθ A.cart A.cart A.onb
    (fun ρ => A.onb ρ * atPl τ h ρ) B.cart B.cart B.onb (fun ρ => B.onb ρ * atPl τ k ρ) (A.elt θ τ h) (B.elt θ τ k)
    c1 c2
    (fun ρ => by rw [compAt_elt A hθ hh, Fr.onb, Matrix.mul_assoc, fr_mul_inv, Matrix.mul_one])
    (fun ρ => by rw [compAt_elt B hθ hk, Fr.onb, Matrix.mul_assoc, fr_mul_inv, Matrix.mul_one]) f hf.1 P).2
  refine hmove.trans ?_
  rw [hvac, GlobalTheory.FiniteFock.pureTensorO_smul, pureTensorO_move A B hW.std hθ hh hk hf.1]
  congr 1
  have hinv : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt V (A.elt θ τ h)⁻¹) = (A.fr ρ)⁻¹ * (atPl τ h ρ)ᴴ * A.fr ρ := fun ρ => by
    have h1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (A.elt θ τ h)
    rw [compAt_elt A hθ hh] at h1
    rw [← Matrix.inv_eq_right_inv h1]
    refine Matrix.inv_eq_right_inv ?_
    have h2 : atPl τ h ρ * (atPl τ h ρ)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 (atPl_mem A hh ρ).1
    calc _ = (A.fr ρ)⁻¹ * (atPl τ h ρ * (A.fr ρ * (A.fr ρ)⁻¹) * (atPl τ h ρ)ᴴ) * A.fr ρ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [fr_mul_inv, Matrix.mul_one, h2, Matrix.mul_one, inv_mul_fr]
  have hdp : ∀ ρ, detPlus (A.cart ρ) (B.cart ρ) (compAt θ ρ (Formalism.L2.Theta.mt V (A.elt θ τ h)⁻¹))
      (compAt θ ρ (Formalism.L2.Theta.mt W (B.elt θ τ k))) =
      detPlus (Formalism.REAL.Jm (A.ε ρ)) (Formalism.REAL.Jm (B.ε ρ)) (atPl τ h ρ)ᴴ (atPl τ k ρ) := fun ρ => by
    rw [hinv, compAt_elt B hθ hk]
    exact detPlus_conj (fr_mul_inv A ρ) (fr_mul_inv B ρ) _ _ _ _
  have bh := isBlock_of_mem hh
  have bk := isBlock_of_mem hk
  have bh' : IsBlock (A.ε τ) hᴴ := fun i j e => by rw [Matrix.conjTranspose_apply, bh j i e.symm, star_zero]
  have ih := fun e => signBlockDeterminant_mul_eq_one_of_mul_eq_one e bh (show h * hᴴ = 1 from Matrix.mem_unitaryGroup_iff.1 hh.1)
  have ik := fun e => signBlockDeterminant_mul_eq_one_of_mul_eq_one e bk (show k * kᴴ = 1 from Matrix.mem_unitaryGroup_iff.1 hk.1)
  simp only [hdp]
  rw [Finset.prod_eq_single τ (fun ρ _ e => by
      rw [atPl, atPl, if_neg e, if_neg e, Matrix.conjTranspose_one, detPlus_one_one]) (by simp),
    atPl, atPl, if_pos rfl, if_pos rfl, detPlus_block bh' bk, prod_bool _ fun e => signBlockDeterminant (A.ε τ) e hᴴ,
    prod_bool _ fun e => signBlockDeterminant (B.ε τ) e k, Circle.coe_mul, Circle.coe_inv,
    hxv _ cT (by rw [hcT]; exact hasInfExp_twist hT (e2 τ) _),
    hyv _ cS (by rw [hcS]; exact hasInfExp_twist hS (e2 τ) _), det_eq_signBlockDeterminant_mul_of_isSignBlockMatrix bh, det_eq_signBlockDeterminant_mul_of_isSignBlockMatrix bk,
    eq_inv_of_mul_eq_one_right (ih true), eq_inv_of_mul_eq_one_right (ih false)]
  have n1 := left_ne_zero_of_mul_eq_one (ih true)
  have n2 := left_ne_zero_of_mul_eq_one (ih false)
  have n3 := left_ne_zero_of_mul_eq_one (ik true)
  have n4 := left_ne_zero_of_mul_eq_one (ik false)
  simp only [zpow_sub₀ n1, zpow_sub₀ n2, zpow_add₀ n3, zpow_add₀ n4, mul_zpow, zpow_natCast, _root_.zpow_neg, inv_pow,
    mul_inv, div_eq_mul_inv]
  ring

end GlobalTheory.CompactFockAction

end
