import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPartStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangulaStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatLinearParamBlockDiagKernelStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DescendBlockDiagPartRatPolyOfFibreConstStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.IdempotentCornerSection

section ring
variable {A : Type} [Ring A] {E : A}

lemma corner_mul (hE : E * E = E) {x y : A} (hx : E * x * (1 - E) = x) (hy : E * y * (1 - E) = y) :
    x * y = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc x * y = (E * x * (1 - E)) * (E * y * (1 - E)) := by rw [hx, hy]
    _ = E * x * ((1 - E) * E) * y * (1 - E) := by noncomm_ring
    _ = 0 := by rw [h]; simp

lemma diag_comm (hE : E * E = E) (g : A) :
    E * (E * g * E + (1 - E) * g * (1 - E)) = (E * g * E + (1 - E) * g * (1 - E)) * E := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h' : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  calc E * (E * g * E + (1 - E) * g * (1 - E))
      = (E * E) * g * E + (E * (1 - E)) * g * (1 - E) := by simp only [mul_add, mul_assoc]
    _ = E * g * (E * E) + (1 - E) * g * ((1 - E) * E) := by rw [hE, h, h']; simp
    _ = _ := by simp only [add_mul, mul_assoc]

lemma corner_mul_comm {x D : A} (hD : E * D = D * E) (hx : E * x * (1 - E) = x) :
    E * (x * D) * (1 - E) = x * D := by
  have h : D * (1 - E) = (1 - E) * D := by rw [mul_sub, sub_mul, hD, mul_one, one_mul]
  calc E * (x * D) * (1 - E) = E * x * (D * (1 - E)) := by simp only [mul_assoc]
    _ = E * x * (1 - E) * D := by rw [h]; simp only [mul_assoc]
    _ = x * D := by rw [hx]

lemma corner_idem (hE : E * E = E) (g : A) : E * (E * g * (1 - E)) * (1 - E) = E * g * (1 - E) := by
  have h : (1 - E) * (1 - E) = 1 - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hE, sub_self, sub_zero]
  calc E * (E * g * (1 - E)) * (1 - E) = (E * E) * g * ((1 - E) * (1 - E)) := by simp only [mul_assoc]
    _ = _ := by rw [hE, h]

lemma corner_diag (hE : E * E = E) {x : A} (hx : E * x * (1 - E) = x) :
    E * x * E + (1 - E) * x * (1 - E) = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc E * x * E + (1 - E) * x * (1 - E)
      = E * (E * x * (1 - E)) * E + (1 - E) * (E * x * (1 - E)) * (1 - E) := by rw [hx]
    _ = E * E * x * ((1 - E) * E) + ((1 - E) * E) * x * (1 - E) * (1 - E) := by simp only [mul_assoc]
    _ = 0 := by rw [h]; simp

lemma inv_comm {D D' : A} (hD : E * D = D * E) (h1 : D * D' = 1) (h2 : D' * D = 1) :
    E * D' = D' * E := by
  calc E * D' = (D' * D) * E * D' := by rw [h2, one_mul]
    _ = D' * (D * E) * D' := by simp only [mul_assoc]
    _ = D' * E * (D * D') := by rw [← hD]; simp only [mul_assoc]
    _ = D' * E := by rw [h1, mul_one]

end ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def beta {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (g : Matrix ι ι R) :
    Matrix ι ι R :=
  e.map (algebraMap ℚ R) * g * (1 - e.map (algebraMap ℚ R)) * (blk e g).adjugate

noncomputable def sec {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ)
    (g : Matrix ι ι R) : Matrix ι ι R :=
  (1 - linExt c (beta e g)) * g

section natural
variable {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)

lemma map_rat (e : Matrix ι ι ℚ) :
    φ.mapMatrix (e.map (algebraMap ℚ R)) = e.map (algebraMap ℚ S) := by
  ext i j; simp [AlgHom.mapMatrix_apply, -eq_ratCast]

lemma map_blk (e : Matrix ι ι ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (blk e g) = blk e (φ.mapMatrix g) := by
  simp only [blk, map_add, map_mul, map_sub, map_one, map_rat]

lemma map_linExt (c : ι × ι → ι × ι → ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (linExt c g) = linExt c (φ.mapMatrix g) := by
  ext i j; simp [linExt, AlgHom.mapMatrix_apply, map_sum, -eq_ratCast]

lemma map_sec (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (sec e c g) = sec e c (φ.mapMatrix g) := by
  simp only [sec, beta, map_mul, map_sub, map_one, map_rat, map_linExt, AlgHom.map_adjugate, map_blk]

end natural

lemma exists_poly (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ) :
    ∃ f : ι → ι → MvPolynomial (ι × ι) ℚ, ∀ (g : Matrix ι ι ℂ) i j, ev (f i j) g = sec e c g i j := by
  refine ⟨fun i j => sec e c (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ)) i j,
    fun g i j => ?_⟩
  have h := map_sec (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) e c
    (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ))
  have h2 : (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)).mapMatrix
      (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ)) = g := by
    ext k l; simp [AlgHom.mapMatrix_apply]
  rw [h2] at h
  rw [← h]; rfl

lemma linExt_sub (c : ι × ι → ι × ι → ℚ) (x y : Matrix ι ι ℂ) :
    linExt c (x - y) = linExt c x - linExt c y := by
  ext i j; simp [linExt, mul_sub, Finset.sum_sub_distrib]

lemma linExt_zero (c : ι × ι → ι × ι → ℚ) : linExt c (0 : Matrix ι ι ℂ) = 0 := by
  ext i j; simp [linExt]

end GlobalTheory.ClassFin.IdempotentCornerSection

open GlobalTheory.ClassFin.IdempotentCornerSection in

theorem GlobalTheory.ClassFin.exists_blk_section : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℂ)) = 1 ∧ ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) ∈ Γ ∧ blk e (Matrix.of fun i j => ev (b i j) (blk e g)) = blk e g ∧ g = (1 + linExt c (e.map (algebraMap ℚ ℂ) * g * (1 - e.map (algebraMap ℚ ℂ)) * (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)) := by
  intro ι _ _ Γ e hΓ he htri
  obtain ⟨c, hc, hfix⟩ := GlobalTheory.T.exists_rat_linear_param_blockDiag_kernel ι Γ e hΓ he
  have hpre := GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart ι Γ e hΓ.toIsPre he htri
  obtain ⟨hb1, -, hdec, hbb, -⟩ := GlobalTheory.T.blockDiagPartOfRatIdempotent_one_and_mul_of_triangular ι e ℂ he
  obtain ⟨f, hf⟩ := exists_poly e c
  have hE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, he]
  have hcomm : ∀ g : Matrix ι ι ℂ, e.map (algebraMap ℚ ℂ) * blk e g = blk e g * e.map (algebraMap ℚ ℂ) :=
    fun g => diag_comm hE g
  have hdet : ∀ g ∈ Γ, (blk e g).det = 1 := fun g hg => hpre.det_eq _ ⟨g, hg, rfl⟩
  have h1 : ∀ g ∈ Γ, blk e g * (blk e g).adjugate = 1 := fun g hg => by
    rw [Matrix.mul_adjugate, hdet g hg, one_smul]
  have h2 : ∀ g ∈ Γ, (blk e g).adjugate * blk e g = 1 := fun g hg => by
    rw [Matrix.adjugate_mul, hdet g hg, one_smul]
  have hβ : ∀ g ∈ Γ, e.map (algebraMap ℚ ℂ) * beta e g * (1 - e.map (algebraMap ℚ ℂ)) = beta e g :=
    fun g hg => corner_mul_comm (inv_comm (hcomm g) (h1 g hg) (h2 g hg)) (corner_idem hE g)
  have hg1 : ∀ g ∈ Γ, g = (1 + beta e g) * blk e g := fun g hg => by
    rw [add_mul, one_mul, beta, mul_assoc _ _ (blk e g), h2 g hg, mul_one]
    exact hdec g (htri g hg)
  have hs : ∀ g ∈ Γ, sec e c g = (1 + (beta e g - linExt c (beta e g))) * blk e g := fun g hg => by
    have h0 := corner_mul hE (hc (beta e g)).2 (hβ g hg)
    have : sec e c g = (1 - linExt c (beta e g)) * ((1 + beta e g) * blk e g) := by
      rw [← hg1 g hg]; rfl
    rw [this, ← mul_assoc]
    congr 1
    rw [mul_add, sub_mul, sub_mul, h0]
    simp only [mul_one, one_mul, sub_zero]
    abel
  have hsub : ∀ x y : Matrix ι ι ℂ, e.map (algebraMap ℚ ℂ) * x * (1 - e.map (algebraMap ℚ ℂ)) = x →
      e.map (algebraMap ℚ ℂ) * y * (1 - e.map (algebraMap ℚ ℂ)) = y →
      e.map (algebraMap ℚ ℂ) * (x - y) * (1 - e.map (algebraMap ℚ ℂ)) = x - y := fun x y hx hy => by
    rw [mul_sub (e.map (algebraMap ℚ ℂ)) x y, sub_mul, hx, hy]
  have hconst : ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → sec e c x = sec e c x' := by
    intro x hx x' hx' hxx
    have hε := hsub _ _ (hβ x hx) (hβ x' hx')
    have h0 := corner_mul hE hε (hβ x' hx')
    have hxe : x = (1 + (beta e x - beta e x')) * x' := by
      have : (1 + (beta e x - beta e x')) * x'
          = (1 + (beta e x - beta e x')) * ((1 + beta e x') * blk e x') := by rw [← hg1 x' hx']
      rw [this, ← mul_assoc, ← hxx]
      have h3 : (1 + (beta e x - beta e x')) * (1 + beta e x') = 1 + beta e x := by
        rw [mul_add, add_mul _ _ (beta e x'), h0]
        simp only [mul_one, one_mul, add_zero]
        abel
      rw [h3]; exact hg1 x hx
    have hmem : 1 + (beta e x - beta e x') ∈ Γ := by
      have h4 : x * x'.adjugate = 1 + (beta e x - beta e x') := by
        have : x * x'.adjugate = ((1 + (beta e x - beta e x')) * x') * x'.adjugate := by rw [← hxe]
        rw [this, mul_assoc, Matrix.mul_adjugate, hΓ.det_eq x' hx', one_smul, mul_one]
      rw [← h4]
      exact hΓ.mul_mem _ hx _ (hΓ.adj_mem _ hx')
    have h5 := hfix _ hmem hε
    rw [linExt_sub] at h5
    rw [hs x hx, hs x' hx', hxx]
    congr 2
    rw [sub_eq_iff_eq_add.mp h5]
    abel
  have hb : ∀ i j, ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev (f i j) x = ev b (blk e x) := fun i j =>
    GlobalTheory.T.descend_blockDiagPart_ratPoly_of_fibre_const ι Γ e hΓ he htri (f i j) fun x hx x' hx' hxx => by
      rw [hf, hf, hconst x hx x' hx' hxx]
  choose b hb using hb
  have hbs : ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) = sec e c g := fun g hg => by
    ext i j; rw [Matrix.of_apply, ← hb i j g hg, hf]
  refine ⟨c, b, hc, ?_, fun g hg => ?_⟩
  · have h := hbs 1 hΓ.one_mem
    rw [hb1] at h
    rw [h]
    have h0 : beta e (1 : Matrix ι ι ℂ) = 0 := by
      rw [beta, mul_one, mul_sub, mul_one, hE, sub_self, zero_mul]
    rw [sec, h0, linExt_zero, sub_zero, mul_one]
  · rw [hbs g hg]
    refine ⟨?_, ?_, ?_⟩
    · have h := (hc (0 - beta e g)).1
      rw [linExt_sub, linExt_zero, ← add_sub_assoc, add_zero] at h
      exact hΓ.mul_mem _ h _ hg
    · have h := corner_diag hE (corner_mul_comm (hcomm g) (hsub _ _ (hβ g hg) (hc (beta e g)).2))
      have h' := hbb g
      rw [hs g hg, add_mul, one_mul]
      generalize (beta e g - linExt c (beta e g)) * blk e g = y at h
      generalize blk e g = D at h' ⊢
      have : blk e (D + y) = blk e D + (e.map (algebraMap ℚ ℂ) * y * e.map (algebraMap ℚ ℂ) +
          (1 - e.map (algebraMap ℚ ℂ)) * y * (1 - e.map (algebraMap ℚ ℂ))) := by
        simp only [blk, mul_add, add_mul]; abel
      rw [this, h, h', add_zero]
    · have h0 := corner_mul hE (hc (beta e g)).2 (hc (beta e g)).2
      change g = (1 + linExt c (beta e g)) * ((1 - linExt c (beta e g)) * g)
      rw [← mul_assoc, mul_sub, add_mul _ _ (linExt c (beta e g)), h0]
      simp
