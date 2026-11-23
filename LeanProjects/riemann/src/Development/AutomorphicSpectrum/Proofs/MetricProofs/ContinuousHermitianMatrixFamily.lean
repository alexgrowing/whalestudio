import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.HmCont

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {g : ℕ}

def cvec (z : Fin g → ℂ) : Fin g ⊕ Fin g → ℝ :=
  Sum.elim (fun k => (z k).re) (fun k => (z k).im)

def realBlock (H : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  Matrix.fromBlocks (H.map Complex.im) (-(H.map Complex.re)) (H.map Complex.re) (H.map Complex.im)

theorem cvec_dot_realBlock (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    cvec z ⬝ᵥ realBlock H *ᵥ cvec w = (z ⬝ᵥ H *ᵥ star w).im := by
  simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec, GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, Matrix.neg_apply,
    Complex.im_sum, Complex.re_sum, Complex.mul_im, Complex.mul_re, Pi.star_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_det_ne_zero {Λ ι : Type} [AddCommGroup Λ] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (inj : Function.Injective form) :
    (Matrix.of fun i j => form (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hform : form (∑ i, c i • b i) = 0 := by
    refine b.ext fun j => ?_
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hj
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    exact hj
  have hsum : ∑ i, c i • b i = 0 := inj (by rw [hform, map_zero])
  exact hc0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hsum))

theorem continuous_of_congruence {ι X : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]
    (T G : X → Matrix ι ι ℝ) (W : Matrix ι ι ℝ) (hT : Continuous T) (hW : W.det ≠ 0)
    (h : ∀ x, (T x)ᵀ * G x * T x = W) : Continuous G := by
  have hdet : ∀ x, (T x).det ≠ 0 := by
    intro x h0
    apply hW
    rw [← h x, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hG : ∀ x, G x = ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    intro x
    have h1 : (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate = (T x).det ^ 2 • G x := by
      calc (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate
          = (T x * (T x).adjugate)ᵀ * G x * (T x * (T x).adjugate) := by
            rw [Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (T x).det ^ 2 • G x := by
            simp only [Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, sq]
    rw [h x] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hdet x)), one_smul]
  have hcont : Continuous fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    have hd : Continuous fun x => (T x).det := hT.matrix_det
    have ha : Continuous fun x => (T x).adjugate := hT.matrix_adjugate
    exact ((hd.pow 2).inv₀ fun x => pow_ne_zero 2 (hdet x)).smul
      ((ha.matrix_transpose.matrix_mul continuous_const).matrix_mul ha)
  rw [show G = fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) from funext hG]
  exact hcont

theorem continuous_Hm (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (hform : ∀ x, (R x).form = form)
    (hP : ∀ v, Continuous fun x => (R x).P v) : Continuous fun x => (R x).Hm := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => isEmptyElim x
  have hlat : ∀ S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ,
      Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g ∧ Function.Bijective S.form := by
    intro S
    obtain ⟨h1, h2, h3, _, _, h4, _, _, _, _, _, _, _, _⟩ := S
    exact ⟨h1, h2, h3, h4⟩
  have hIm : ∀ (S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ) (u v : Λ),
      ((S.P u) ⬝ᵥ S.Hm *ᵥ star (S.P v)).im = S.form u v := by
    intro S u v
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := S
    exact h u v
  obtain ⟨hfree, hfin, hrank, hbij⟩ := hlat (R x₀)
  have hinj : Function.Injective form := by
    rw [← hform x₀]
    exact hbij.1
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin g ⊕ Fin g) ℤ Λ) :=
    ⟨(Module.finBasisOfFinrankEq ℤ Λ (hrank.trans (two_mul g))).reindex finSumFinEquiv.symm⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      W = Matrix.of fun i j => ((form (b i) (b j) : ℤ) : ℝ) := ⟨_, rfl⟩
  have hW : W.det ≠ 0 := by
    have h0 := GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.gram_det_ne_zero b form hinj
    have hmap : W = (Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j => form (b i) (b j)) := by
      ext i j
      rw [hWdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply]
      simp
    rw [hmap, ← RingHom.map_det]
    simpa using h0
  have hT : Continuous fun x =>
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) := by
    refine continuous_matrix fun a i => ?_
    rcases a with k | k
    · exact Complex.continuous_re.comp ((continuous_apply k).comp (hP (b i)))
    · exact Complex.continuous_im.comp ((continuous_apply k).comp (hP (b i)))
  have hTGT : ∀ x,
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)ᵀ *
        GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *
        (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) = W := by
    intro x
    ext i j
    rw [Matrix.mul_assoc]
    calc _ = GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) ⬝ᵥ
            GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *ᵥ GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b j)) := rfl
      _ = (((R x).P (b i)) ⬝ᵥ (R x).Hm *ᵥ star ((R x).P (b j))).im :=
          GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec_dot_realBlock _ _ _
      _ = (R x).form (b i) (b j) := hIm (R x) (b i) (b j)
      _ = W i j := by rw [hform x, hWdef, Matrix.of_apply]
  have hG : Continuous fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm :=
    GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_of_congruence
      (fun x => (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a :
        Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ))
      (fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm) W hT hW hTGT
  refine continuous_matrix fun k l => ?_
  have hre : Continuous fun x => ((R x).Hm k l).re := by
    have h := hG.matrix_elem (Sum.inr k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₂₁, Matrix.map_apply] at h
    exact h
  have him : Continuous fun x => ((R x).Hm k l).im := by
    have h := hG.matrix_elem (Sum.inl k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₁₁, Matrix.map_apply] at h
    exact h
  have heq : (fun x => (R x).Hm k l) =
      fun x => (((R x).Hm k l).re : ℂ) + (((R x).Hm k l).im : ℂ) * Complex.I :=
    funext fun x => (Complex.re_add_im _).symm
  show Continuous fun x => (R x).Hm k l
  rw [heq]
  exact (Complex.continuous_ofReal.comp hre).add ((Complex.continuous_ofReal.comp him).mul continuous_const)

end GlobalTheory.CompanionTheory.Ar.Cusp.HmCont
