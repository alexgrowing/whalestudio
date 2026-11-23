import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorusExists

open Matrix

section Gen

variable {R : Type} [CommRing R] {d : ℕ}

def sesq (c : R →+* R) (j : Matrix (Fin d) (Fin d) R) (u w : Fin d → R) : R := u ⬝ᵥ j *ᵥ fun i => c (w i)

def torusMat (c : R →+* R) (j : Matrix (Fin d) (Fin d) R) (x y : Fin d → R) (t s : R) : Matrix (Fin d) (Fin d) R :=
  1 + (t - 1) • vecMulVec x (j *ᵥ fun i => c (y i)) + (1 - s) • vecMulVec y (j *ᵥ fun i => c (x i))

variable {c : R →+* R} {j : Matrix (Fin d) (Fin d) R}

theorem vecMulVec_mulVec_eq (x a v : Fin d → R) : vecMulVec x a *ᵥ v = (v ⬝ᵥ a) • x := by
  ext i
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

theorem torusMat_mulVec (x y : Fin d → R) (t s : R) (v : Fin d → R) :
    torusMat c j x y t s *ᵥ v = v + ((t - 1) * sesq c j v y) • x + ((1 - s) * sesq c j v x) • y := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec_eq, sesq, smul_smul]

theorem sesq_add_left (u u' w : Fin d → R) : sesq c j (u + u') w = sesq c j u w + sesq c j u' w := by
  simp [sesq, add_dotProduct]

theorem sesq_smul_left (r : R) (u w : Fin d → R) : sesq c j (r • u) w = r * sesq c j u w := by
  simp [sesq, smul_dotProduct]

theorem sesq_add_right (u w w' : Fin d → R) : sesq c j u (w + w') = sesq c j u w + sesq c j u w' := by
  have : (fun i => c ((w + w') i)) = (fun i => c (w i)) + fun i => c (w' i) := by ext; simp
  simp only [sesq, this, mulVec_add, dotProduct_add]

theorem sesq_smul_right (r : R) (u w : Fin d → R) : sesq c j u (r • w) = c r * sesq c j u w := by
  have : (fun i => c ((r • w) i)) = c r • fun i => c (w i) := by ext; simp
  simp only [sesq, this, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem sesq_skew (hcc : ∀ z, c (c z) = z) (hj : ∀ i k, c (j k i) = -j i k) (u w : Fin d → R) :
    sesq c j u w = -c (sesq c j w u) := by
  simp only [sesq, dotProduct, mulVec, map_sum, map_mul, hcc, hj]
  simp only [Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem sesq_torusMat (hcc : ∀ z, c (c z) = z) (hj : ∀ i k, c (j k i) = -j i k) {x y : Fin d → R}
    (hxx : sesq c j x x = 0) (hyy : sesq c j y y = 0) (hxy : sesq c j x y = 1) {t s : R} (h1 : t * c s = 1)
    (h2 : c t * s = 1) (v w : Fin d → R) :
    sesq c j (torusMat c j x y t s *ᵥ v) (torusMat c j x y t s *ᵥ w) = sesq c j v w := by
  have hyx : sesq c j y x = -1 := by rw [sesq_skew hcc hj, hxy, map_one]
  have hxw : sesq c j x w = -c (sesq c j w x) := sesq_skew hcc hj _ _
  have hyw : sesq c j y w = -c (sesq c j w y) := sesq_skew hcc hj _ _
  rw [torusMat_mulVec, torusMat_mulVec]
  simp only [sesq_add_left, sesq_add_right, sesq_smul_left, sesq_smul_right, hxx, hyy, hxy, hyx, hxw, hyw, map_mul,
    map_sub, map_one, hcc]
  linear_combination (-(sesq c j v y * c (sesq c j w x))) * h1 + (sesq c j v x * c (sesq c j w y)) * h2

theorem sesq_mulVec (A : Matrix (Fin d) (Fin d) R) (v w : Fin d → R) :
    sesq c j (A *ᵥ v) (A *ᵥ w) = v ⬝ᵥ (Aᵀ * j * A.map c) *ᵥ fun i => c (w i) := by
  have : (fun i => c ((A *ᵥ w) i)) = A.map c *ᵥ fun i => c (w i) := by
    ext i; exact RingHom.map_mulVec c A w i
  rw [sesq, this, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ v), dotProduct_mulVec,
    dotProduct_comm]

theorem torusMat_unitary (hcc : ∀ z, c (c z) = z) (hj : ∀ i k, c (j k i) = -j i k) {x y : Fin d → R}
    (hxx : sesq c j x x = 0) (hyy : sesq c j y y = 0) (hxy : sesq c j x y = 1) {t s : R} (h1 : t * c s = 1)
    (h2 : c t * s = 1) : (torusMat c j x y t s)ᵀ * j * (torusMat c j x y t s).map c = j := by
  ext i k
  have h := sesq_torusMat hcc hj hxx hyy hxy h1 h2 (Pi.single i 1) (Pi.single k 1)
  have hs : ∀ (M : Matrix (Fin d) (Fin d) R), (Pi.single i (1 : R)) ⬝ᵥ M *ᵥ (fun l => c ((Pi.single k (1 : R) : Fin d → R) l)) = M i k := by
    intro M
    have : (fun l => c ((Pi.single k (1 : R) : Fin d → R) l)) = Pi.single k 1 := by
      ext l; by_cases hl : l = k
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [this]; simp [mulVec_single_one]
  rw [sesq_mulVec, hs, sesq] at h
  rw [h, hs j]

theorem torusMat_mul (hcc : ∀ z, c (c z) = z) (hj : ∀ i k, c (j k i) = -j i k) {x y : Fin d → R}
    (hxx : sesq c j x x = 0) (hyy : sesq c j y y = 0) (hxy : sesq c j x y = 1) {t s t' s' : R} (ht : t * t' = 1)
    (hs : s * s' = 1) : torusMat c j x y t s * torusMat c j x y t' s' = 1 := by
  have hyx : sesq c j y x = -1 := by rw [sesq_skew hcc hj, hxy, map_one]
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← mulVec_mulVec, one_mulVec]
  generalize (Pi.single k 1 : Fin d → R) = v
  rw [torusMat_mulVec (c := c) (j := j) x y t' s' v, torusMat_mulVec]
  simp only [sesq_add_left, sesq_smul_left, hxx, hyy, hxy, hyx]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (sesq c j v y * x i) * ht - (sesq c j v x * y i) * hs

end Gen

section Spec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigma_sigma h]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem sesq_incV {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (u w : Fin d → E) :
    sesq (cA σ).toRingHom (incM F J) (incV F u) (incV F w) = inclR (AF F) (form σ J u w) := by
  simp [sesq, form, dotProduct, mulVec, incV, incM, map_sum, map_mul, cA_inclR]

end Spec

theorem levi_torus_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ t
  classical
  have hcm : IsCMExt F E σ := hP.base.cm
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hc
  have hcc : ∀ z, c (c z) = z := fun z => cA_cA hcm z
  have hj : ∀ i k, c (incM F W.J k i) = -incM F W.J i k := by
    intro i k
    simp [c, incM, cA_inclR, hP.skew.skew i k]
  have hxx : sesq c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [sesq_incV, hH.xx, map_zero]
  have hyy : sesq c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [sesq_incV, hH.yy, map_zero]
  have hxy : sesq c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [sesq_incV, hH.xy, map_one]
  have hyx : sesq c (incM F W.J) (incV F H'.y) (incV F H'.x) = -1 := by rw [sesq_skew hcc hj, hxy, map_one]
  have h1 : t.1 * c (cA σ (t⁻¹).1) = 1 := by simp [c, cA_cA hcm]
  have h2 : c t.1 * cA σ (t⁻¹).1 = 1 := by simp [c, ← map_mul]
  have h3 : cA σ (t⁻¹).1 * c t.1 = 1 := by rw [mul_comm, h2]
  let m := torusMat c (incM F W.J) (incV F H'.x) (incV F H'.y) t.1 (cA σ (t⁻¹).1)
  let m' := torusMat c (incM F W.J) (incV F H'.x) (incV F H'.y) (t⁻¹).1 (c t.1)
  have hmm' : m * m' = 1 := torusMat_mul hcc hj hxx hyy hxy (by simp) h3
  have hm'm : m' * m = 1 := torusMat_mul hcc hj hxx hyy hxy (by simp) (by rw [mul_comm, h3])
  let g : GL (Fin d) (AE F E) := ⟨m, m', hmm', hm'm⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) := torusMat_unitary hcc hj hxx hyy hxy h1 h2
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
  · show m *ᵥ incV F H'.x = t.1 • incV F H'.x
    rw [torusMat_mulVec, hxy, hxx]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · show m *ᵥ incV F H'.y = cA σ (t⁻¹).1 • incV F H'.y
    rw [torusMat_mulVec, hyy, hyx]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · show m * incM F H'.ι = incM F H'.ι * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))
    refine (?_ : m * incM F H'.ι = incM F H'.ι).trans (Matrix.mul_one _).symm
    refine Matrix.ext_of_mulVec_single fun k => ?_
    rw [← mulVec_mulVec]
    have hcol : incM F H'.ι *ᵥ Pi.single k 1 = incV F (H'.ι *ᵥ Pi.single k 1) := by
      ext i; simp [mulVec_single_one, incV, incM]
    rw [hcol, torusMat_mulVec, sesq_incV, sesq_incV, (hH.orth _).1, (hH.orth _).2]
    simp

end GlobalTheory.LeviTorusExists
