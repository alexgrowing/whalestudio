import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Swap

open GlobalTheory.Amp.Rad GlobalTheory.Amp.UEmb

variable {k r : ℕ}

theorem mI_eq (j : Fin (k + 1)) : mI k r j = wI k r j := rfl

def rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) : Fin r → Fin (k + 1) → ℂ :=
  fun a j => ∑ c, star (u a c) * B c j

theorem herm_rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) :
    (Matrix.of fun a b => herm (Hb k) (rowAct u B b) (rowAct u B a)) =
      u * (Matrix.of fun a b => herm (Hb k) (B b) (B a)) * uᴴ := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, herm_Hb, rowAct, star_sum, star_mul', star_star,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

theorem uEmb_mul_pEl (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (B : Fin r → Fin (k + 1) → ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ) :
    uEmb k r u * pEl k r B S = pEl k r (rowAct u B) (u * S * uᴴ) * uEmb k r u := by
  have h1 : ∀ a b, ∑ c, u⁻¹ a c * u c b = if a = b then 1 else 0 := fun a b => by
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul u hu, Matrix.one_apply]
  have h2 : uᴴ * (u⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul u hu, Matrix.conjTranspose_one]
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply, sum3, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp only [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, ← mI_eq,
      u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss] <;> simp only [mI_eq] <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss]
  · simp [rowAct, Finset.sum_mul, mul_assoc]
  · rename_i a b
    set G : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => herm (Hb k) (B b) (B a) with hG
    have h3 : ∀ a c, herm (Hb k) (rowAct u B c) (rowAct u B a) = (u * G * uᴴ) a c := fun a c =>
      congrFun (congrFun (herm_rowAct u B) a) c
    have h4 : u * (S - (1 / 2 : ℂ) • G) = (u * S * uᴴ - (1 / 2 : ℂ) • (u * G * uᴴ)) * (u⁻¹)ᴴ := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc _ uᴴ, Matrix.mul_assoc _ uᴴ, h2, Matrix.mul_one,
        Matrix.mul_one, Matrix.mul_sub, Matrix.mul_smul]
    have h5 := congrFun (congrFun h4 a) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at h5
    simp only [h3]
    convert h5 using 2 with c _ c _
    · simp [hG, div_eq_inv_mul]
    · simp [div_eq_inv_mul]
  · rename_i i b
    simp only [rowAct, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ d, ∑ c, star (u c d) * B d i * (starRingEnd ℂ) (u⁻¹ b c) = star (∑ c, u⁻¹ b c * u c d) * B d i := by
      intro d
      rw [star_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by simp; ring
    simp only [this, h1]
    simp [apply_ite (starRingEnd ℂ)]

theorem det_eq_one {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι) (L : Module.End ℝ V) (T : Module.End ℝ W)
    (h : ∀ v, ι (L v) = T (ι v)) (hT : IsNilpotent (T - 1)) : LinearMap.det L = 1 := by
  have hL : IsNilpotent (L - 1) := by
    obtain ⟨n, hn⟩ := hT
    have : ∀ (m : ℕ) (v : V), ι (((L - 1) ^ m) v) = ((T - 1) ^ m) (ι v) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => intro v; simp [pow_succ, ih, h]
    refine ⟨n, LinearMap.ext fun v => hι ?_⟩
    rw [this, hn]; simp
  have hc := hL.neg.charpoly_eq_X_pow_finrank
  have he := LinearMap.eval_charpoly (-(L - 1)) 1
  rw [hc] at he
  simpa using he.symm

theorem nil_mul {R : Type*} [Ring R] {a b : R} (h : Commute a b) (ha : IsNilpotent (a - 1)) (hb : IsNilpotent (b - 1)) :
    IsNilpotent (a * b - 1) := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by noncomm_ring
  have c1 : Commute (a - 1) b := h.sub_left (Commute.one_left b)
  rw [e]
  refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right ha) hb
  exact Commute.mul_left (c1.sub_right (Commute.one_right _)) ((Commute.refl b).sub_right (Commute.one_right _))

theorem nil_upper (x : UT r → ℂ) : IsNilpotent (upper x - 1) := by
  have hc : (upper x - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular]
    · simp [upper]
    · intro a b h
      have h : b < a := h
      simp [upper, h.not_gt, h.ne']
  have := Matrix.aeval_self_charpoly (upper x - 1)
  rw [hc] at this
  exact ⟨r, by simpa using this⟩

def rowLin (k : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Fin r → Fin (k + 1) → ℂ) where
  toFun := rowAct u
  map_add' B B' := by ext a j; simp [rowAct, mul_add, Finset.sum_add_distrib]
  map_smul' c B := by
    ext a j; simp only [rowAct, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

def skewLin (r : ℕ) : ((UT r → ℂ) × (Fin r → ℝ)) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun p := skewM p.1 p.2
  map_add' p q := by
    ext a b; simp only [skewM, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' c p := by
    ext a b; simp only [skewM, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp <;> ring

def coordLin (r : ℕ) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] ((UT r → ℂ) × (Fin r → ℝ)) where
  toFun S := (fun q => S q.1.1 q.1.2, fun a => (S a a).im)
  map_add' S T := by ext <;> simp
  map_smul' c S := by ext <;> simp

theorem coord_skew (p : (UT r → ℂ) × (Fin r → ℝ)) : coordLin r (skewLin r p) = p := by
  ext q
  · simp [coordLin, skewLin, skewM, q.2]
  · simp [coordLin, skewLin, skewM]

theorem skew_coord (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) : skewLin r (coordLin r S) = S := by
  obtain ⟨p, hp, -⟩ := skewM_unique S hS
  have : S = skewLin r p := hp
  rw [this, coord_skew]

def conjLin (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Matrix (Fin r) (Fin r) ℂ) :=
  LinearMap.mulLeft ℝ u * LinearMap.mulRight ℝ uᴴ

def skewAct (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ ((UT r → ℂ) × (Fin r → ℝ)) :=
  coordLin r ∘ₗ conjLin u ∘ₗ skewLin r

theorem skew_skewAct (u : Matrix (Fin r) (Fin r) ℂ) (p : (UT r → ℂ) × (Fin r → ℝ)) :
    skewLin r (skewAct u p) = u * skewLin r p * uᴴ := by
  have h : (skewLin r p)ᴴ = -skewLin r p := skewM_skew p.1 p.2
  have e : skewAct u p = coordLin r (u * skewLin r p * uᴴ) := by
    simp [skewAct, conjLin, Matrix.mul_assoc]
  rw [e, skew_coord]
  simp [Matrix.conjTranspose_mul, h, Matrix.mul_assoc]

theorem mp_of_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] E) (h : LinearMap.det L = 1) :
    MeasurePreserving L μ μ :=
  ⟨L.continuous_of_finiteDimensional.measurable, by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [h]; exact one_ne_zero), h]; simp⟩

def parAct (u : Matrix (Fin r) (Fin r) ℂ) (q : PPar k r) : PPar k r := (rowLin k u q.1, skewAct u q.2)

theorem uEmb_mul_pOf (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (q : PPar k r) :
    uEmb k r u * pOf k r q = pOf k r (parAct u q) * uEmb k r u := by
  have h := skew_skewAct u q.2
  unfold pOf
  rw [uEmb_mul_pEl u hu]
  congr 2
  exact h.symm

theorem cont_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold upper
  split_ifs <;> fun_prop

theorem cont_uEmb (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x) := by
  have hi : Continuous fun x : UT r → ℂ => (upper x)⁻¹ := by
    have : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate := by
      funext x; rw [Matrix.inv_def, det_upper]; simp
    rw [this]; exact (cont_upper r).matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold uEmb
  split_ifs
  · exact (cont_upper r).matrix_elem _ _
  · exact (hi.matrix_elem _ _).star
  all_goals exact continuous_const

theorem cont_pOf (k r : ℕ) : Continuous (pOf k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold pOf pEl skewM herm Matrix.mulVec dotProduct
  simp only [Pi.star_apply]
  split_ifs <;> fun_prop

theorem cont_parAct (k r : ℕ) : Continuous fun q : (UT r → ℂ) × PPar k r => parAct (upper q.1) q.2 := by
  have hu : Continuous fun q : (UT r → ℂ) × PPar k r => upper q.1 := (cont_upper r).comp continuous_fst
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun a => continuous_pi fun j => ?_
    change Continuous fun q : (UT r → ℂ) × PPar k r => ∑ c, star (upper q.1 a c) * q.2.1 c j
    exact continuous_finset_sum _ fun c _ => (hu.matrix_elem a c).star.mul (by fun_prop)
  · have hs : Continuous fun q : (UT r → ℂ) × PPar k r => skewLin r q.2.2 :=
      (skewLin r).continuous_of_finiteDimensional.comp (by fun_prop)
    exact (coordLin r).continuous_of_finiteDimensional.comp (hu.matrix_mul (hs.matrix_mul hu.matrix_conjTranspose))

end GlobalTheory.Amp.Swap
