import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open Matrix Topology Filter
open scoped ComplexOrder

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.REAL

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {W : Submodule ℂ (Fin n → ℂ)}

def Sc (J : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (l m : ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ w ∈ W, g *ᵥ w = l • w) ∧ (∀ z ∈ perp J W, g *ᵥ z - z ∈ W) ∧ ∀ z, g *ᵥ z - m • z ∈ perp J W

theorem lowers_iff {g : Matrix (Fin n) (Fin n) ℂ} : Lowers J W (g - 1) ↔ Sc J W 1 1 g := by
  simp only [Lowers, Sc, sub_mulVec, one_mulVec, one_smul, sub_eq_zero]

theorem Sc.mul (hW : Isot J W) {l m l' m' : ℂ} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : Sc J W l m g)
    (hh : Sc J W l' m' h) : Sc J W (l * l') (m * m') (g * h) := by
  have gW : ∀ w ∈ W, g *ᵥ w ∈ W := fun w hw => by rw [hg.1 w hw]; exact W.smul_mem _ hw
  have gP : ∀ z ∈ perp J W, g *ᵥ z ∈ perp J W := fun z hz => by
    simpa using (perp J W).add_mem (hW (hg.2.1 z hz)) hz
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · rw [← mulVec_mulVec, hh.1 w hw, mulVec_smul, hg.1 w hw, smul_smul, mul_comm]
  · have := W.add_mem (gW _ (hh.2.1 z hz)) (hg.2.1 z hz)
    rwa [mulVec_sub, sub_add_sub_cancel, mulVec_mulVec] at this
  · have := (perp J W).add_mem (gP _ (hh.2.2 z)) ((perp J W).smul_mem m' (hg.2.2 z))
    rwa [mulVec_sub, mulVec_smul, smul_sub, sub_add_sub_cancel, mulVec_mulVec, smul_smul, mul_comm m'] at this

theorem Sc.inv (hW : Isot J W) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : Sc J W 1 1 g) (e : h * g = 1) :
    Sc J W 1 1 h := by
  have e' : ∀ z, h *ᵥ (g *ᵥ z) = z := fun z => by rw [mulVec_mulVec, e, one_mulVec]
  have h1 : ∀ w ∈ W, h *ᵥ w = w := fun w hw => by
    have := e' w
    rwa [hg.1 w hw, one_smul] at this
  have h0 : ∀ z, h *ᵥ z - z = -(h *ᵥ (g *ᵥ z - z)) := fun z => by rw [mulVec_sub, e', neg_sub]
  have h2 : ∀ z ∈ perp J W, h *ᵥ z - z ∈ W := fun z hz => by
    rw [h0, h1 _ (hg.2.1 z hz)]; exact W.neg_mem (hg.2.1 z hz)
  refine ⟨fun w hw => by rw [h1 w hw, one_smul], h2, fun z => ?_⟩
  have h3 := hg.2.2 z
  rw [one_smul] at h3 ⊢
  rw [h0]
  simpa using (perp J W).neg_mem ((perp J W).add_mem (hW (h2 _ h3)) h3)

theorem uMat_mul {ε : Fin n → Bool} (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_inv_mulF {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel]; rfl

theorem uMat_mul_invF {ε : Fin n → Bool} (g : UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel]; rfl

theorem continuous_uMat {ε : Fin n → Bool} : Continuous (uMat : UJ ε → _) := (isClosedEmbeddingMatrix n ε).1.continuous

theorem unipotent_radical_subgroup : NWSub := by
  intro n ε W hW
  constructor
  · have hc : ∀ z, Continuous fun g : UJ ε => (uMat g - 1) *ᵥ z := fun z =>
      (continuous_uMat.sub continuous_const).matrix_mulVec continuous_const
    have : NWset ε W = (⋂ w ∈ W, {g | (uMat g - 1) *ᵥ w = 0}) ∩
        ((⋂ z ∈ perp (Jm ε) W, (fun g : UJ ε => (uMat g - 1) *ᵥ z) ⁻¹' (W : Set _)) ∩
          ⋂ z, (fun g : UJ ε => (uMat g - 1) *ᵥ z) ⁻¹' (perp (Jm ε) W : Set _)) := by
      ext g; simp [NWset, Lowers]
    rw [this]
    exact (isClosed_biInter fun w _ => isClosed_eq (hc w) continuous_const).inter
      ((isClosed_biInter fun z _ => W.closed_of_finiteDimensional.preimage (hc z)).inter
        (isClosed_iInter fun z => (perp (Jm ε) W).closed_of_finiteDimensional.preimage (hc z)))
  · exact ⟨{ carrier := NWset ε W
             mul_mem' := fun {a b} ha hb => lowers_iff.2 (by
               simpa [uMat_mul] using (lowers_iff.1 ha).mul hW (lowers_iff.1 hb))
             one_mem' := by
               show Lowers _ _ ((1 : Matrix (Fin n) (Fin n) ℂ) - 1)
               rw [sub_self]
               exact ⟨fun _ _ => zero_mulVec _, fun _ _ => by rw [zero_mulVec]; exact W.zero_mem,
                 fun _ => by rw [zero_mulVec]; exact Submodule.zero_mem _⟩
             inv_mem' := fun {a} ha => lowers_iff.2 ((lowers_iff.1 ha).inv hW (uMat_inv_mulF a)) }, rfl⟩

def IsPr (W : Submodule ℂ (Fin n → ℂ)) (p : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  pᴴ = p ∧ (∀ z, p *ᵥ z ∈ W) ∧ ∀ w ∈ W, p *ᵥ w = w

theorem exists_isPr (W : Submodule ℂ (Fin n → ℂ)) : ∃ p, IsPr W p := by
  let e := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := W.comap (e : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ))
  let P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := K.starProjection
  have hP : ∀ z, Matrix.toEuclideanLin.symm P *ᵥ z = (P (WithLp.toLp 2 z)).ofLp := fun z => by
    conv_rhs => rw [← Matrix.toEuclideanLin.apply_symm_apply P]
    rfl
  refine ⟨Matrix.toEuclideanLin.symm P, ?_, fun z => ?_, fun w hw => ?_⟩
  · refine Matrix.isHermitian_iff_isSymmetric.2 ?_
    rw [LinearEquiv.apply_symm_apply]
    exact K.starProjection_isSymmetric
  · rw [hP]; exact K.starProjection_apply_mem _
  · rw [hP]
    exact congrArg WithLp.ofLp (Submodule.starProjection_eq_self_iff.2 (show WithLp.toLp 2 w ∈ K from hw))

theorem mat_extF {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext h)

theorem IsPr.sq {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) : p * p = p :=
  mat_extF fun z => by rw [← mulVec_mulVec, hp.2.2 _ (hp.2.1 z)]

theorem IsPr.dot {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) (y z : Fin n → ℂ) :
    star y ⬝ᵥ (p *ᵥ z) = star (p *ᵥ y) ⬝ᵥ z := by
  rw [star_mulVec, hp.1, dotProduct_mulVec]

theorem IsPr.kill {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) {z : Fin n → ℂ} (hz : z ∈ perp J W) :
    p *ᵥ (J *ᵥ z) = 0 := by
  refine dotProduct_star_self_eq_zero.1 ?_
  rw [hp.dot]
  exact hz _ (hp.2.1 _)

theorem IsPr.entry {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) (i j : Fin n) : ‖p i j‖ ≤ 1 := by
  have h : ∀ j, ((∑ k, ‖p k j‖ ^ 2 : ℝ) : ℂ) = p j j := fun j => by
    conv_rhs => rw [← hp.sq, ← hp.1]
    rw [hp.1]
    conv_rhs => rw [show p * p = pᴴ * p by rw [hp.1]]
    simp only [mul_apply, conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def,
      Complex.conj_mul']
  have h1 : ∀ k, ‖p k j‖ ^ 2 ≤ ‖p j j‖ := fun k => by
    rw [← h j, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.single_le_sum (f := fun k => ‖p k j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 : ‖p j j‖ ≤ 1 := by nlinarith [h1 j, norm_nonneg (p j j)]
  nlinarith [h1 i, norm_nonneg (p i j)]

def am (J p : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + ((Real.exp t - 1 : ℝ) : ℂ) • p + ((Real.exp (-t) - 1 : ℝ) : ℂ) • (J * p * J)

theorem expand {p q : Matrix (Fin n) (Fin n) ℂ} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0)
    (a b c d : ℂ) : (1 + a • p + b • q) * (1 + c • p + d • q) =
      1 + (a + c + a * c) • p + (b + d + b * d) • q := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hp, hq,
    hpq, hqp, smul_zero, add_smul]
  module

section Am

variable {ε : Fin n → Bool} {p : Matrix (Fin n) (Fin n) ℂ}

theorem Jm_sq (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; split_ifs <;> simp

theorem Jm_hermF (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a; by_cases h : ε a <;> simp [h]

theorem pJp (hW : Isot (Jm ε) W) (hp : IsPr W p) : p * Jm ε * p = 0 :=
  mat_extF fun z => by rw [← mulVec_mulVec, ← mulVec_mulVec, hp.kill (hW (hp.2.1 z)), zero_mulVec]

theorem q_facts (hW : Isot (Jm ε) W) (hp : IsPr W p) :
    (Jm ε * p * Jm ε) * (Jm ε * p * Jm ε) = Jm ε * p * Jm ε ∧ p * (Jm ε * p * Jm ε) = 0 ∧
      (Jm ε * p * Jm ε) * p = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · calc _ = Jm ε * p * (Jm ε * Jm ε) * p * Jm ε := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Jm_sq, Matrix.mul_one, Matrix.mul_assoc (Jm ε), hp.sq]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, pJp hW hp, Matrix.zero_mul]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc p, pJp hW hp, Matrix.mul_zero]

theorem am_add (hW : Isot (Jm ε) W) (hp : IsPr W p) (s t : ℝ) : am (Jm ε) p (s + t) = am (Jm ε) p s * am (Jm ε) p t := by
  obtain ⟨h1, h2, h3⟩ := q_facts hW hp
  rw [am, am, am, expand hp.sq h1 h2 h3, neg_add, Real.exp_add, Real.exp_add]
  congr 2
  · congr 1; push_cast; ring
  · push_cast; ring

theorem am_mem (hW : Isot (Jm ε) W) (hp : IsPr W p) (t : ℝ) : inUJ ε (am (Jm ε) p t) := by
  have hH : (am (Jm ε) p t)ᴴ = am (Jm ε) p t := by
    simp only [am, conjTranspose_add, conjTranspose_one, conjTranspose_smul, conjTranspose_mul, hp.1, Jm_hermF,
      Complex.star_def, Complex.conj_ofReal, Matrix.mul_assoc]
  have hJ : am (Jm ε) p t * Jm ε = Jm ε * am (Jm ε) p (-t) := by
    simp only [am, neg_neg, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Jm_sq]
    rw [← Matrix.mul_assoc (Jm ε) (Jm ε), Jm_sq, Matrix.one_mul]
    abel
  rw [inUJ, hH, hJ, Matrix.mul_assoc, ← am_add hW hp, neg_add_cancel]
  simp [am]

theorem am_sc (hW : Isot (Jm ε) W) (hp : IsPr W p) (t : ℝ) :
    Sc (Jm ε) W (Real.exp t) (Real.exp (-t)) (am (Jm ε) p t) := by
  have hv : ∀ z, am (Jm ε) p t *ᵥ z = z + ((Real.exp t - 1 : ℝ) : ℂ) • p *ᵥ z +
      ((Real.exp (-t) - 1 : ℝ) : ℂ) • Jm ε *ᵥ (p *ᵥ (Jm ε *ᵥ z)) := fun z => by
    simp only [am, add_mulVec, one_mulVec, smul_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · rw [hv, hp.kill (hW hw), hp.2.2 w hw, mulVec_zero]
    push_cast
    module
  · rw [hv, hp.kill hz, mulVec_zero, smul_zero, add_zero, add_sub_cancel_left]
    exact W.smul_mem _ (hp.2.1 z)
  · have h1 : Jm ε *ᵥ (p *ᵥ (Jm ε *ᵥ z)) - z ∈ perp (Jm ε) W := fun w hw => by
      rw [hf, mulVec_sub, mulVec_mulVec, Jm_sq, one_mulVec, dotProduct_sub, hp.dot, hp.2.2 w hw, sub_self]
    have := (perp (Jm ε) W).add_mem ((perp (Jm ε) W).smul_mem ((Real.exp t - 1 : ℝ) : ℂ) (hW (hp.2.1 z)))
      ((perp (Jm ε) W).smul_mem ((Real.exp (-t) - 1 : ℝ) : ℂ) h1)
    convert this using 1
    rw [hv]
    push_cast
    module

theorem hf_uMatF (x : UJ ε) (y z : Fin n → ℂ) : hf (Jm ε) (uMat x *ᵥ y) (uMat x *ᵥ z) = hf (Jm ε) y z := by
  have hx : (uMat x)ᴴ * Jm ε * uMat x = Jm ε := x.2
  rw [hf, hf, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hx]

end Am

theorem norm_mulVec_le (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖M *ᵥ v‖ ≤ (1 + ∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖M i j‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ ≤ ∑ j, ‖M i j‖ * ‖v‖ :=
        (norm_sum_le Finset.univ fun j => M i j * v j).trans (Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _))
    _ ≤ _ := by
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right (le_add_of_nonneg_of_le zero_le_one ?_) (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem real_parabolic_decomposition : RealPar := by
  intro n ε W hW0 hW N hN
  have hmem : ∀ g, g ∈ N ↔ Sc (Jm ε) W 1 1 (uMat g) := fun g => by
    rw [← lowers_iff, ← SetLike.mem_coe, hN]; rfl
  obtain ⟨w₀, hw₀, hw0⟩ := (Submodule.ne_bot_iff W).1 hW0
  obtain ⟨p, hp⟩ := exists_isPr W
  let a : ℝ → UJ ε := fun t => indefiniteUnitaryMk ε _ (am_mem hW hp t)
  have hadd : ∀ s t, a (s + t) = a s * a t := fun s t => indefinite_unitary_ext (am_add hW hp s t)
  have ha0 : a 0 = 1 := indefinite_unitary_ext (by show am _ _ 0 = 1; simp [am])
  have hinv : ∀ t, (a t)⁻¹ = a (-t) := fun t => inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, ha0])
  have hee : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) * (Real.exp (-t) : ℝ) = 1 := fun t => by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hne : ∀ g : UJ ε, uMat g⁻¹ *ᵥ w₀ ≠ 0 := fun g h => hw0 (by
    rw [← one_mulVec w₀, ← uMat_mul_invF g, ← mulVec_mulVec, h, mulVec_zero])
  have hamc : Continuous fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => am (Jm ε) q.2 q.1 := by
    unfold am
    have c1 : Continuous fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => ((Real.exp q.1 - 1 : ℝ) : ℂ) := by fun_prop
    have c2 : Continuous fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => ((Real.exp (-q.1) - 1 : ℝ) : ℂ) := by fun_prop
    exact (continuous_const.add (c1.smul continuous_snd)).add
      (c2.smul ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const))
  let S : UJ ε → ℝ := fun g => 1 + ∑ i, ∑ j, ‖uMat g i j‖
  have hS1 : ∀ g, 1 ≤ S g := fun g => le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hSc : Continuous fun g => Real.log (S g) :=
    (continuous_const.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_uMat.matrix_elem i j).norm)).log fun g => (one_pos.trans_le (hS1 g)).ne'
  refine ⟨a, fun g => -Real.log ‖uMat g⁻¹ *ᵥ w₀‖, ?_, hadd, fun t m hm => ?_, ?_, fun m hm g => ?_, fun t g => ?_,
    ⟨fun y => Real.log (S y) + Real.log (S y⁻¹), hSc.add (hSc.comp continuous_inv), fun x y => ?_⟩, fun U hU => ?_⟩
  · exact (isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff.2 (hamc.comp (continuous_id.prodMk continuous_const))
  · rw [hmem, hinv]
    have := ((am_sc hW hp t).mul hW ((hmem m).1 hm)).mul hW (am_sc hW hp (-t))
    rwa [mul_one, mul_one, neg_neg, hee, mul_comm, hee] at this
  · exact (((continuous_uMat.comp continuous_inv).matrix_mulVec continuous_const).norm.log
      fun g => norm_ne_zero_iff.2 (hne g)).neg
  · rw [_root_.mul_inv_rev, uMat_mul, ← mulVec_mulVec, ((hmem _).1 (N.inv_mem hm)).1 w₀ hw₀, one_smul]
  · rw [_root_.mul_inv_rev, uMat_mul, ← mulVec_mulVec, hinv]
    have : uMat (a (-t)) *ᵥ w₀ = ((Real.exp (-t) : ℝ) : ℂ) • w₀ := (am_sc hW hp (-t)).1 w₀ hw₀
    rw [this, mulVec_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.2 (hne g)), Real.log_exp]
    ring
  · have p1 := norm_pos_iff.2 (hne x)
    have p2 := norm_pos_iff.2 (hne (x * y))
    have e1 : uMat (x * y)⁻¹ *ᵥ w₀ = uMat y⁻¹ *ᵥ (uMat x⁻¹ *ᵥ w₀) := by
      rw [_root_.mul_inv_rev, uMat_mul, mulVec_mulVec]
    have e2 : uMat x⁻¹ *ᵥ w₀ = uMat y *ᵥ (uMat (x * y)⁻¹ *ᵥ w₀) := by
      rw [e1, mulVec_mulVec _ (uMat y), uMat_mul_invF, one_mulVec]
    have b1 : Real.log ‖uMat (x * y)⁻¹ *ᵥ w₀‖ ≤ Real.log (S y⁻¹) + Real.log ‖uMat x⁻¹ *ᵥ w₀‖ := by
      rw [← Real.log_mul (one_pos.trans_le (hS1 _)).ne' p1.ne']
      exact Real.log_le_log p2 (by rw [e1]; exact norm_mulVec_le _ _)
    have b2 : Real.log ‖uMat x⁻¹ *ᵥ w₀‖ ≤ Real.log (S y) + Real.log ‖uMat (x * y)⁻¹ *ᵥ w₀‖ := by
      rw [← Real.log_mul (one_pos.trans_le (hS1 _)).ne' p2.ne']
      exact Real.log_le_log p1 (by nth_rewrite 1 [e2]; exact norm_mulVec_le _ _)
    have c1 := Real.log_nonneg (hS1 y)
    have c2 := Real.log_nonneg (hS1 y⁻¹)
    rw [abs_le]
    constructor <;> linarith
  · rw [(isClosedEmbeddingMatrix n ε).1.isInducing.nhds_eq_comap, mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
      (P := fun t q => am (Jm ε) (Matrix.of q) t ∈ V) fun q _ =>
        hamc.continuousAt (x := (0, Matrix.of q)) (by
          show V ∈ 𝓝 (am (Jm ε) (Matrix.of q) 0)
          simpa [am] using hV)
    obtain ⟨τ, hτ, hb⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨τ, hτ, fun t ht x => ?_⟩
    let W' : Submodule ℂ (Fin n → ℂ) := W.comap (Matrix.toLin' (uMat x))
    have hxx : ∀ z, uMat x *ᵥ (uMat x⁻¹ *ᵥ z) = z := fun z => by rw [mulVec_mulVec, uMat_mul_invF, one_mulVec]
    have hP' : ∀ z, z ∈ perp (Jm ε) W' ↔ uMat x *ᵥ z ∈ perp (Jm ε) W := fun z =>
      ⟨fun h w hw => by
        rw [← hxx w, hf_uMatF]
        exact h _ (show uMat x *ᵥ _ ∈ W by rwa [hxx]),
       fun h w hw => by rw [← hf_uMatF x]; exact h _ hw⟩
    have hW' : Isot (Jm ε) W' := fun z hz => (hP' z).2 (hW hz)
    obtain ⟨p', hp'⟩ := exists_isPr W'
    let a' : UJ ε := indefiniteUnitaryMk ε _ (am_mem hW' hp' t)
    have hs' : Sc (Jm ε) W' (Real.exp t) (Real.exp (-t)) (uMat a') := am_sc hW' hp' t
    have hs : Sc (Jm ε) W (Real.exp t) (Real.exp (-t)) (uMat (x * a' * x⁻¹)) := by
      have hv : ∀ z, uMat (x * a' * x⁻¹) *ᵥ z = uMat x *ᵥ (uMat a' *ᵥ (uMat x⁻¹ *ᵥ z)) := fun z => by
        rw [uMat_mul, uMat_mul, mulVec_mulVec, mulVec_mulVec]
      refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
      · rw [hv, hs'.1 _ (show uMat x *ᵥ _ ∈ W by rwa [hxx]), mulVec_smul, hxx]
      · have : uMat x *ᵥ _ ∈ W := hs'.2.1 (uMat x⁻¹ *ᵥ z) ((hP' _).2 (by rwa [hxx]))
        rwa [mulVec_sub, hxx, ← hv] at this
      · have := (hP' _).1 (hs'.2.2 (uMat x⁻¹ *ᵥ z))
        rwa [mulVec_sub, mulVec_smul, hxx, ← hv] at this
    refine ⟨x * a' * x⁻¹ * a (-t), (hmem _).2 ?_, ?_⟩
    · have := hs.mul hW (am_sc hW hp (-t))
      rwa [neg_neg, hee, mul_comm, hee] at this
    · rw [← hinv, inv_mul_cancel_right, show x⁻¹ * (x * a' * x⁻¹) * x = a' by group]
      exact hVU (hb (by simpa using ht) (fun i j => p' i j) fun i _ j _ => by simpa using hp'.entry i j)

end CompanionTheory.D.gk.RF
