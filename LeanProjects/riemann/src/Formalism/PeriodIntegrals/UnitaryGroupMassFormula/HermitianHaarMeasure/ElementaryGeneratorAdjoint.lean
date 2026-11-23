import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FinalG
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

namespace HermitianAdjointLemmas

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have hexp : NormedSpace.exp X = ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • X ^ m := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  let φ : Matrix (Fin n) (Fin n) ℂ →+ (Fin n → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun A B => Matrix.add_mulVec A B v }
  have hφ : Continuous φ := continuous_id.matrix_mulVec continuous_const
  have h1 := hs.hasSum.map φ hφ
  have h2 : HasSum (fun m : ℕ => φ (((m.factorial : ℂ)⁻¹) • X ^ m)) v := by
    have e : (fun m : ℕ => φ (((m.factorial : ℂ)⁻¹) • X ^ m)) = fun m => if m = 0 then v else 0 := by
      funext m
      rcases m with _ | m
      · simp [φ]
      · simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (Nat.succ_ne_zero m)]
        rw [Matrix.smul_mulVec, pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
          smul_zero]
    rw [e]
    exact hasSum_ite_eq 0 v
  rw [hexp]
  exact h1.unique h2

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv WeylGroupFacts.hpk_sq

lemma hpk_ct : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1

lemma hpk_isUnit : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, WeylGroupFacts.hpk_sq, WeylGroupFacts.hpk_sq⟩, rfl⟩

lemma hpk_hpk (X : Mx k r) : Hpk k r * (Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.one_mul]

lemma inU_rsmul {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) (c : ℝ) :
    ((c : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((c : ℂ) • X) = 0 := by
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma exp_mem_uh {Y : Mx k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  have h0 : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hpk_inv, Matrix.mul_neg, ← h0, Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.mul_one]
  have hexp : (NormedSpace.exp Y)ᴴ = Hpk k r * NormedSpace.exp (-Y) * Hpk k r := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hpk_isUnit, hpk_inv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  rw [hexp, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-Y)) (Hpk k r) (Hpk k r), WeylGroupFacts.hpk_sq,
    Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]

lemma glev_mul_exp {i : Fin (r + 1)} {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X)
    (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  have e : ∀ v, X *ᵥ v = 0 → (g * NormedSpace.exp ((t : ℂ) • X)) *ᵥ v = g *ᵥ v := by
    intro v hv
    rw [← Matrix.mulVec_mulVec, exp_mulVec_fix _ v (by rw [Matrix.smul_mulVec, hv, smul_zero])]
  show _ ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val → _
  refine ⟨WeylGroupFacts.uh_mul hg'.1 (exp_mem_uh (inU_rsmul hX.1 t)), fun a ha => ?_⟩
  obtain ⟨h1, h2⟩ := hX.2 a ha
  obtain ⟨g1, g2⟩ := hg'.2 a ha
  exact ⟨by rw [e _ h1, g1], by rw [e _ h2, g2]⟩

lemma rd_ext {i : Fin (r + 1)} {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) {g : Mx k r}
    (hg : g ∈ Glev k r i) : ∃ L : Mx k r →L[ℝ] ℂ, ∀ X, inLieLev k r i X → RdV X f g = L (g * X) := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g ⟨hg, Set.mem_univ _⟩
  refine ⟨fderiv ℝ F g, fun X hX => ?_⟩
  unfold RdV
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (glev_mul_exp hg hX t)
  rw [hev.deriv_eq]
  exact hcomp.deriv

lemma rdV_neg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : RdV (-X) f g = -RdV X f g := by
  unfold RdV
  have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • -X))) =
      fun t : ℝ => (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (-t) := by
    funext t
    simp only [Complex.ofReal_neg, smul_neg, neg_smul]
  rw [e]
  exact (deriv_comp_neg (f := fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (x := 0)).trans
    (by rw [neg_zero])

def Out (i : Fin (r + 1)) (p : Fin (2 * r + k + 1)) : Prop := p.val < i.val ∨ 2 * r + k < p.val + i.val

def SuppV (i : Fin (r + 1)) (W : Mx k r) : Prop := ∀ p q, (Out i p ∨ Out i q) → W p q = 0

lemma out_tau {i : Fin (r + 1)} {p : Fin (2 * r + k + 1)} (h : Out i p) : Out i (WeylGroupFacts.tau k r p) := by
  have := i.isLt
  have := p.isLt
  unfold Out WeylGroupFacts.tau at *
  split_ifs <;> simp only <;> omega

lemma not_out_posL (i : Fin (r + 1)) (c : Fin (mdim k r i)) : ¬ Out i (posL k r i c) := by
  have := i.isLt
  have := c.isLt
  unfold Out posL mdim at *
  simp only
  omega

lemma supp_sub {i : Fin (r + 1)} {A B : Mx k r} (hA : SuppV i A) (hB : SuppV i B) : SuppV i (A - B) := by
  intro p q h; rw [Matrix.sub_apply, hA p q h, hB p q h, sub_zero]

lemma supp_add {i : Fin (r + 1)} {A B : Mx k r} (hA : SuppV i A) (hB : SuppV i B) : SuppV i (A + B) := by
  intro p q h; rw [Matrix.add_apply, hA p q h, hB p q h, add_zero]

lemma supp_smul {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) (c : ℂ) : SuppV i (c • A) := by
  intro p q h; rw [Matrix.smul_apply, hA p q h, smul_zero]

lemma supp_ct {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i Aᴴ := by
  intro p q h; rw [Matrix.conjTranspose_apply, hA q p h.symm, star_zero]

lemma supp_hmul {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (Hpk k r * A) := by
  intro p q h
  rw [WeylGroupFacts.hpk_mul_apply]
  rcases h with hp | hq
  · rw [hA _ _ (Or.inl (out_tau hp)), mul_zero]
  · rw [hA _ _ (Or.inr hq), mul_zero]

lemma supp_mulh {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (A * Hpk k r) := by
  have e : A * Hpk k r = (Hpk k r * Aᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct]
  rw [e]
  exact supp_ct (supp_hmul (supp_ct hA))

lemma supp_conj {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (Hpk k r * Aᴴ * Hpk k r) :=
  supp_mulh (supp_hmul (supp_ct hA))

lemma supp_single (i : Fin (r + 1)) (c d : Fin (mdim k r i)) :
    SuppV i (Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) := by
  intro p q h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  rcases h with h | h <;> exact not_out_posL i _ h

lemma supp_hpart1 {i : Fin (r + 1)} {W : Mx k r} (hW : SuppV i W) : SuppV i (hpart1 (Hpk k r) W) := by
  unfold hpart1
  rw [hpk_inv]
  exact supp_smul (supp_sub hW (supp_conj hW)) _

lemma supp_hpart2 {i : Fin (r + 1)} {W : Mx k r} (hW : SuppV i W) : SuppV i (hpart2 (Hpk k r) W) := by
  unfold hpart2
  rw [hpk_inv]
  exact supp_smul (supp_add hW (supp_conj hW)) _

lemma inU_hpart1 (W : Mx k r) :
    (hpart1 (Hpk k r) W)ᴴ * Hpk k r + Hpk k r * hpart1 (Hpk k r) W = 0 := by
  unfold hpart1
  rw [hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, ← smul_add]
  convert smul_zero (1 / 2 : ℂ) using 2
  abel

lemma inU_hpart2 (W : Mx k r) :
    (hpart2 (Hpk k r) W)ᴴ * Hpk k r + Hpk k r * hpart2 (Hpk k r) W = 0 := by
  unfold hpart2
  rw [hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    simp [mul_neg, div_neg, map_ofNat]
  rw [hs, neg_smul, neg_add_eq_zero]
  congr 1
  abel

lemma lie_of {i : Fin (r + 1)} {X : Mx k r} (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hS : SuppV i X) :
    inLieLev k r i X := by
  refine ⟨hU, fun a ha => ⟨?_, ?_⟩⟩
  · funext p
    simp only [bvec, Matrix.mulVec_single_one, Pi.zero_apply]
    refine hS _ _ (Or.inr ?_)
    have := a.isLt
    unfold Out eI
    simp only
    omega
  · funext p
    simp only [bvec, Matrix.mulVec_single_one, Pi.zero_apply]
    refine hS _ _ (Or.inr ?_)
    have := a.isLt
    unfold Out esI
    simp only
    omega

lemma hpart1_add (A B : Mx k r) :
    hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
  unfold hpart1
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

lemma hpart2_add (A B : Mx k r) :
    hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
  unfold hpart2
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

lemma two_I_inv : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero) two_ne_zero]
  linear_combination (2 : ℂ) * Complex.I_sq

lemma star_re_im (c : ℂ) : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

lemma hpart1_smul (c : ℂ) (W : Mx k r) :
    hpart1 (Hpk k r) (c • W) = c.re • hpart1 (Hpk k r) W - c.im • hpart2 (Hpk k r) W := by
  unfold hpart1 hpart2
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
    ← Complex.coe_smul, two_I_inv, star_re_im]
  set M := (Hpk k r)⁻¹ * Wᴴ * Hpk k r
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  match_scalars <;> ring_nf

lemma hpart2_smul (c : ℂ) (W : Mx k r) :
    hpart2 (Hpk k r) (c • W) = c.re • hpart2 (Hpk k r) W + c.im • hpart1 (Hpk k r) W := by
  unfold hpart1 hpart2
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
    ← Complex.coe_smul, two_I_inv, star_re_im]
  set M := (Hpk k r)⁻¹ * Wᴴ * Hpk k r
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  match_scalars <;> (ring_nf; (try simp only [Complex.I_sq]); (try ring))

def phiL (L : Mx k r →L[ℝ] ℂ) (g : Mx k r) : Mx k r →ₗ[ℂ] ℂ where
  toFun W := L (g * hpart1 (Hpk k r) W) + Complex.I * L (g * hpart2 (Hpk k r) W)
  map_add' A B := by
    simp only [hpart1_add, hpart2_add, Matrix.mul_add, map_add]
    ring
  map_smul' c W := by
    simp only [RingHom.id_apply, smul_eq_mul, hpart1_smul, hpart2_smul, Matrix.mul_sub,
      Matrix.mul_add, Matrix.mul_smul, map_sub, map_add, map_smul, Complex.real_smul]
    set L1 := L (g * hpart1 (Hpk k r) W)
    set L2 := L (g * hpart2 (Hpk k r) W)
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_rhs => rw [hc]
    linear_combination (-((c.im : ℂ) * L2)) * Complex.I_sq

lemma hpart1_conj (Z : Mx k r) :
    hpart1 (Hpk k r) (Hpk k r * Zᴴ * Hpk k r) = -hpart1 (Hpk k r) Z := by
  unfold hpart1
  rw [hpk_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hpk_ct]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  rw [← smul_neg, neg_sub]

lemma hpart2_conj (Z : Mx k r) :
    hpart2 (Hpk k r) (Hpk k r * Zᴴ * Hpk k r) = hpart2 (Hpk k r) Z := by
  unfold hpart2
  rw [hpk_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hpk_ct]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  congr 1
  abel

lemma hpk_conj_single_apply (a' b' p q : Fin (2 * r + k + 1)) :
    (Hpk k r * (Matrix.single a' b' (1 : ℂ))ᴴ * Hpk k r) p q = Hpk k r p b' * Hpk k r a' q := by
  rw [Matrix.conjTranspose_single, star_one]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

lemma hpk_out_left {i : Fin (r + 1)} {p m : Fin (2 * r + k + 1)} (hp : Out i p) (hm : ¬ Out i m) :
    Hpk k r p m = 0 := by
  rw [WeylGroupFacts.hpk_row, if_neg]
  intro h
  exact hm (h ▸ out_tau hp)

lemma hpk_out_right {i : Fin (r + 1)} {q m : Fin (2 * r + k + 1)} (hq : Out i q) (hm : ¬ Out i m) :
    Hpk k r m q = 0 := by
  rw [WeylGroupFacts.hpk_row, if_neg]
  intro h
  apply hm
  have := out_tau (k := k) hq
  rw [h, WeylGroupFacts.tau_tau] at this
  exact this

lemma posL_inj {i : Fin (r + 1)} {c c' : Fin (mdim k r i)} (h : posL k r i c = posL k r i c') : c = c' := by
  have := congrArg Fin.val h
  simp only [posL] at this
  exact Fin.ext (by omega)

lemma posL_surj {i : Fin (r + 1)} {p : Fin (2 * r + k + 1)} (hp : ¬ Out i p) :
    ∃ c : Fin (mdim k r i), posL k r i c = p := by
  have := i.isLt
  unfold Out at hp
  refine ⟨⟨p.val - i.val, by unfold mdim; omega⟩, Fin.ext ?_⟩
  simp only [posL]
  omega

lemma conj_single_expand (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r =
      ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ) := by
  ext p q
  rw [hpk_conj_single_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hp : Out i p
  · rw [hpk_out_left hp (not_out_posL i b), zero_mul]
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨rfl, -⟩
    exact not_out_posL i c hp
  by_cases hq : Out i q
  · rw [hpk_out_right hq (not_out_posL i a), mul_zero]
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨-, rfl⟩
    exact not_out_posL i d hq
  obtain ⟨c₀, rfl⟩ := posL_surj hp
  obtain ⟨d₀, rfl⟩ := posL_surj hq
  rw [Finset.sum_eq_single c₀, Finset.sum_eq_single d₀, if_pos ⟨rfl, rfl⟩]
  · rfl
  · intro d _ hd
    rw [if_neg]
    rintro ⟨-, h⟩
    exact hd (posL_inj h)
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨h, -⟩
    exact hc (posL_inj h)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma ec_phi {i : Fin (r + 1)} {L : Mx k r →L[ℝ] ℂ} {f : Mx k r → ℂ} {g : Mx k r}
    (hL : ∀ X, inLieLev k r i X → RdV X f g = L (g * X)) {W : Mx k r} (hW : SuppV i W) :
    RdV (hpart1 (Hpk k r) W) f g + Complex.I • RdV (hpart2 (Hpk k r) W) f g = phiL L g W := by
  rw [hL _ (lie_of (inU_hpart1 W) (supp_hpart1 hW)), hL _ (lie_of (inU_hpart2 W) (supp_hpart2 hW)),
    smul_eq_mul]
  rfl

lemma ec_expand {i : Fin (r + 1)} {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) {g : Mx k r}
    (hg : g ∈ Glev k r i) (a b : Fin (mdim k r i)) :
    RdV (hpart1 (Hpk k r) (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) f g +
      Complex.I • RdV (hpart2 (Hpk k r)
        (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) f g =
    ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g := by
  obtain ⟨L, hL⟩ := rd_ext hf hg
  rw [ec_phi hL (supp_conj (supp_single i a b)), conj_single_expand, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, ← ec_phi hL (supp_single i c d)]
  rfl

end HermitianAdjointLemmas

open HermitianAdjointLemmas in
theorem elementary_generator_adjoint : EabAdjFrom := by
  intro hRd _hP hT hI k r i μ hμ a b f₁ f₂ h₁ h₂
  set Z : Mx k r := Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) with hZ
  have hX1 : inLieLev k r i (hpart1 (Hpk k r) Z) :=
    lie_of (inU_hpart1 Z) (supp_hpart1 (supp_single i a b))
  have hX2 : inLieLev k r i (hpart2 (Hpk k r) Z) :=
    lie_of (inU_hpart2 Z) (supp_hpart2 (supp_single i a b))
  set Ψ : (Mx k r → ℂ) → Mx k r → ℂ := fun f g =>
    ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g with hΨ
  have hE : ∀ f g, EH k r (posL k r i a) (posL k r i b) f g =
      RdV (hpart1 (Hpk k r) Z) f g + Complex.I * RdV (hpart2 (Hpk k r) Z) f g := fun f g => rfl
  have hPsi : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      Ψ f g = -RdV (hpart1 (Hpk k r) Z) f g + Complex.I * RdV (hpart2 (Hpk k r) Z) f g := by
    intro f hf g hg
    rw [hΨ]
    dsimp only
    rw [← ec_expand hf hg a b, hpart1_conj, hpart2_conj, rdV_neg, smul_eq_mul]
  have hR1 : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      RdV (hpart1 (Hpk k r) Z) f g = (EH k r (posL k r i a) (posL k r i b) f g - Ψ f g) / 2 := by
    intro f hf g hg
    rw [hE, hPsi f hf g hg]
    ring
  have hR2 : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      RdV (hpart2 (Hpk k r) Z) f g =
        (EH k r (posL k r i a) (posL k r i b) f g + Ψ f g) / (2 * Complex.I) := by
    intro f hf g hg
    rw [hE, hPsi f hf g hg]
    field_simp
    ring
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ Glev k r i := by
    rw [ae_iff]
    exact hμ.conc

  have iA : Integrable (fun x : Mt k r =>
      EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ :=
    hI k r i μ hμ _ _ (hT k r i a b f₁ h₁) h₂
  have iB : Integrable (fun x : Mt k r => Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ := by
    have e : (fun x : Mt k r => Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) = fun x =>
        ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) *
          (EH k r (posL k r i c) (posL k r i d) f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) := by
      funext x
      simp only [hΨ, Finset.sum_mul, smul_eq_mul, mul_assoc]
    rw [e]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ =>
      (hI k r i μ hμ _ _ (hT k r i c d f₁ h₁) h₂).const_mul _
  have iC : Integrable (fun x : Mt k r =>
      f₁ (Matrix.of x) * star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x))) μ :=
    hI k r i μ hμ _ _ h₁ (hT k r i a b f₂ h₂)
  have iD : Integrable (fun x : Mt k r => f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x))) μ := by
    have e : (fun x : Mt k r => f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x))) = fun x =>
        ∑ c, ∑ d, star (Hm k r i c b * Hm k r i a d) *
          (f₁ (Matrix.of x) * star (EH k r (posL k r i c) (posL k r i d) f₂ (Matrix.of x))) := by
      funext x
      simp only [hΨ, star_sum, Finset.mul_sum, smul_eq_mul, star_mul']
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [e]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ =>
      (hI k r i μ hμ _ _ h₁ (hT k r i c d f₂ h₂)).const_mul _

  have s1 := hRd k r i μ hμ _ f₁ f₂ hX1 h₁.1 h₂.1 h₁.2 h₂.2
  have s2 := hRd k r i μ hμ _ f₁ f₂ hX2 h₁.1 h₂.1 h₁.2 h₂.2
  have l1 : (∫ x : Mt k r, RdV (hpart1 (Hpk k r) Z) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      (1 / 2 : ℂ) * ((∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) *
        star (f₂ (Matrix.of x)) ∂μ) - ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_sub iA iB, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR1 f₁ h₁.1 _ hx]
    ring
  have r1 : (∫ x : Mt k r, f₁ (Matrix.of x) * star (RdV (hpart1 (Hpk k r) Z) f₂ (Matrix.of x)) ∂μ) =
      (1 / 2 : ℂ) * ((∫ x : Mt k r, f₁ (Matrix.of x) *
        star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ) -
          ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_sub iC iD, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR1 f₂ h₂.1 _ hx, star_div₀, star_sub, star_ofNat]
    ring
  have l2 : (∫ x : Mt k r, RdV (hpart2 (Hpk k r) Z) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      (1 / (2 * Complex.I)) * ((∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) *
        star (f₂ (Matrix.of x)) ∂μ) + ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_add iA iB, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR2 f₁ h₁.1 _ hx]
    ring
  have r2 : (∫ x : Mt k r, f₁ (Matrix.of x) * star (RdV (hpart2 (Hpk k r) Z) f₂ (Matrix.of x)) ∂μ) =
      -(1 / (2 * Complex.I)) * ((∫ x : Mt k r, f₁ (Matrix.of x) *
        star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ) +
          ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_add iC iD, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR2 f₂ h₂.1 _ hx, star_div₀, star_add, star_mul', star_ofNat, Complex.star_def, Complex.conj_I]
    field_simp
  rw [l1, r1] at s1
  rw [l2, r2] at s2
  show (∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
    ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ
  set A := ∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ
  set B := ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ
  set C := ∫ x : Mt k r, f₁ (Matrix.of x) * star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ
  set D := ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ
  have hk : (1 / (2 * Complex.I) : ℂ) ≠ 0 := by simp
  have e2 : A + B = C + D := mul_left_cancel₀ hk (by rw [s2]; ring)
  linear_combination s1 + (1 / 2 : ℂ) * e2

end PI.QnHermHaar
