import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines

noncomputable section

open scoped TensorProduct Matrix Classical Real
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex MvPolynomial

namespace PositivityTheory.RL.Up

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def atL (w : ι) : Module.End ℂ V →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, V) :=
  (PiTensorProduct.mapMultilinear ℂ (fun _ : ι => V) fun _ => V).toLinearMap (fun _ => LinearMap.id) w

omit [Fintype ι] in
theorem atL_eq (w : ι) (L : Module.End ℂ V) : atPl (V := fun _ : ι => V) w L = atL w L := rfl

omit [Fintype ι] in
theorem atL_tprod (w : ι) (L : Module.End ℂ V) (x : ι → V) :
    atL w L (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (Function.update x w (L (x w))) := by
  rw [← atL_eq, atPl, PiTensorProduct.map_tprod]
  congr 1
  funext v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

omit [Fintype ι] in
theorem atL_mul (w : ι) (L L' : Module.End ℂ V) : atL w (L * L') = atL w L * atL w L' := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp [atL_tprod]

omit [Fintype ι] in
theorem atL_one (w : ι) : atL w (1 : Module.End ℂ V) = 1 := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp [atL_tprod]

theorem map_sumPl (e : V →ₗ[ℂ] W) (L : ι → Module.End ℂ V) (L' : ι → Module.End ℂ W) (h : ∀ w x, e (L w x) = L' w (e x))
    (T : ⨂[ℂ] _ : ι, V) : PiTensorProduct.map (fun _ => e) (sumPl (V := fun _ => V) L T) =
      sumPl (V := fun _ => W) L' (PiTensorProduct.map (fun _ => e) T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, sumPl, LinearMap.sum_apply, map_sum, atL_eq, atL_tprod, PiTensorProduct.map_tprod]
    congr 1
    refine Finset.sum_congr rfl fun w _ => congrArg _ (funext fun v => ?_)
    by_cases hv : v = w
    · subst hv; simp [h]
    · simp [hv]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tensor

variable {P Q R S : ℕ}

theorem pd_X {σ : Type} [DecidableEq σ] (a b : σ) :
    ((pderiv a).toLinearMap * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * (pderiv a).toLinearMap + if a = b then 1 else 0 := by
  refine LinearMap.ext fun p => ?_
  by_cases h : a = b
  · subst h
    simp [add_comm]
  · simp [h, pderiv_X_of_ne (Ne.symm h)]

theorem pd_pd {σ : Type} [DecidableEq σ] (a b : σ) :
    ((pderiv a).toLinearMap * (pderiv b).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) =
      (pderiv b).toLinearMap * (pderiv a).toLinearMap := by
  refine LinearMap.ext fun P => ?_
  change pderiv a (pderiv b P) = pderiv b (pderiv a P)
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem low_rai (l l' : Ln P Q R S) : lowB l' * raiB l = raiB l * lowB l' + if l = l' then 1 else 0 := by
  unfold lowB raiB
  by_cases h : l = l'
  · subst h
    cases linePos l <;> simp [pd_X]
  · have h' : l' ≠ l := Ne.symm h
    cases linePos l <;> cases linePos l' <;> simp [pd_X, h, h', pd_pd l l']
    exact LinearMap.ext fun p => mul_left_comm _ _ _

theorem anti_omE (l l' : Ln P Q R S) : raiB l * lowB l' + lowB l' * raiB l = (2 : ℂ) • omE l l' := by
  rw [low_rai, omE]
  split_ifs <;> module

def eps : Ix R S → ℝ := Sum.elim (fun _ => 1) fun _ => -1

theorem lineSign_eq (a : Ix P Q) (b : Ix R S) :
    lineSign (p := P) (q := Q) (r := R) (s := S) a b = ((eps a * eps b : ℝ) : ℂ) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, eps]

theorem eps_sq (a : Ix R S) : eps a * eps a = 1 := by rcases a with a | a <;> simp [eps]

theorem upq_entry {Y : Mat R S} (hY : Y ∈ upq R S) (b b' : Ix R S) :
    ((eps b * eps b' : ℝ) : ℂ) * star (Y b' b) = -Y b b' := by
  have := congrFun (congrFun (show Yᴴ * Jm R S + Jm R S * Y = 0 from hY) b) b'
  rw [PositivityTheory.RL.Jm_eq, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at this
  rcases b with b | b <;> rcases b' with b' | b' <;> simp [eps] at this ⊢ <;>
    first | linear_combination this | linear_combination -this

theorem im_twisted_inner_sum (c c' : Matrix (Ix P Q) (Ix R S) ℂ) : (∑ l, Fock.tw1 c l * star (Fock.tw1 c' l)).im =
    ∑ l : Ln P Q R S, eps l.1 * eps l.2 * (c l.1 l.2 * star (c' l.1 l.2)).im := by
  rw [im_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases l with ⟨a | a, b | b⟩ <;> simp [Fock.tw1, linePos, eps] <;> ring

def cu (Y : Mat R S) (j : Ln P Q R S × Bool) : Matrix (Ix P Q) (Ix R S) ℂ :=
  (if j.2 then 1 else I) • (Matrix.single j.1.1 j.1.2 (1 : ℂ) * Yᵀ)

def cv (j : Ln P Q R S × Bool) : Matrix (Ix P Q) (Ix R S) ℂ :=
  (((eps j.1.1 * eps j.1.2 / 2 : ℝ) : ℂ) * if j.2 then I else -1) • Matrix.single j.1.1 j.1.2 1

theorem expand (Y : Mat R S) (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    c * Yᵀ = ∑ j, (2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 c l)).im) • cu Y j := by
  have h : ∀ j : Ln P Q R S × Bool, 2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 c l)).im =
      if j.2 then (c j.1.1 j.1.2).re else (c j.1.1 j.1.2).im := fun j => by
    obtain ⟨⟨a, b⟩, t⟩ := j
    rw [im_twisted_inner_sum, Finset.sum_eq_single (a, b) (fun l _ hl => by
      have : ¬(a = l.1 ∧ b = l.2) := fun h => hl (Prod.ext h.1.symm h.2.symm)
      simp [cv, this]) (by simp)]
    rcases a with a | a <;> rcases b with b | b <;> cases t <;> simp [cv, eps] <;> ring
  simp only [h]
  conv_lhs => rw [Matrix.matrix_eq_sum_single c]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (c a b) = c a b • Matrix.single a b 1 by simp, Matrix.smul_mul]
  simp only [Fintype.sum_bool, cu, if_true, Bool.false_eq_true, if_false, one_smul]
  generalize Matrix.single a b (1 : ℂ) * Yᵀ = N
  ext i k
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, real_smul]
  linear_combination (-N i k) * re_add_im (c a b)

theorem heis_smul (z : ℂ) (c : Matrix (Ix P Q) (Ix R S) ℂ) : heisOp (z • c) = ((Real.sqrt (2 * π) : ℝ) : ℂ) •
    (z • (∑ l : Ln P Q R S, c l.1 l.2 • raiB l) - star z • ∑ l : Ln P Q R S,
      (((eps l.1 * eps l.2 : ℝ) : ℂ) * star (c l.1 l.2)) • lowB l) := by
  rw [heisOp, Finset.smul_sum (r := z), Finset.smul_sum (r := star z), ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [lineSign_eq, Matrix.smul_apply, smul_eq_mul, star_mul', smul_smul]
  congr 2
  ring

theorem fock_eq {Y : Mat R S} (hY : Y ∈ upq R S) :
    (8 * π * I : ℂ)⁻¹ • ∑ j : Ln P Q R S × Bool, (heisOp (cu Y j) * heisOp (cv j) + heisOp (cv j) * heisOp (cu Y j)) =
      fockAct2 P Q R S Y := by
  set k : ℂ := ((Real.sqrt (2 * π) : ℝ) : ℂ) with hk
  have hk2 : k * k = 2 * π := by
    rw [hk, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have one : ∀ (a : Ix P Q) (b : Ix R S), (8 * π * I : ℂ)⁻¹ • ∑ t : Bool,
      (heisOp (cu Y ((a, b), t)) * heisOp (cv ((a, b), t)) + heisOp (cv ((a, b), t)) * heisOp (cu Y ((a, b), t))) =
      (1 / 2 : ℂ) • (∑ b', Y b' b • omE (a, b') (a, b) + ∑ b', Y b b' • omE (a, b) (a, b')) := fun a b => by
    have r1 : (∑ l : Ln P Q R S, (Matrix.single a b (1 : ℂ) * Yᵀ) l.1 l.2 • raiB l) = ∑ b', Y b' b • raiB (a, b') := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun a' _ h => by simp [Matrix.mul_apply, h.symm]) (by simp)]
      simp
    have r2 : (∑ l : Ln P Q R S, (((eps l.1 * eps l.2 : ℝ) : ℂ) * star ((Matrix.single a b (1 : ℂ) * Yᵀ) l.1 l.2)) • lowB l) =
        -(((eps a * eps b : ℝ) : ℂ) • ∑ b', Y b b' • lowB (a, b')) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun a' _ h => by simp [Matrix.mul_apply, h.symm]) (by simp),
        Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [smul_smul, ← neg_smul, Matrix.single_mul_apply_same, one_mul, Matrix.transpose_apply]
      congr 1
      have h1 := upq_entry hY b b'
      have h2 : ((eps b : ℝ) : ℂ) * (eps b : ℝ) = 1 := by rw [← ofReal_mul, eps_sq, ofReal_one]
      push_cast at h1 ⊢
      linear_combination ((eps a : ℂ) * eps b) * h1 - ((eps a : ℂ) * eps b' * star (Y b' b)) * h2
    have r3 : (∑ l : Ln P Q R S, (Matrix.single a b (1 : ℂ)) l.1 l.2 • raiB l) = raiB (a, b) := by
      rw [Finset.sum_eq_single (a, b) (fun l _ hl => by
        have : ¬(a = l.1 ∧ b = l.2) := fun h => hl (Prod.ext h.1.symm h.2.symm)
        simp [this]) (by simp)]
      simp
    have r4 : (∑ l : Ln P Q R S, (((eps l.1 * eps l.2 : ℝ) : ℂ) * star ((Matrix.single a b (1 : ℂ)) l.1 l.2)) • lowB l) =
        ((eps a * eps b : ℝ) : ℂ) • lowB (a, b) := by
      rw [Finset.sum_eq_single (a, b) (fun l _ hl => by
        have : ¬(a = l.1 ∧ b = l.2) := fun h => hl (Prod.ext h.1.symm h.2.symm)
        simp [this]) (by simp)]
      simp
    have a1 : (2 : ℂ) • ∑ b', Y b' b • omE (a, b') (a, b) =
        (∑ b', Y b' b • raiB (a, b')) * lowB (a, b) + lowB (a, b) * ∑ b', Y b' b • raiB (a, b') := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, ← smul_add, anti_omE, smul_comm]
    have a2 : (2 : ℂ) • ∑ b', Y b b' • omE (a, b) (a, b') =
        raiB (a, b) * (∑ b', Y b b' • lowB (a, b')) + (∑ b', Y b b' • lowB (a, b')) * raiB (a, b) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, ← smul_add, anti_omE, smul_comm]
    have hs : ((eps a * eps b : ℝ) : ℂ) * ((eps a * eps b : ℝ) : ℂ) = 1 := by
      rw [← ofReal_mul, mul_mul_mul_comm, eps_sq, eps_sq, mul_one, ofReal_one]
    rw [show (1 / 2 : ℂ) = (1 / 4) * 2 by norm_num, mul_smul, smul_add (2 : ℂ), a1, a2, inv_smul_eq_iff₀ (by simp [hπ])]
    simp only [Fintype.sum_bool, cu, cv, heis_smul, r1, r2, r3, r4, if_true, Bool.false_eq_true, if_false, ← hk]
    simp only [ofReal_div, ofReal_ofNat, star_mul', star_div₀, star_ofNat, star_one, star_neg, star_def, conj_I, conj_ofReal, map_neg, map_one]
    generalize ((eps a * eps b : ℝ) : ℂ) = s at hs
    generalize (∑ b', Y b' b • raiB (a, b') : Module.End ℂ (Pol P Q R S)) = Rp
    generalize (∑ b', Y b b' • lowB (a, b') : Module.End ℂ (Pol P Q R S)) = Lp
    simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_neg, neg_mul]
    match_scalars <;> first | ring1 | linear_combination (I * s ^ 2) * hk2 + (2 * π * I) * hs
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.smul_sum]
  simp only [Finset.smul_sum (r := (8 * π * I : ℂ)⁻¹) (s := (Finset.univ : Finset (Ix R S))), one]
  simp only [fockAct2, LinearMap.comp_apply, omAct_apply, Matrix.kroneckerMapBilinear_apply_apply,
    Matrix.kroneckerMap_apply, LinearMap.mul_apply', Fintype.sum_prod_type, Matrix.one_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_comm (f := fun b b' => Y b' b • omE (a, b') (a, b)),
    ← two_smul ℂ, smul_smul]
  simp [ite_smul]

def sw (P Q R S : ℕ) : Pol R S P Q ≃ₐ[ℂ] Pol P Q R S := renameEquiv ℂ (Equiv.prodComm _ _)

theorem linePos_swap (a : Ix P Q) (b : Ix R S) :
    linePos (p := R) (q := S) (r := P) (s := Q) (b, a) = linePos (p := P) (q := Q) (r := R) (s := S) (a, b) := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem sw_pd (a : Ix P Q) (b : Ix R S) (p : Pol R S P Q) : sw P Q R S (pderiv (b, a) p) = pderiv (a, b) (sw P Q R S p) :=
  (pderiv_rename (Equiv.prodComm _ _).injective (b, a) p).symm

theorem sw_low (a : Ix P Q) (b : Ix R S) (p : Pol R S P Q) : sw P Q R S (lowB (b, a) p) = lowB (a, b) (sw P Q R S p) := by
  unfold lowB
  rw [linePos_swap]
  split_ifs
  · exact sw_pd a b p
  · simp [sw]

theorem sw_rai (a : Ix P Q) (b : Ix R S) (p : Pol R S P Q) : sw P Q R S (raiB (b, a) p) = raiB (a, b) (sw P Q R S p) := by
  unfold raiB
  rw [linePos_swap]
  split_ifs
  · simp [sw]
  · simp only [LinearMap.neg_apply, map_neg]
    exact congrArg _ (sw_pd a b p)

theorem sw_heis (c : Matrix (Ix R S) (Ix P Q) ℂ) (p : Pol R S P Q) :
    sw P Q R S (heisOp c p) = heisOp cᵀ (sw P Q R S p) := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, map_smul, map_sum, map_sub,
    Fintype.sum_prod_type, sw_low, sw_rai, lineSign_eq, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
  rw [mul_comm (eps a)]

theorem sw_fock (Y : Mat P Q) (p : Pol R S P Q) :
    sw P Q R S (fockAct2 R S P Q Y p) = fockAct1 P Q R S Y (sw P Q R S p) := by
  have h : ∀ (a a' : Ix P Q) (b b' : Ix R S), sw P Q R S (omE (b, a) (b', a') p) = omE (a, b) (a', b') (sw P Q R S p) :=
    fun a a' b b' => by
      simp only [omE, LinearMap.add_apply, Module.End.mul_apply, map_add, sw_rai, sw_low, Prod.mk.injEq, and_comm]
      split_ifs <;> simp
  simp only [fockAct1, fockAct2, LinearMap.comp_apply, LinearMap.flip_apply, omAct_apply,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, LinearMap.mul_apply', Fintype.sum_prod_type,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

end PositivityTheory.RL.Up

namespace PositivityTheory.RL

open Up

theorem lieFirst : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := by
  intro h2 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om χ m hcm hψ hfr hΦ hd hW hm γ hγ Y hY T
  let Ψ : Tens F R S P Q ≃ₗ[ℂ] Tens F P Q R S := PiTensorProduct.congr fun _ => (sw P Q R S).toLinearEquiv
  have hΨ : ∀ T, Ψ T = PiTensorProduct.map (fun _ => (sw P Q R S).toLinearMap) T := fun _ => rfl
  have h1 : IsFockMap ψ τ d' C A (Φ ∘ₗ Ψ.toLinearMap) := by
    refine ⟨hΦ.1.comp Ψ.injective, fun u hu c hc T => ?_⟩
    have := hΦ.2 uᵀ (fun s hs => by rw [← Matrix.transpose_smul, hu s hs, Matrix.transpose_zero]) (fun w => (c w)ᵀ)
      (fun w => by rw [Matrix.transpose_map, hc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]) (Ψ T)
    have e : ∀ t, d.rho ψ (realAd F t • uᵀ) = d'.rho ψ (realAd F t • u) := fun t => by
      rw [Darboux.rho, Darboux.rho, ← hd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [e] at this
    rw [hΨ, ← map_sumPl _ (fun w => heisOp (c w)) _ fun w x => sw_heis (c w) x] at this
    exact this
  have := h2 F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om χ m hcm hψ ⟨(mul_comm _ _).trans hfr.1, hfr.2.2, hfr.2.1⟩ h1 hW hm
    γ hγ Y hY (Ψ.symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
  rw [hΨ, map_sumPl _ _ (fun w => fockAct1 P Q R S (Y w) + ((m w : ℂ) / 2 * (Y w).trace) • 1) fun w x => by
    simp only [LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, Module.End.one_apply]
    exact congrArg (· + _) (sw_fock (Y w) x), ← hΨ, LinearEquiv.apply_symm_apply] at this
  exact this

end PositivityTheory.RL

end
