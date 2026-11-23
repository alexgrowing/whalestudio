import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmQuadraticPhaseEquivariantEmbeddingsStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ProdThetaConj

theorem ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  simp only [ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_sum {κ : Type*} [Fintype κ] (a : κ → ℝ) : ee (∑ j, a j) = ∏ j, ee (a j) := by
  simp only [ee, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

theorem thetaTranslation_comp_eq_cocycle_mul (Λ : AddSubgroup ℂ) (x y : ℂ) (g : ℂ → ℂ) :
    U1 Λ x (U1 Λ y g) = fun z => ee (gl3FieldFirst Λ y (x / 2)) * U1 Λ (x + y) g z := by
  funext z
  simp only [U1, ee, gl3FieldFirst]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]
  congr 2
  have h := Complex.sub_conj (y * (starRingEnd ℂ) (x / 2))
  simp only [map_mul, Complex.conj_conj, map_div₀, map_ofNat, map_add] at h ⊢
  push_cast at h ⊢
  simp only [div_eq_mul_inv, mul_inv] at h ⊢
  linear_combination (Real.pi : ℂ) * (area Λ : ℂ)⁻¹ * h

theorem differentiable_U1 (Λ : AddSubgroup ℂ) (x : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (U1 Λ x g) := by
  unfold U1
  fun_prop

theorem thetaTranslation_const_mul (Λ : AddSubgroup ℂ) (x a : ℂ) (g : ℂ → ℂ) :
    U1 Λ x (fun z => a * g z) = fun z => a * U1 Λ x g z := by
  funext z
  simp only [U1, mul_assoc]

theorem taylorCoeffAtZero_const_mul (a : ℂ) (g : ℂ → ℂ) (n : ℕ) :
    coef1 (fun z => a * g z) n = a * coef1 g n := by
  rw [coef1, coef1, iteratedDeriv_const_mul_field, mul_div_assoc]

def OddLaw (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) : Prop :=
  deriv g 0 = 1 ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω g z = (if ω / 2 ∈ Λ then 1 else -1) * g z

theorem riemannFormImag_real_smul_left (Λ : AddSubgroup ℂ) (r : ℝ) (x y : ℂ) :
    gl3FieldFirst Λ (r * x) y = r * gl3FieldFirst Λ x y := by
  simp only [gl3FieldFirst, mul_assoc, Complex.im_ofReal_mul, mul_div_assoc]

theorem riemannFormImag_swap (Λ : AddSubgroup ℂ) (x y : ℂ) : gl3FieldFirst Λ y x = -gl3FieldFirst Λ x y := by
  simp only [gl3FieldFirst, Complex.mul_im, Complex.conj_im, Complex.conj_re]
  ring

theorem riemannFormImag_real_smul_right (Λ : AddSubgroup ℂ) (r : ℝ) (x y : ℂ) :
    gl3FieldFirst Λ x (r * y) = r * gl3FieldFirst Λ x y := by
  rw [riemannFormImag_swap, riemannFormImag_real_smul_left, riemannFormImag_swap Λ x y]
  ring

theorem OddLaw.ee_eq_one {Λ : AddSubgroup ℂ} {g : ℂ → ℂ} (h : OddLaw Λ g) {a b : ℂ}
    (ha : a ∈ Λ) (hb : b ∈ Λ) : ee (gl3FieldFirst Λ a b) = 1 := by
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra! h0
    have h1 := h.1
    rw [show g = fun _ => 0 from funext h0] at h1
    simp at h1
  have h2 : (2 * b) ∈ Λ := by rw [two_mul]; exact Λ.add_mem hb hb
  have e1 := congrFun (thetaTranslation_comp_eq_cocycle_mul Λ (2 * b) a g) z
  have hne : (if a / 2 ∈ Λ then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> simp
  rw [funext (h.2 a ha), thetaTranslation_const_mul, h.2 _ (Λ.add_mem h2 ha)] at e1
  simp only at e1
  rw [h.2 _ h2, show 2 * b / 2 = b by ring, if_pos hb, show (2 * b + a) / 2 = b + a / 2 by ring] at e1
  simp only [Λ.add_mem_cancel_left hb, one_mul] at e1
  exact (mul_right_cancel₀ (mul_ne_zero hne hz) (by rw [one_mul]; exact e1)).symm

theorem OddLaw.doubleTranslate_shift_lattice_mod_two_mul {Λ : AddSubgroup ℂ} {g : ℂ → ℂ} (h : OddLaw Λ g) {x t μ : ℂ} {m : ℕ}
    (hx : (m : ℂ) * x ∈ Λ) (ht : (m : ℂ) * t ∈ Λ) (hμ : μ ∈ Λ) :
    U1 Λ (x + 2 * m * μ) (U1 Λ t g) = U1 Λ x (U1 Λ t g) := by
  have hmμ : (m : ℂ) * μ ∈ Λ := by simpa using Λ.nsmul_mem hμ m
  have h2 : (2 * m * μ : ℂ) ∈ Λ := by
    rw [mul_assoc, two_mul]; exact Λ.add_mem hmμ hmμ
  have hω : U1 Λ (2 * m * μ) g = g := by
    funext z
    rw [h.2 _ h2, show (2 * m * μ : ℂ) / 2 = m * μ by ring, if_pos hmμ, one_mul]
  have e1 := thetaTranslation_comp_eq_cocycle_mul Λ (x + t) (2 * m * μ) g
  have f1 : gl3FieldFirst Λ (2 * m * μ) ((x + t) / 2) = gl3FieldFirst Λ μ (m * x + m * t) := by
    have a1 := riemannFormImag_real_smul_left Λ (2 * m) μ ((x + t) / 2)
    have a2 := riemannFormImag_real_smul_right Λ (2 * m) μ ((x + t) / 2)
    push_cast at a1 a2
    rw [a1, ← a2]
    congr 1
    ring
  have f2 : gl3FieldFirst Λ t ((x + 2 * m * μ) / 2) = gl3FieldFirst Λ t (x / 2) + gl3FieldFirst Λ (m * t) μ := by
    have a1 := riemannFormImag_real_smul_left Λ m t μ
    have a2 := riemannFormImag_real_smul_right Λ m t μ
    push_cast at a1 a2
    rw [a1, ← a2, show (x + 2 * m * μ) / 2 = x / 2 + m * μ by ring]
    simp only [gl3FieldFirst, map_add, mul_add, Complex.add_im, add_div]
  rw [hω, f1, h.ee_eq_one hμ (Λ.add_mem hx ht)] at e1
  rw [thetaTranslation_comp_eq_cocycle_mul, thetaTranslation_comp_eq_cocycle_mul, f2, ee_add, h.ee_eq_one ht hμ, e1, add_right_comm]
  simp only [one_mul, mul_one]

noncomputable def topHom (s : ℂ →+* ℂ) : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ :=
  s.toRatAlgHom.comp (IntermediateField.val ⊤)

theorem cj_topHom (s : ℂ →+* ℂ) (x : ℂ) : cj ⊤ (topHom s) x = s x := by
  simp only [cj, TaylorLogMetric.liftM, IntermediateField.mem_top, dif_pos]
  rfl

section GenusOne

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {s : ℂ →+* ℂ}

theorem exists_adp (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) {t : ℂ} {m : ℕ} (hm : 0 < m)
    (ht : (m : ℂ) * t ∈ lamOf D cc δ) {n : ℕ} (hn : 0 < n) :
    ∃ t', Adp1 ⊤ (topHom s) (lamOf D cc δ) n t t' := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨u, hu⟩ := (GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc ⊤ _ hK trivial trivial).1 (t / n)
    ⟨m * n, by positivity, by
      rw [show ((m * n : ℕ) : ℂ) * (t / n) = m * t by push_cast; field_simp]; exact ht⟩
    (Or.inr ⟨trivial, trivial⟩)
  exact ⟨n * u, by rwa [Adp1, mul_div_cancel_left₀ _ hn']⟩

theorem adp_add (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) {n : ℕ} {x x' t t' : ℂ}
    (hx : Adp1 ⊤ (topHom s) (lamOf D cc δ) n x x') (ht : Adp1 ⊤ (topHom s) (lamOf D cc δ) n t t') :
    Adp1 ⊤ (topHom s) (lamOf D cc δ) n (x + t) (x' + t') := by
  rw [Adp1, add_div, add_div]
  exact (GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc ⊤ _ hK trivial trivial).2.2.2.1 _ _ _ _ hx ht

theorem adp_half (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) {n : ℕ} {x x' : ℂ}
    (hx : Adp1 ⊤ (topHom s) (lamOf D cc δ) (2 * n) x x') :
    Adp1 ⊤ (topHom s) (lamOf D cc δ) n x x' := by
  have h := adp_add hc hK hx hx
  have e : ∀ y : ℂ, (y + y) / ((2 * n : ℕ) : ℂ) = y / n := fun y => by
    push_cast
    rw [← two_mul, mul_div_mul_left _ _ two_ne_zero]
  rwa [Adp1, e, e] at h

theorem adp_mem (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) {n m : ℕ} (hn : 0 < n) {x x' : ℂ}
    (hx : Adp1 ⊤ (topHom s) (lamOf D cc δ) n x x') (hm : (m : ℂ) * x ∈ lamOf D cc δ) :
    (m : ℂ) * x' ∈ lamConj ⊤ (topHom s) (lamOf D cc δ) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := (GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc ⊤ _ hK trivial trivial).2.2.2.2.2.1 (m * n) _ _ hx
  have e : ∀ y : ℂ, ((m * n : ℕ) : ℂ) * (y / n) = m * y := fun y => by
    push_cast; field_simp
  rw [e, e] at h
  exact h.1 hm

theorem sgStar_law (hc : Crv D cc δ) :
    Differentiable ℂ (sgStar (lamOf D cc δ)) ∧ OddLaw (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  have h := (GlobalTheory.OddTheta.sgStar_laws _
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc).1).1
  exact ⟨h.1, h.2.1, h.2.2.2⟩

theorem sgStar_conj_law (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) :
    Differentiable ℂ (sgStar (lamConj ⊤ (topHom s) (lamOf D cc δ))) ∧
      OddLaw (lamConj ⊤ (topHom s) (lamOf D cc δ)) (sgStar (lamConj ⊤ (topHom s) (lamOf D cc δ))) := by
  obtain ⟨cc', δ', hc', -, h⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc ⊤ _ hK trivial trivial 1 one_pos
  rw [h]
  exact sgStar_law hc'

theorem coef_translate (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) {m : ℕ} (hm : 0 < m) {t t' : ℂ}
    (ht : (m : ℂ) * t ∈ lamOf D cc δ) (ha : Adp1 ⊤ (topHom s) (lamOf D cc δ) (2 * (2 * m)) t t')
    (n : ℕ) : s (coef1 (U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ))) n) =
      coef1 (U1 (lamConj ⊤ (topHom s) (lamOf D cc δ)) t'
        (sgStar (lamConj ⊤ (topHom s) (lamOf D cc δ)))) n := by
  rw [← cj_topHom]
  refine GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ hc ⊤ _ hK trivial trivial t t' (2 * m) (by positivity) ?_ ha
    (fun _ => trivial) n
  rwa [show ((2 * m : ℕ) : ℂ) * (t / 2) = m * t by push_cast; ring]

theorem coef_translate₂ (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) {m : ℕ} (hm : 0 < m)
    {x x' t t' : ℂ} (hx : (m : ℂ) * x ∈ lamOf D cc δ) (ht : (m : ℂ) * t ∈ lamOf D cc δ)
    (hxa : Adp1 ⊤ (topHom s) (lamOf D cc δ) (2 * m) x x')
    (ha : Adp1 ⊤ (topHom s) (lamOf D cc δ) (2 * (2 * m)) t t')
    (n : ℕ) : s (coef1 (U1 (lamOf D cc δ) x (U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)))) n) =
      coef1 (U1 (lamConj ⊤ (topHom s) (lamOf D cc δ)) x' (U1 (lamConj ⊤ (topHom s) (lamOf D cc δ)) t'
        (sgStar (lamConj ⊤ (topHom s) (lamOf D cc δ))))) n := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨y, hy⟩ := exists_adp hc hK hm hx (n := 2 * (2 * m)) (by positivity)
  have hμ := ((GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc ⊤ _ hK trivial trivial).2.1 _ _ _ (adp_half hc hK hy)).1 hxa
  have hsh := (sgStar_conj_law hc hK).2.doubleTranslate_shift_lattice_mod_two_mul (adp_mem hc hK (by positivity) hxa hx)
    (adp_mem hc hK (by positivity) ha ht) hμ
  rw [show x' + 2 * m * (y / ((2 * m : ℕ) : ℂ) - x' / ((2 * m : ℕ) : ℂ)) = y by
    push_cast; field_simp; ring] at hsh
  rw [← hsh, thetaTranslation_comp_eq_cocycle_mul, thetaTranslation_comp_eq_cocycle_mul, taylorCoeffAtZero_const_mul, taylorCoeffAtZero_const_mul, map_mul,
    coef_translate hc hK hm (by rw [mul_add]; exact AddSubgroup.add_mem _ hx ht) (adp_add hc hK hy ha),
    ← cj_topHom]
  congr 1
  refine GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion D cc δ hc ⊤ _ hK trivial trivial t (x / 2) t' (y / 2) (2 * m) (by positivity)
    ?_ ?_ (adp_half hc hK ha) ?_ trivial
  · rw [show ((2 * m : ℕ) : ℂ) * t = m * t + m * t by push_cast; ring]
    exact AddSubgroup.add_mem _ ht ht
  · rwa [show ((2 * m : ℕ) : ℂ) * (x / 2) = m * x by push_cast; ring]
  · have e : ∀ w : ℂ, w / 2 / ((2 * m : ℕ) : ℂ) = w / ((2 * (2 * m) : ℕ) : ℂ) := fun w => by
      rw [div_div]; push_cast; rfl
    rwa [Adp1, e, e]

end GenusOne

section Coordinates

variable {D : D7} {N N' r : ℕ} (T : Tor D) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

noncomputable def coordL (j : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b j
  map_add' z w := by simp [coordB, add_mul, Finset.sum_add_distrib]
  map_smul' a z := by simp [coordB, Finset.mul_sum, mul_assoc]

theorem coordL_apply (j : Fin r) (z : VC D N N') : coordL T b j z = coordB D T b j z := rfl

theorem coordL_coordV (j : Fin r) (k : D.what₂.Tau × Fin N' × Fin N) :
    coordL T b j (coordV D k) = (starRingEnd ℂ) (T.emb k.1 (b j k.2.1 k.2.2)) := by
  simp [coordL_apply, coordB, coordV, ite_and]

theorem Hf_sum (z : VC D N N') (c : Fin r → ℂ) :
    Hf D T z (∑ j, c j • embV D T (b j)) =
      ∑ j, coordB D T b j z * (starRingEnd ℂ) (c j) / (area T.abelian₂ : ℂ) := by
  rw [Hf, ← Finset.sum_div]
  congr 1
  simp only [coordB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, embV,
    Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {T b} (hT : ∀ i j, coordB D T b j (embV D T (b i)) = if i = j then 1 else 0)
include hT

theorem coordB_sum (c : Fin r → ℂ) (j : Fin r) :
    coordB D T b j (∑ i, c i • embV D T (b i)) = c j := by
  change coordL T b j _ = _
  rw [map_sum]
  simp only [map_smul]
  simp [coordL_apply, hT]

theorem U_prod (c : Fin r → ℂ) (g : Fin r → ℂ → ℂ) :
    U D T (∑ j, c j • embV D T (b j)) (fun z => ∏ j, g j (coordL T b j z)) =
      fun z => ∏ j, U1 T.abelian₂ (c j) (g j) (coordL T b j z) := by
  funext z
  simp only [U, U1, Hf_sum, coordB_sum hT, Finset.prod_mul_distrib, ← Complex.exp_sum, map_add]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [show coordL T b j (∑ j, c j • embV D T (b j)) = c j from coordB_sum hT c j]
  · congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = -(Real.pi : ℂ) * coordB D T b j z * _ / _ - _
    simp only [div_eq_mul_inv, mul_inv]
    ring

theorem wdPh_sum (c : Fin r → ℂ) :
    wdPh D T (∑ j, c j • embV D T (b j)) = ∏ j, ee (q1 D T.abelian₂ (c j) / 2) := by
  rw [wdPh, ← ee_sum, qH, Hf_sum, Complex.re_sum, Finset.mul_sum, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordB_sum hT, q1, Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

omit hT in
theorem exists_of_mem_LaB {x : VC D N N'} (hx : x ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ x = ∑ j, w j • embV D T (b j) := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, j, rfl⟩ := hz
    refine ⟨Pi.single j w, fun i => ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs
      exacts [hw, T.abelian₂.zero_mem]
    · simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, fun _ => T.abelian₂.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨w + v, fun j => T.abelian₂.add_mem (hw j) (hv j), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨-w, fun j => T.abelian₂.neg_mem (hw j), by simp⟩

omit hT in
theorem exists_of_nsmul_mem_LaB {x : VC D N N'} {m : ℕ} (hm : 0 < m) (hx : m • x ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, (m : ℂ) * w j ∈ T.abelian₂) ∧ x = ∑ j, w j • embV D T (b j) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨w, hw, h⟩ := exists_of_mem_LaB hx
  refine ⟨fun j => (m : ℂ)⁻¹ * w j, fun j => by rw [mul_inv_cancel_left₀ hm']; exact hw j, ?_⟩
  simp only [mul_smul]
  rw [← Finset.smul_sum, ← h, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hm']

omit hT in
theorem U_comb {k : ℕ} (x : VC D N N') (c : Fin k → ℂ) (F : Fin k → VC D N N' → ℂ) :
    U D T x (fun z => ∑ i, c i * F i z) = fun z => ∑ i, c i * U D T x (F i) z := by
  funext z
  simp only [U, Finset.sum_mul, mul_assoc]

end Coordinates

section Main

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {s : ℂ →+* ℂ} {N N' r : ℕ}
  {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem sum_emb_pair (hb : OnB D b) (i j : Fin r) :
    ∑ τ, embT D τ (∑ a, ∑ c, b i a c * D.host.conj (b j a c)) = if i = j then 1 else 0 := by
  rw [(GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1.2]
  have h := hb.1 i j
  rw [hYY] at h
  rw [h]
  split_ifs <;> simp

theorem torConj_emb (τ : D.what₂.Tau) (x : D.host.E) :
    (torConj D (tor0 D cc δ) ⊤ (topHom s)).emb τ x = s.comp (embT D τ) x := cj_topHom s _

theorem frameCoordinate_orthonormal_baseTorus (hb : OnB D b) (i j : Fin r) :
    coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b i)) = if i = j then 1 else 0 := by
  rw [← sum_emb_pair hb]
  simp only [coordB, embV, tor0, map_sum, map_mul, emb_conj]

theorem ortho_torConj (hb : OnB D b) (i j : Fin r) :
    coordB D (torConj D (tor0 D cc δ) ⊤ (topHom s)) b j
      (embV D (torConj D (tor0 D cc δ) ⊤ (topHom s)) (b i)) = if i = j then 1 else 0 := by
  have h := congrArg s (sum_emb_pair hb i j)
  rw [apply_ite s, map_one, map_zero, map_sum] at h
  rw [← h]
  simp only [coordB, embV, torConj_emb, ← emb_conj]
  simp only [map_sum, map_mul, RingHom.comp_apply]

theorem conjPair_prod {g g' : Fin r → ℂ → ℂ} (hg : ∀ j, Differentiable ℂ (g j))
    (hg' : ∀ j, Differentiable ℂ (g' j)) (h : ∀ j n, s (coef1 (g j) n) = coef1 (g' j) n) :
    ConjPair D s (fun z => ∏ j, g j (coordL (tor0 D cc δ) b j z))
      (fun z => ∏ j, g' j (coordL (torConj D (tor0 D cc δ) ⊤ (topHom s)) b j z)) :=
  ConjPair.prod fun j => ConjPair.comp_form (hg j) (hg' j) (h j) _ _ fun k => by
    rw [coordL_coordV, coordL_coordV, torConj_emb, ← emb_conj]
    exact congrArg s (emb_conj (embT D k.1) _).symm

theorem exists_conjPair (hc : Crv D cc δ) (hK : FixK D ⊤ (topHom s)) (hb : OnB D b) {k : ℕ}
    (c : Fin k → ℂ) (t : Fin k → VC D N N') (u u' : Fin r → ℂ) {m : ℕ} (hm : 0 < m)
    (hx : m • (∑ j, u j • embV D (tor0 D cc δ) (b j)) ∈ LaB D (tor0 D cc δ) b)
    (ht : ∀ i, m • t i ∈ LaB D (tor0 D cc δ) b)
    (hu : ∀ j, Adp1 ⊤ (topHom s) (lamOf D cc δ) (2 * m) (u j) (u' j)) :
    (∃ G', ConjPair D s (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) G' ∧
      ConjPair D s (U D (tor0 D cc δ) (∑ j, u j • embV D (tor0 D cc δ) (b j))
          (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))))
        (U D (torConj D (tor0 D cc δ) ⊤ (topHom s))
          (∑ j, u' j • embV D (torConj D (tor0 D cc δ) ⊤ (topHom s)) (b j)) G')) ∧
    s (wdPh D (tor0 D cc δ) (∑ j, u j • embV D (tor0 D cc δ) (b j))) =
      wdPh D (torConj D (tor0 D cc δ) ⊤ (topHom s))
        (∑ j, u' j • embV D (torConj D (tor0 D cc δ) ⊤ (topHom s)) (b j)) := by
  have hum : ∀ j, (m : ℂ) * u j ∈ lamOf D cc δ := fun j => by
    obtain ⟨w, hw, h⟩ := exists_of_nsmul_mem_LaB hm hx
    have := congrArg (coordB D (tor0 D cc δ) b j) h
    rw [coordB_sum (frameCoordinate_orthonormal_baseTorus hb), coordB_sum (frameCoordinate_orthonormal_baseTorus hb)] at this
    rw [this]
    exact hw j
  choose w hw htw using fun i => exists_of_nsmul_mem_LaB hm (ht i)
  choose w' hw' using fun i j => exists_adp hc hK hm (hw i j) (n := 2 * (2 * m)) (by positivity)
  have hd := (sgStar_law hc).1
  have hd' := (sgStar_conj_law hc hK).1
  have hG : comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) =
      fun z => ∑ i, c i * ∏ j, U1 (lamOf D cc δ) (w i j) (sgStar (lamOf D cc δ))
        (coordL (tor0 D cc δ) b j z) := by
    funext z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [htw i]
    exact congrArg (c i * ·)
      (congrFun (U_prod (frameCoordinate_orthonormal_baseTorus hb) (w i) fun _ => sgStar (lamOf D cc δ)) z)
  refine ⟨⟨fun z => ∑ i, s (c i) * ∏ j, U1 (lamConj ⊤ (topHom s) (lamOf D cc δ)) (w' i j)
    (sgStar (lamConj ⊤ (topHom s) (lamOf D cc δ)))
      (coordL (torConj D (tor0 D cc δ) ⊤ (topHom s)) b j z), ?_, ?_⟩, ?_⟩
  · rw [hG]
    exact ConjPair.sum fun i => (conjPair_prod (fun j => differentiable_U1 _ _ hd)
      (fun j => differentiable_U1 _ _ hd')
      fun j n => coef_translate hc hK hm (hw i j) (hw' i j) n).const_mul (c i)
  · rw [hG, U_comb, U_comb]
    refine ConjPair.sum fun i => ConjPair.const_mul ?_ (c i)
    rw [U_prod (frameCoordinate_orthonormal_baseTorus hb), U_prod (ortho_torConj hb)]
    exact conjPair_prod (fun j => differentiable_U1 _ _ (differentiable_U1 _ _ hd))
      (fun j => differentiable_U1 _ _ (differentiable_U1 _ _ hd'))
      fun j n => coef_translate₂ hc hK hm (hum j) (hw i j) (hu j) (hw' i j) n
  · rw [wdPh_sum (frameCoordinate_orthonormal_baseTorus hb), wdPh_sum (ortho_torConj hb), map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← cj_topHom]
    exact (GlobalTheory.T.cmQuadraticPhase_equivariant_embeddings D cc δ hc).2 ⊤ _ hK trivial trivial _ _ m hm (hum j) (hu j) trivial

end Main

theorem galB_all : ∀ D : D7, galB D := by
  intro D cc δ hc M ρ hK hM N N' r b hb k c t x x' m hm hx ht ⟨u, u', _, hxu, hxu', hu⟩ hG hUG
  set G := comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) with hGdef
  let S : Set ℂ := Set.range (fun p : D.what₂.Tau × D.host.E => embT D p.1 p.2) ∪
    Set.range D.host.φ₀ ∪ {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wdPh D (tor0 D cc δ) x} ∪
    Set.range (TaylorLogMetric.taylor D G) ∪ Set.range (TaylorLogMetric.taylor D (U D (tor0 D cc δ) x G)) ∪
    Set.range (TaylorLogMetric.taylor D (Wd D (tor0 D cc δ) x G)) ∪
    Set.range (fun j => wpF (lamOf D cc δ) (u j / ((2 * m : ℕ) : ℂ))) ∪
    Set.range (fun j => wpD (lamOf D cc δ) (u j / ((2 * m : ℕ) : ℂ)))
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have hS : S.Countable := by
    simp only [S, Set.countable_union, Set.countable_range, Set.countable_insert,
      Set.countable_singleton, and_self]
  obtain ⟨s, hs⟩ := exists_endo_eq_cj M ρ hS
  have hK' : FixK D ⊤ (topHom s) := fun a =>
    ⟨trivial, by rw [cj_topHom, ← hs _ (by simp [S]) (hK a).1, (hK a).2]⟩
  have hΛ : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (topHom s) (lamOf D cc δ) := by
    have h2 := (hs (g2 (lamOf D cc δ)) (by simp [S]) hM.2.1).trans (cj_topHom s _).symm
    have h3 := (hs (g3 (lamOf D cc δ)) (by simp [S]) hM.2.2).trans (cj_topHom s _).symm
    simp only [cj] at h2 h3
    simp only [lamConj, h2, h3]
  have hT : torConj D (tor0 D cc δ) M ρ = torConj D (tor0 D cc δ) ⊤ (topHom s) := by
    simp only [torConj, Tor.mk.injEq]
    refine ⟨funext fun τ => funext fun y => ?_, hΛ⟩
    exact (hs (embT D τ y) (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      ⟨(τ, y), rfl⟩))))))) (hM.1 τ y)).trans (cj_topHom s _).symm
  have hu' : ∀ j, Adp1 ⊤ (topHom s) (lamOf D cc δ) (2 * m) (u j) (u' j) := fun j => by
    have h := hu j
    change StarPt M ρ (lamOf D cc δ) _ _ at h
    rw [StarPt, hΛ] at h
    refine h.imp id fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, trivial, trivial, ?_, ?_⟩
    · rw [h5, cj_topHom, hs _ (by simp [S]) h3]
    · rw [h6, cj_topHom, hs _ (by simp [S]) h4]
  rw [hT] at hxu' ⊢
  obtain ⟨⟨G', h1, h2⟩, h3⟩ := exists_conjPair hc hK' hb c t u u' hm (hxu ▸ hx) ht hu'
  rw [← hxu, ← hxu'] at h2 h3
  rw [← hGdef] at h1 h2
  rw [h1.fnConj_eq fun α => hs _ (by simp [S]) (hG α)]
  refine ⟨h2.fnConj_eq fun α => hs _ (by simp [S]) (hUG α), fun hw =>
    ⟨(hs _ (by simp [S]) hw).trans h3, ?_⟩⟩
  have h4 := h2.const_mul (wdPh D (tor0 D cc δ) x)
  rw [h3] at h4
  refine h4.fnConj_eq fun α => hs _ ?_ ?_
  · exact Or.inl (Or.inl (Or.inr ⟨α, rfl⟩))
  · rw [taylor_const_mul h2.1]
    exact M.mul_mem hw (hUG α)

end GlobalTheory.ProdThetaConj
