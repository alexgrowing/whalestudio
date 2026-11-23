import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero

noncomputable section

namespace GlobalTheory.Mem.Col2.ThetaVec

open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real

variable (L : PeriodPair)

theorem area_eq : F.area L = latticeArea L := (latticeArea_eq L).symm

theorem herm_eq (z w : ℂ) : F.herm L z w = latticeForm L z w := by
  rw [F.herm, latticeForm, area_eq]

theorem semiChar_eq (w : ℂ) : F.semiChar L w = sigmaSign L w := by
  unfold F.semiChar sigmaSign
  congr

theorem wEta_eq : F.wEta L = quasiPeriod L := by
  have : F.wZeta L = weierstrassZeta L := by
    funext z
    simp only [F.wZeta, weierstrassZeta, zetaTerm_eq]
  rw [F.wEta, quasiPeriod, this]

theorem quasiPeriodConst_eq : F.s2 L = sTwo L := by
  have h : L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ ≠ 0 := by
    intro h0
    have h1 := latticeArea_pos L
    rw [latticeArea_eq] at h1
    have h2 := congrArg Complex.im h0
    simp at h1 h2
    apply h1
    linarith
  rw [F.s2, wEta_eq, quasiPeriod_eq, quasiPeriod_eq, div_eq_iff h]
  ring

theorem sgStar_eq : F.sgStar L = canonicalSigma L := by
  funext z
  have : ∀ l : ℂ, F.wFactor l z = sigmaFactor l z := by
    intro l
    rw [sigmaFactor_eq, F.wFactor, primaryFactor, div_pow, div_div, mul_comm (l ^ 2)]
  rw [F.sgStar, canonicalSigma, F.wSigma, weierstrassSigma, sigmaProd, quasiPeriodConst_eq]
  simp only [this]
  congr 2
  ring

def form1 : Sesq ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => latticeForm L z w)
    (latticeForm_add_left L) (fun a u v => latticeForm_mul_left L a u v) (latticeForm_add_right L)
    (fun a u v => latticeForm_mul_right L a u v)

theorem periodLatticeSesquilinearForm_apply (z w : ℂ) : form1 L z w = latticeForm L z w := rfl

theorem periodLatticeSesquilinearForm_isHerm : IsHerm (form1 L) := fun x y => (conj_latticeForm L x y).symm

theorem opU_eq (x : ℂ) (G : ℂ → ℂ) : F.opU L x G = opU (form1 L) x G := by
  funext z
  simp only [F.opU, opU, herm_eq, periodLatticeSesquilinearForm_apply]

theorem th0Char_eq (ω₀ ω : ℂ) :
    F.thetaZeroCharacter L ω₀ ω = sigmaSign L ω * cexp (π * I * (altE (form1 L) ω ω₀ : ℂ)) := by
  rw [F.thetaZeroCharacter, semiChar_eq, F.altE, herm_eq]; rfl

theorem sigmaSign_sq (w : ℂ) : sigmaSign L w * sigmaSign L w = 1 := by
  unfold sigmaSign; split_ifs <;> simp

theorem law_iff (G : ℂ → ℂ) (w z : ℂ) :
    sigmaSign L w * opU (form1 L) w G z = G z ↔
      G (z + w) = sigmaSign L w * cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * G z := by
  have he : cexp (-(π : ℂ) * form1 L z w - π * form1 L w w / 2) *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) = 1 := by
    rw [← Complex.exp_add, periodLatticeSesquilinearForm_apply, periodLatticeSesquilinearForm_apply, ← Complex.exp_zero]; congr 1; ring
  have hs := sigmaSign_sq L w
  rw [opU]
  constructor
  · intro h
    rw [← h]
    linear_combination (-G (z + w)) * he - (G (z + w) * cexp (-(π : ℂ) * form1 L z w - π * form1 L w w / 2) *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2)) * hs
  · intro h
    rw [h]
    linear_combination (G z) * he + (G z * cexp (-(π : ℂ) * form1 L z w - π * form1 L w w / 2) *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2)) * hs

theorem chi_half (ω ω₀ : ℂ) :
    cexp (π * I * (altE (form1 L) ω ω₀ : ℂ)) * chi (form1 L) ω (ω₀ / 2) = 1 := by
  have : altE (form1 L) ω ω₀ = 2 * altE (form1 L) ω (ω₀ / 2) := by
    conv_lhs => rw [← add_halves ω₀]
    simp only [altE, map_add, add_im]; ring
  rw [chi, ← Complex.exp_add, this, ← Complex.exp_zero]
  congr 1; push_cast; ring

theorem thetaZero_periodLattice_eq (t z : ℂ) :
    F.th0 L t z = opU (form1 L) t (canonicalSigma L) z / opU (form1 L) t (canonicalSigma L) 0 := by
  rw [F.th0, opU_eq, sgStar_eq]

theorem const_ne {t : ℂ} (ht : t ∉ L.lattice) : opU (form1 L) t (canonicalSigma L) 0 ≠ 0 := by
  rw [opU, zero_add]
  exact mul_ne_zero ((canonicalSigma_eq_zero_iff L).not.2 ht) (Complex.exp_ne_zero _)

theorem evenTheta_zero_eq_one {t : ℂ} (ht : t ∉ L.lattice) : F.th0 L t 0 = 1 := by
  rw [thetaZero_periodLattice_eq, div_self (const_ne L ht)]

theorem differentiable_evenTheta (t : ℂ) : Differentiable ℂ (F.th0 L t) := by
  have : F.th0 L t = fun z => opU (form1 L) t (canonicalSigma L) z / opU (form1 L) t (canonicalSigma L) 0 :=
    funext (thetaZero_periodLattice_eq L t)
  rw [this]
  exact (differentiable_opU (differentiable_canonicalSigma L) t).div_const _

theorem evenTheta_translation_law (ω₀ : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    F.thetaZeroCharacter L ω₀ ω * opU (form1 L) ω (F.th0 L (ω₀ / 2)) z = F.th0 L (ω₀ / 2) z := by
  have e : F.th0 L (ω₀ / 2) = fun z => (opU (form1 L) (ω₀ / 2) (canonicalSigma L) 0)⁻¹ *
      opU (form1 L) (ω₀ / 2) (canonicalSigma L) z := by
    funext z; rw [thetaZero_periodLattice_eq, div_eq_inv_mul]
  have e2 : opU (form1 L) ω (canonicalSigma L) = fun z => sigmaSign L ω * canonicalSigma L z := by
    funext z
    rw [← (law_iff L _ ω z).2 (canonicalSigma_add L hω z), ← mul_assoc, sigmaSign_sq, one_mul]
  rw [e, opU_mul, opU_comm (periodLatticeSesquilinearForm_isHerm L), e2, opU_mul, th0Char_eq]
  have h1 := chi_half L ω ω₀
  have h2 := sigmaSign_sq L ω
  set c := (opU (form1 L) (ω₀ / 2) (canonicalSigma L) 0)⁻¹ * opU (form1 L) (ω₀ / 2) (canonicalSigma L) z
  linear_combination (c * sigmaSign L ω * sigmaSign L ω) * h1 + c * h2

theorem opU_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (G : V → ℂ) : opU H 0 G = G := by
  funext w; simp [opU]

theorem evenTheta_spans_thetaSpace {ω₀ : ℂ} (h0 : ω₀ / 2 ∉ L.lattice) {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hlaw : ∀ ω ∈ L.lattice, ∀ z, F.thetaZeroCharacter L ω₀ ω * opU (form1 L) ω G z = G z) (z : ℂ) :
    G z = G 0 * F.th0 L (ω₀ / 2) z := by
  set t := ω₀ / 2 with ht
  obtain ⟨c, hc⟩ := exists_eq_mul_canonicalSigma L (differentiable_opU (H := form1 L) hG (-t)) fun w hw z => by
    rw [← law_iff, opU_comm (periodLatticeSesquilinearForm_isHerm L)]
    conv_rhs => rw [← funext (hlaw w hw)]
    rw [opU_mul, th0Char_eq]
    have h1 := chi_half L w ω₀
    have h2 : chi (form1 L) w (-t) * chi (form1 L) w t = 1 := by
      rw [← chi_add_right]; simp [chi, altE]
    set u := sigmaSign L w * opU (form1 L) (-t) (opU (form1 L) w G) z
    linear_combination (-u * chi (form1 L) w (-t)) * h1 + u * cexp (π * I * (altE (form1 L) w ω₀ : ℂ)) * h2
  have key : ∀ z, G z = c * opU (form1 L) t (canonicalSigma L) z := by
    intro z
    rw [← opU_mul, ← funext hc, opU_opU (periodLatticeSesquilinearForm_isHerm L), add_neg_cancel, opU_zero]
    have : altE (form1 L) t (-t) = 0 := by
      have := altE_swap (periodLatticeSesquilinearForm_isHerm L) t t
      simp only [altE, map_neg, neg_im] at this ⊢
      linarith
    simp [this]
  rw [key z, key 0, thetaZero_periodLattice_eq]
  have := const_ne L h0
  field_simp

theorem exp_int_sign (k : ℤ) : cexp (π * I * ((k : ℝ) : ℂ)) = 1 ∨ cexp (π * I * ((k : ℝ) : ℂ)) = -1 := by
  rw [mul_comm, Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases Int.even_or_odd k with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem th0Char_sq {ω₀ ω : ℂ} (h0 : ω₀ ∈ L.lattice) (h : ω ∈ L.lattice) :
    F.thetaZeroCharacter L ω₀ ω * F.thetaZeroCharacter L ω₀ ω = 1 := by
  obtain ⟨k, hk⟩ := exists_int_im_latticeForm L h h0
  have : altE (form1 L) ω ω₀ = k := hk
  rw [th0Char_eq, this, mul_mul_mul_comm, sigmaSign_sq]
  rcases exp_int_sign k with h | h <;> rw [h] <;> norm_num

theorem th0Char_zero (ω₀ : ℂ) : F.thetaZeroCharacter L ω₀ 0 = 1 := by
  rw [th0Char_eq, sigmaSign_of_mem L (by simp)]
  simp [altE]

theorem th0Char_add (ω₀ : ℂ) {a b : ℂ} (ha : a ∈ L.lattice) (hb : b ∈ L.lattice) :
    F.thetaZeroCharacter L ω₀ (a + b) = F.thetaZeroCharacter L ω₀ a * F.thetaZeroCharacter L ω₀ b * cexp (π * I * (altE (form1 L) a b : ℂ)) := by
  simp only [th0Char_eq, sigmaSign_add L ha hb]
  have : (altE (form1 L) (a + b) ω₀ : ℂ) = altE (form1 L) a ω₀ + altE (form1 L) b ω₀ := by
    simp [altE]
  rw [this, mul_add, Complex.exp_add]
  change _ * _ * cexp (π * I * (altE (form1 L) a b : ℂ)) * _ = _
  ring

theorem mem_of_int {x : ℂ} (h : ∀ y ∈ L.lattice, ∃ m : ℤ, altE (form1 L) x y = m) : x ∈ L.lattice := by
  obtain ⟨a, ha⟩ := h _ L.ω₁_mem_lattice
  obtain ⟨b, hb⟩ := h _ L.ω₂_mem_lattice
  have hx := L.basis.sum_repr x
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hx
  set s := L.basis.repr x 0
  set t := L.basis.repr x 1
  have hs : ∀ u : ℂ, altE (form1 L) u u = 0 := fun u => by
    have := altE_swap (periodLatticeSesquilinearForm_isHerm L) u u
    linarith
  have e : ∀ y, altE (form1 L) x y = s * altE (form1 L) L.ω₁ y + t * altE (form1 L) L.ω₂ y := by
    intro y
    rw [← altE_real_smul_left, ← altE_real_smul_left, ← hx]
    simp only [altE, map_add, LinearMap.add_apply, add_im]
  rw [e, hs] at ha hb
  rw [altE_swap (periodLatticeSesquilinearForm_isHerm L) L.ω₂] at hb
  have h1 : |altE (form1 L) L.ω₂ L.ω₁| = 1 := abs_im_latticeForm L
  rw [PeriodPair.mem_lattice]
  rcases (abs_eq zero_le_one).1 h1 with h2 | h2 <;> rw [h2] at ha hb
  · refine ⟨-b, a, ?_⟩
    rw [← hx, show s = -b by linarith, show t = a by linarith]
    simp
  · refine ⟨b, -a, ?_⟩
    rw [← hx, show s = b by linarith, show t = -a by linarith]
    simp

section Std

variable {n : Type} [Fintype n] [DecidableEq n]

theorem stdH_apply (z w : n → ℂ) : stdH L n z w = ∑ i, form1 L (z i) (w i) := by
  change ∑ i, ∑ j, z i * _ * conj (w j) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply_ne hj.symm]) (by simp), periodLatticeSesquilinearForm_apply,
    latticeForm, area_eq]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  ring

theorem stdH_herm : IsHerm (stdH L n) := fun x y => by
  simp only [stdH_apply, map_sum, ← periodLatticeSesquilinearForm_isHerm L _ _]

theorem altE_stdH (z w : n → ℂ) : altE (stdH L n) z w = ∑ i, altE (form1 L) (z i) (w i) := by
  simp only [altE, stdH_apply, Complex.im_sum]

theorem stdH_single (z : n → ℂ) (i : n) (w : ℂ) : stdH L n z (Pi.single i w) = form1 L (z i) w := by
  rw [stdH_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

omit [Fintype n] [DecidableEq n] in
theorem mem_stdLat {x : n → ℂ} : x ∈ stdLat L n ↔ ∀ i, x i ∈ L.lattice := by
  simp [stdLat, AddSubgroup.mem_pi]

omit [Fintype n] in
theorem single_mem (i : n) {w : ℂ} (hw : w ∈ L.lattice) : (Pi.single i w : n → ℂ) ∈ stdLat L n :=
  (mem_stdLat L).2 fun j => by
    by_cases h : j = i
    · subst h; simpa using hw
    · simp [Pi.single_eq_of_ne h]

theorem std_selfDual : IsSelfDual (stdH L n) (stdLat L n) := by
  ext x
  constructor
  · intro h
    refine (mem_stdLat L).2 fun i => mem_of_int L fun y hy => ?_
    have := h _ (single_mem L i hy)
    rwa [altE, stdH_single] at this
  · intro h y hy
    choose k hk using fun i => exists_int_im_latticeForm L ((mem_stdLat L).1 h i) ((mem_stdLat L).1 hy i)
    refine ⟨∑ i, k i, ?_⟩
    rw [altE_stdH]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hk i

theorem std_semiChar {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) {α : (n → ℂ) → ℂ}
    (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) : IsSemiChar (stdH L n) (stdLat L n) α := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [← mul_self_eq_one_iff, hα x hx, stdChar, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => th0Char_sq L h0 ((mem_stdLat L).1 hx i)
  · rw [hα x hx, hα y hy, hα _ (add_mem hx hy), stdChar, stdChar, stdChar, altE_stdH, Complex.ofReal_sum,
      Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => th0Char_add L ω₀ ((mem_stdLat L).1 hx i) ((mem_stdLat L).1 hy i)

omit [DecidableEq n] in
theorem productEvenTheta_zero_eq_one {ω₀ : ℂ} (h : ω₀ / 2 ∉ L.lattice) : F0 L ω₀ n 0 = 1 := by
  simp [F0, prodFn, evenTheta_zero_eq_one L h]

theorem productEvenTheta_mem_thetaSpace (ω₀ : ℂ) {α : (n → ℂ) → ℂ} (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) :
    F0 L ω₀ n ∈ Th (stdH L n) α (stdLat L n) := by
  refine ⟨fun z _ => ?_, fun x hx z => ?_⟩
  · refine Finset.analyticAt_fun_prod (f := fun i (z : n → ℂ) => F.th0 L (ω₀ / 2) (z i)) _ fun i _ => ?_
    exact ((differentiable_evenTheta L _).analyticAt _).comp (f := fun z : n → ℂ => z i)
      ((ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ).analyticAt z)
  · rw [hα x hx, stdChar, opU, stdH_apply, stdH_apply, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib, Complex.exp_sum, F0, prodFn, prodFn, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => evenTheta_translation_law L ω₀ ((mem_stdLat L).1 hx i) (z i)

theorem std_line {ω₀ : ℂ} (h0 : ω₀ / 2 ∉ L.lattice) {α : (n → ℂ) → ℂ}
    (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) {G : (n → ℂ) → ℂ} (hG : Differentiable ℂ G)
    (hF : G ∈ fixedBy (stdH L n) α (stdLat L n)) : G = G 0 • F0 L ω₀ n := by
  have one : ∀ (z : n → ℂ) (i : n), G z = G (Function.update z i 0) * F.th0 L (ω₀ / 2) (z i) := by
    intro z i
    have := evenTheta_spans_thetaSpace L h0 (G := fun x => G (Function.update z i x))
      (hG.comp (fun x => (hasDerivAt_update z i x).differentiableAt)) (fun ω hω x => by
        have h1 := hF _ (single_mem L i hω) (Function.update z i x)
        rw [hα _ (single_mem L i hω), stdChar,
          Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, th0Char_zero]) (by simp),
          opU, stdH_single, stdH_single] at h1
        have h2 : Function.update z i x + Pi.single i ω = Function.update z i (x + ω) := by
          funext j
          by_cases h : j = i
          · subst h; simp
          · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
        rw [h2] at h1
        simpa [opU] using h1) (z i)
    simpa using this
  have all : ∀ (s : Finset n) (z : n → ℂ),
      G z = G (fun i => if i ∈ s then 0 else z i) * ∏ i ∈ s, F.th0 L (ω₀ / 2) (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      intro z
      rw [ih z, one _ i, Finset.prod_insert hi, if_neg hi, mul_assoc]
      congr 2
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  funext z
  rw [all Finset.univ z]
  simp only [Finset.mem_univ, if_true]
  rfl

end Std

section Four

variable {n : Type} [Fintype n]

theorem matH_apply (h : Matrix n n ℂ) (z w : n → ℂ) : matH h z w = ∑ i, ∑ j, z i * h i j * conj (w j) := rfl

theorem matrixForm_fourfoldBlock (h : Matrix n n ℂ) (z w : Fin 4 × n → ℂ) :
    matH (blk4 h) z w = ∑ a, matH h (slice a z) (slice a w) := by
  simp only [matH_apply, Fintype.sum_prod_type, blk4, slice]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb.symm]) (by simp)]
  simp

theorem analyticAt_slice (a : Fin 4) (z : Fin 4 × n → ℂ) : AnalyticAt ℂ (slice (n := n) a) z :=
  (ContinuousLinearMap.pi fun i : n => (ContinuousLinearMap.proj (a, i) : (Fin 4 × n → ℂ) →L[ℂ] ℂ)).analyticAt z

theorem tens4Mem : Tens4Mem := by
  intro n _ h Λ α θ hθ
  refine ⟨fun z _ => ?_, fun x hx z => ?_⟩
  · exact Finset.analyticAt_fun_prod (f := fun a (v : Fin 4 × n → ℂ) => θ a (slice a v)) _ fun a _ =>
      ((hθ a).1 _ trivial).comp (analyticAt_slice a z)
  · rw [opU, matrixForm_fourfoldBlock, matrixForm_fourfoldBlock, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib, Complex.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (hθ a).2 _ (hx a) (slice a z)

def ins (z : Fin 4 × n → ℂ) (x : n → ℂ) : Fin 4 × n → ℂ := fun w => if w.1 = 0 then x w.2 else z w

omit [Fintype n] in
theorem slice_ins (z : Fin 4 × n → ℂ) (x : n → ℂ) (a : Fin 4) :
    slice a (ins z x) = if a = 0 then x else slice a z := by
  funext i
  by_cases h : a = 0 <;> simp [slice, ins, h]

theorem ins_mem {h : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)} {α : (n → ℂ) → ℂ} (h0 : α 0 = 1)
    {P : (Fin 4 × n → ℂ) → ℂ} (hP : P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ))
    (z : Fin 4 × n → ℂ) : (fun x => P (ins z x)) ∈ Th (matH h) α Λ := by
  have hs : ∀ a, slice a (0 : Fin 4 × n → ℂ) = 0 := fun _ => rfl
  refine ⟨fun x _ => ?_, fun y hy x => ?_⟩
  · refine (hP.1 _ trivial).comp (f := ins z) (analyticAt_pi_iff.2 fun w => ?_)
    by_cases hw : w.1 = 0
    · simp only [ins, hw, if_true]
      exact (ContinuousLinearMap.proj w.2 : (n → ℂ) →L[ℂ] ℂ).analyticAt x
    · simp only [ins, hw, if_false]
      exact analyticAt_const
  · have h1 := hP.2 (ins 0 y) (fun a => by rw [slice_ins]; split_ifs; exacts [hy, Λ.zero_mem]) (ins z x)
    have h2 : ins z x + ins 0 y = ins z (x + y) := by
      funext w
      by_cases hw : w.1 = 0 <;> simp [ins, hw]
    rw [opU, h2, matrixForm_fourfoldBlock, matrixForm_fourfoldBlock] at h1
    simpa [opU, slice_ins, Fin.sum_univ_four, Fin.prod_univ_four, hs, h0] using h1

theorem fourthRoot : FourthRoot := by
  intro n _ h Λ α h0 P hP hne hline
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  constructor
  · have hf := ins_mem h0 hP z₀
    obtain ⟨c, hc⟩ := hline _ (tens4Mem n h Λ α (fun _ => fun x => P (ins z₀ x)) fun _ => hf)
    have hz : ins z₀ (slice 0 z₀) = z₀ := by
      funext ⟨a, i⟩
      by_cases hw : a = 0 <;> simp [ins, slice, hw]
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := congrFun hc fun w => z₀ (0, w.2)
      rw [zero_smul, Pi.zero_apply, Finset.prod_eq_zero_iff] at this
      obtain ⟨a, -, ha⟩ := this
      exact hz₀ (hz ▸ ha)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (n := 4) (by norm_num)
    refine ⟨r • fun x => P (ins z₀ x), Submodule.smul_mem _ r hf, ?_⟩
    funext v
    have := congrFun hc v
    simp only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this ⊢
    rw [this, hr, inv_mul_cancel_left₀ hc0]
  · intro θ hθ hP4
    obtain ⟨a, ha⟩ : ∃ a, θ a ≠ 0 := ⟨slice 0 z₀, fun h0 => hz₀ (by
      rw [← hP4]; exact Finset.prod_eq_zero (Finset.mem_univ 0) h0)⟩
    have span : ∀ G ∈ Th (matH h) α Λ, ∃ c : ℂ, G = c • θ := by
      intro G hG
      obtain ⟨c, hc⟩ := hline _ (tens4Mem n h Λ α ![G, θ, θ, θ] fun b => by fin_cases b <;> simpa)
      refine ⟨c, funext fun x => ?_⟩
      have := congrFun hc (ins (fun w => a w.2) x)
      have hs : ∀ b, slice b (fun w : Fin 4 × n => a w.2) = a := fun _ => rfl
      rw [← hP4] at this
      simp only [tens4, Pi.smul_apply, smul_eq_mul, Fin.prod_univ_four, slice_ins, hs] at this
      simp only [Fin.isValue, if_true, Fin.reduceEq, if_false, Matrix.cons_val] at this
      apply mul_right_cancel₀ (pow_ne_zero 3 ha)
      rw [Pi.smul_apply, smul_eq_mul]
      linear_combination this
    refine ⟨fun θ' hθ' hP' => ?_, span⟩
    obtain ⟨c, rfl⟩ := span θ' hθ'
    refine ⟨c, ?_, rfl⟩
    have := congrFun (hP'.trans hP4.symm) z₀
    rw [← hP4] at hz₀
    simp only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    exact mul_right_cancel₀ hz₀ (this.trans (one_mul _).symm)

theorem analytic_inter (H : Sesq (n → ℂ)) (α : (n → ℂ) → ℂ) (A₁ A₂ : AddSubgroup (n → ℂ))
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] {G : (n → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (inter H α A₁ A₂ G) Set.univ := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  rw [inter_eq]
  intro z _
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.mul ?_)
  generalize ((Quotient.out c : A₂) : n → ℂ) = x
  have h : AnalyticAt ℂ (fun z => H z x) z := (LinearMap.toContinuousLinearMap (H.flip x)).analyticAt z
  exact ((hG _ trivial).comp (f := fun z => z + x) (analyticAt_id.add analyticAt_const)).mul
    (((analyticAt_const.mul h).sub analyticAt_const).cexp)

theorem inter_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V)
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] (c : ℂ) (G : V → ℂ) :
    inter H α A₁ A₂ (c • G) = c • inter H α A₁ A₂ G := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  rw [inter_eq, inter_eq]
  funext z
  simp only [opU, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem thetaVector : ThetaVector := by
  intro L ω₀ n _ _ h Λ α β g S κ hκ
  set A := imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) with hA
  have f1 : Finite (A ⧸ (stdLat L (Fin 4 × n)).addSubgroupOf A) := Nat.finite_of_card_ne_zero S.idx₁
  have f2 : Finite (stdLat L (Fin 4 × n) ⧸ A.addSubgroupOf (stdLat L (Fin 4 × n))) :=
    Nat.finite_of_card_ne_zero S.idx₂
  have hH := stdH_herm L (n := Fin 4 × n)
  have hd := std_selfDual L (n := Fin 4 × n)
  have hs := std_semiChar L S.per S.betaStd
  have hF := productEvenTheta_mem_thetaSpace L ω₀ S.betaStd
  have hiso : ∀ x y, stdH L (Fin 4 × n) (g x) (g y) = matH (blk4 h) x y := S.isom
  have hK : inter (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n)) A (F0 L ω₀ (Fin 4 × n)) ∈ Th (stdH L _) β A :=
    ⟨analytic_inter _ _ _ _ hF.1, inter_mem_fixedBy hH hs S.selfDual S.betaSemi hF.2⟩
  set K := inter (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n)) A (F0 L ω₀ (Fin 4 × n)) with hKdef
  have hk : kernel4 L ω₀ Λ β g = fun z => K (g z) := rfl
  have hK0 : K ≠ 0 := by
    intro h0
    have h1 := inter_inter hH hd S.selfDual hs hF.2
    rw [← hKdef, h0, ← zero_smul ℂ (0 : (Fin 4 × n → ℂ) → ℂ), inter_smul, zero_smul] at h1
    have := congrFun h1 0
    rw [productEvenTheta_zero_eq_one L S.half] at this
    exact zero_ne_one this
  have hP : kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) := by
    rw [hk]
    refine ⟨fun z _ => (hK.1 _ trivial).comp
      ((LinearMap.toContinuousLinearMap (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))).analyticAt z),
      fun x hx z => ?_⟩
    have := hK.2 (g x) ⟨x, hx, rfl⟩ (g z)
    rw [opU, hiso, hiso, ← map_add, S.betaAlpha] at this
    exact this
  have hne : κ • kernel4 L ω₀ Λ β g ≠ 0 := by
    refine smul_ne_zero hκ fun h0 => hK0 (funext fun z => ?_)
    simpa [hk] using congrFun h0 (g.symm z)
  have hline : ∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ),
      ∃ c : ℂ, G = c • κ • kernel4 L ω₀ Λ β g := by
    intro G hG
    have hG' : (fun z => G (g.symm z)) ∈ Th (stdH L _) β A := by
      refine ⟨fun z _ => (hG.1 _ trivial).comp
        ((LinearMap.toContinuousLinearMap (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))).analyticAt z), ?_⟩
      rintro _ ⟨x, hx, rfl⟩ z
      obtain ⟨y, rfl⟩ := g.surjective z
      change β (g x) * opU _ (g x) _ (g y) = G (g.symm (g y))
      rw [opU, hiso, hiso, ← map_add, S.betaAlpha, g.symm_apply_apply, g.symm_apply_apply]
      exact hG.2 x hx y
    have h1 := std_line L S.half S.betaStd
      (differentiableOn_univ.1 (analytic_inter (stdH L _) β A (stdLat L _) hG'.1).differentiableOn)
      (inter_mem_fixedBy hH S.betaSemi hd hs hG'.2)
    have h2 := inter_inter hH S.selfDual hd S.betaSemi hG'.2
    rw [h1, inter_smul, ← hKdef] at h2
    generalize inter (stdH L (Fin 4 × n)) β A (stdLat L _) (fun z => G (g.symm z)) 0 = c at h2
    refine ⟨c * κ⁻¹, funext fun z => ?_⟩
    have := congrFun h2 (g z)
    rw [g.symm_apply_apply] at this
    rw [← this, smul_smul, inv_mul_cancel_right₀ hκ, hk]
    rfl
  obtain ⟨e, u⟩ := fourthRoot n h Λ α S.alpha0 _ (Submodule.smul_mem _ κ hP) hne hline
  refine ⟨e, fun θ hθ h4 => ⟨?_, u θ hθ h4⟩⟩
  rintro rfl
  apply hne
  rw [← h4]
  funext z
  simp [tens4]

end Four

end GlobalTheory.Mem.Col2.ThetaVec
