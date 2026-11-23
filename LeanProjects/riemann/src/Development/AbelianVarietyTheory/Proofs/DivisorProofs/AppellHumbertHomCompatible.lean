import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LamPullFrame

open GlobalTheory.ProdUnifSq

variable {g : ℕ}

def hf (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

theorem hf_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) : hf Hm (z + z') w = hf Hm z w + hf Hm z' w :=
  add_dotProduct _ _ _

theorem hf_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) : hf Hm z (w + w') = hf Hm z w + hf Hm z w' := by
  simp only [hf, star_add, Matrix.mulVec_add, dotProduct_add]

def sumL (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  (if (0 : Fin 2) ∈ I.down then (halfL g).toLinearMap else 0) +
    (if (1 : Fin 2) ∈ I.down then (halfR g).toLinearMap else 0)

theorem prod_four {Mo : Type} [CommMonoid Mo] (F : ULift.{0} (Finset (Fin 2)) → Mo) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift.{0, 0} (α := Finset (Fin 2))).symm.prod_comp]
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  rw [← _root_.mul_assoc, ← _root_.mul_assoc]
  rfl

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem padd_eq {T : Over (Sp ℂ)} (a b : T ⟶ A) : padd A a b = a * b := (Hom.mul_def a b).symm

theorem pzero_eq (T : Over (Sp ℂ)) : pzero A T = 1 := by
  rw [pzero, Hom.one_def]

theorem ex_zero {M : LB A.left} (u : HolUnif A M g) : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)

theorem ex_sumL {M₀ M : LB A.left} (u₀ : HolUnif A M₀ g) (u : HolUnif A M g) (hex : u.ex = u₀.ex)
    (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex (sumL g I v) = (sqUnif A u₀).ex v ≫ psum A (x2 A) I.down := by
  have e : (sqUnif A u₀).ex v = lift (u₀.ex (halfL g v)) (u₀.ex (halfR g v)) := rfl
  rw [e, hex]
  obtain ⟨I⟩ := I
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl
  · simp [sumL, psum, pzero_eq, ex_zero]
  · simp [sumL, psum, padd_eq, pzero_eq, x2, List.finRange_succ]
  · simp [sumL, psum, padd_eq, pzero_eq, x2, List.finRange_succ]
  · simp [sumL, psum, padd_eq, pzero_eq, x2, List.finRange_succ, u₀.ex_add, MonObj.comp_mul]

end GlobalTheory.LamPullFrame

namespace GlobalTheory.LamPullFrame

open GlobalTheory.ProdUnifSq

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

def lamUnif {M₀ M : LB A.left} (u₀ : HolUnif A M₀ g) (u : HolUnif A M g) (hex : u.ex = u₀.ex) :
    HolUnif (A ⊗ A) (abelian₂ A M) (g + g) :=
  GlobalTheory.linCombUnif (sqUnif A u₀) u (fun I : ULift.{0} (Finset (Fin 2)) => psum A (x2 A) I.down) (sumL g)
    (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_sumL u₀ u hex I v)

theorem lamUnif_fr {M₀ M : LB A.left} (u₀ : HolUnif A M₀ g) (u : HolUnif A M g) (hex : u.ex = u₀.ex)
    (j : (abelian₂ A M).ι) (v : Fin (g + g) → ℂ) :
    (lamUnif u₀ u hex).fr j v = ∏ I, u.fr (j I) (sumL g I v) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := rfl

theorem lamUnif_ex {M₀ M : LB A.left} (u₀ : HolUnif A M₀ g) (u : HolUnif A M g) (hex : u.ex = u₀.ex) :
    (lamUnif u₀ u hex).ex = (sqUnif A u₀).ex := rfl

theorem lam_chart {M₀ M : LB A.left} (u₀ : HolUnif A M₀ g) (u : HolUnif A M g) (hex : u.ex = u₀.ex)
    (j : (abelian₂ A M).ι) (v : Fin (g + g) → ℂ) (hv : ⊤ ≤ ((sqUnif A u₀).ex v).left ⁻¹ᵁ (abelian₂ A M).U j)
    (I : ULift.{0} (Finset (Fin 2))) : ⊤ ≤ (u.ex (sumL g I v)).left ⁻¹ᵁ M.U (j I) := by
  have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u₀).ex v).left M
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) j).1 hv I
  rw [ex_sumL u₀ u hex I v, Over.comp_left]
  exact h

omit [IsCommMonObj A] in
theorem ex_add_mem {M : LB A.left} (u : HolUnif A M g) (z : Fin g → ℂ) {w : Fin g → ℂ} (hw : w ∈ u.Λ) :
    u.ex (z + w) = u.ex z := by
  rw [u.ex_add, (u.ker w).2 hw, _root_.mul_one]

omit [IsCommMonObj A] in
theorem exists_chart_pt' {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := by
    haveI := q.isPrime
    haveI := p0.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime p0.asIdeal).symm)
  rw [this]
  exact hj

open Classical in

def chi {M : LB A.left} (u : HolUnif A M g) (χ : u.Λ → ℂ) (z : Fin g → ℂ) : ℂ :=
  if h : z ∈ u.Λ then χ ⟨z, h⟩ else 0

omit [IsCommMonObj A] in

theorem semichar {M : LB A.left} (hM : M.IsLB) (u : HolUnif A M g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} (hF : IsFactorAH u Hm χ) {l m : Fin g → ℂ} (hl : l ∈ u.Λ) (hm : m ∈ u.Λ) :
    chi u χ (l + m) * Complex.exp ((Real.pi : ℂ) / 2 * (hf Hm l m + hf Hm m l)) =
      chi u χ l * chi u χ m * Complex.exp ((Real.pi : ℂ) * hf Hm l m) := by
  obtain ⟨i, hi⟩ := exists_chart_pt' M hM (u.ex 0).left
  have hz : ∀ z ∈ u.Λ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i := by
    intro z hz
    rw [(u.ker z).2 hz, ← (u.ker 0).2 (zero_mem _)]
    exact hi
  have law1 := hF.2.2 ⟨l, hl⟩ i 0 (hz 0 (zero_mem _))
  have law2 := hF.2.2 ⟨m, hm⟩ i l (hz l hl)
  have law3 := hF.2.2 ⟨l + m, add_mem hl hm⟩ i 0 (hz 0 (zero_mem _))
  have hF0 := u.fr_ne i (l + m) (hz _ (add_mem hl hm))
  simp only [zero_dotProduct, mul_zero, zero_add] at law1 law3
  have hlm : (l + m) ⬝ᵥ Hm.mulVec (star (l + m)) = hf Hm l l + hf Hm l m + hf Hm m l + hf Hm m m := by
    change hf Hm (l + m) (l + m) = _
    rw [hf_add_left, hf_add_right, hf_add_right]
    ring
  rw [hlm] at law3
  change u.fr i 0 = χ ⟨l, hl⟩ * Complex.exp (↑Real.pi / 2 * hf Hm l l) * u.fr i l at law1
  change u.fr i l = χ ⟨m, hm⟩ * Complex.exp (↑Real.pi * hf Hm l m + ↑Real.pi / 2 * hf Hm m m) * u.fr i (l + m) at law2
  rw [chi, dif_pos (add_mem hl hm), chi, dif_pos hl, chi, dif_pos hm]
  set a := hf Hm l l
  set b := hf Hm l m
  set c := hf Hm m l
  set d := hf Hm m m
  have ex1 : Complex.exp (↑Real.pi / 2 * (b + c)) * Complex.exp (↑Real.pi / 2 * (a + d)) =
      Complex.exp (↑Real.pi / 2 * (a + b + c + d)) := by
    rw [← Complex.exp_add]; ring_nf
  have ex2 : Complex.exp (↑Real.pi * b) * Complex.exp (↑Real.pi / 2 * (a + d)) =
      Complex.exp (↑Real.pi / 2 * a) * Complex.exp (↑Real.pi * b + ↑Real.pi / 2 * d) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  refine mul_right_cancel₀ (mul_ne_zero (Complex.exp_ne_zero (↑Real.pi / 2 * (a + d))) hF0) ?_
  linear_combination (χ ⟨l + m, add_mem hl hm⟩ * u.fr i (l + m)) * ex1 -
    (χ ⟨l, hl⟩ * χ ⟨m, hm⟩ * u.fr i (l + m)) * ex2 - law3 + law1 +
    χ ⟨l, hl⟩ * Complex.exp (↑Real.pi / 2 * a) * law2

end GlobalTheory.LamPullFrame

namespace GlobalTheory.LamPullFrame

open GlobalTheory.ProdUnifSq

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem sumL_empty (v : Fin (g + g) → ℂ) : sumL g ⟨∅⟩ v = 0 := by simp [sumL]
theorem sumL_zero (v : Fin (g + g) → ℂ) : sumL g ⟨{0}⟩ v = halfL g v := by simp [sumL]
theorem sumL_one (v : Fin (g + g) → ℂ) : sumL g ⟨{1}⟩ v = halfR g v := by simp [sumL]
theorem sumL_both (v : Fin (g + g) → ℂ) : sumL g ⟨{0, 1}⟩ v = halfL g v + halfR g v := by simp [sumL]

omit [IsCommMonObj A] in
theorem mem_iff {M₀ M : LB A.left} (u₀ : HolUnif A M₀ g) (u : HolUnif A M g) (hex : u.ex = u₀.ex)
    (z : Fin g → ℂ) : z ∈ u.Λ ↔ z ∈ u₀.Λ := by
  rw [← u.ker, ← u₀.ker, hex]

omit [IsCommMonObj A] in
theorem sumL_mem {M₀ M : LB A.left} (u₀ : HolUnif A M₀ g) (u : HolUnif A M g) (hex : u.ex = u₀.ex)
    (I : ULift.{0} (Finset (Fin 2))) {w : Fin (g + g) → ℂ} (hw : w ∈ sqLat u₀.Λ) : sumL g I w ∈ u.Λ := by
  rw [mem_iff u₀ u hex]
  obtain ⟨hl, hr⟩ := (mem_sqLat _ _).1 hw
  simp only [sumL, LinearMap.add_apply]
  refine add_mem ?_ ?_ <;> split_ifs <;> simp [hl, hr]

omit [IsCommMonObj A] in
theorem chi_ne {M : LB A.left} (u : HolUnif A M g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hF : IsFactorAH u Hm χ) {z : Fin g → ℂ} (hz : z ∈ u.Λ) : chi u χ z ≠ 0 := by
  rw [chi, dif_pos hz]
  intro h0
  have := hF.2.1 ⟨z, hz⟩
  rw [h0, norm_zero] at this
  exact zero_ne_one this

omit [IsCommMonObj A] in
theorem key_exp {M : LB A.left} (hM : M.IsLB) (u : HolUnif A M g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} (hF : IsFactorAH u Hm χ) {l m : Fin g → ℂ} (hl : l ∈ u.Λ) (hm : m ∈ u.Λ) (x y : Fin g → ℂ) :
    chi u χ (l + m) * Complex.exp (↑Real.pi * hf Hm (x + y) (l + m) + ↑Real.pi / 2 * hf Hm (l + m) (l + m)) =
      Complex.exp (↑Real.pi * (hf Hm x m + hf Hm y l + hf Hm l m)) *
        (chi u χ l * Complex.exp (↑Real.pi * hf Hm x l + ↑Real.pi / 2 * hf Hm l l)) *
        (chi u χ m * Complex.exp (↑Real.pi * hf Hm y m + ↑Real.pi / 2 * hf Hm m m)) := by
  have sc := semichar hM u hF hl hm
  have e1 : ↑Real.pi * hf Hm (x + y) (l + m) + ↑Real.pi / 2 * hf Hm (l + m) (l + m) =
      ↑Real.pi / 2 * (hf Hm l m + hf Hm m l) +
        (↑Real.pi * (hf Hm x l + hf Hm x m + hf Hm y l + hf Hm y m) +
          ↑Real.pi / 2 * (hf Hm l l + hf Hm m m)) := by
    simp only [hf_add_left, hf_add_right]; ring
  have e2 : Complex.exp (↑Real.pi * (hf Hm x m + hf Hm y l + hf Hm l m)) *
      Complex.exp (↑Real.pi * hf Hm x l + ↑Real.pi / 2 * hf Hm l l) *
      Complex.exp (↑Real.pi * hf Hm y m + ↑Real.pi / 2 * hf Hm m m) =
      Complex.exp (↑Real.pi * hf Hm l m) *
        Complex.exp (↑Real.pi * (hf Hm x l + hf Hm x m + hf Hm y l + hf Hm y m) +
          ↑Real.pi / 2 * (hf Hm l l + hf Hm m m)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [e1, Complex.exp_add]
  linear_combination (Complex.exp (↑Real.pi * (hf Hm x l + hf Hm x m + hf Hm y l + hf Hm y m) +
      ↑Real.pi / 2 * (hf Hm l l + hf Hm m m))) * sc - chi u χ l * chi u χ m * e2

theorem lam_factor {M₀ M : LB A.left} (hM : M.IsLB) (u₀ : HolUnif A M₀ g) (u : HolUnif A M g)
    (hex : u.ex = u₀.ex) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hF : IsFactorAH u Hm χ)
    (j : (abelian₂ A M).ι) (v w : Fin (g + g) → ℂ) (hw : w ∈ sqLat u₀.Λ)
    (hv : ⊤ ≤ ((sqUnif A u₀).ex v).left ⁻¹ᵁ (abelian₂ A M).U j) :
    (lamUnif u₀ u hex).fr j v = Complex.exp ((Real.pi : ℂ) * (hf Hm (halfL g v) (halfR g w) +
      hf Hm (halfR g v) (halfL g w) + hf Hm (halfL g w) (halfR g w))) * (lamUnif u₀ u hex).fr j (v + w) := by
  have law : ∀ I, u.fr (j I) (sumL g I v) = chi u χ (sumL g I w) *
      Complex.exp (↑Real.pi * hf Hm (sumL g I v) (sumL g I w) +
        ↑Real.pi / 2 * hf Hm (sumL g I w) (sumL g I w)) * u.fr (j I) (sumL g I (v + w)) := by
    intro I
    rw [chi, dif_pos (sumL_mem u₀ u hex I hw), map_add]
    exact hF.2.2 ⟨_, sumL_mem u₀ u hex I hw⟩ (j I) _ (lam_chart u₀ u hex j v hv I)
  have hne : ∀ I, u.fr (j I) (sumL g I (v + w)) ≠ 0 := by
    intro I
    refine u.fr_ne _ _ ?_
    rw [map_add, ex_add_mem u _ (sumL_mem u₀ u hex I hw)]
    exact lam_chart u₀ u hex j v hv I
  obtain ⟨hl, hr⟩ := (mem_sqLat _ _).1 hw
  have hl' := (mem_iff u₀ u hex _).2 hl
  have hr' := (mem_iff u₀ u hex _).2 hr
  have k := key_exp hM u hF hl' hr' (halfL g v) (halfR g v)
  have l1 := law ⟨{0}⟩
  have l2 := law ⟨{1}⟩
  have l3 := law ⟨{0, 1}⟩
  have n1 := hne ⟨{0}⟩
  have n2 := hne ⟨{1}⟩
  have c1 := chi_ne u hF hl'
  have c2 := chi_ne u hF hr'
  simp only [sumL_zero, sumL_one, sumL_both] at l1 l2 l3 n1 n2
  rw [lamUnif_fr, lamUnif_fr, prod_four, prod_four]
  have d0 : ((-1 : ℤ) ^ (2 - (⟨∅⟩ : ULift.{0} (Finset (Fin 2))).down.card)) = 1 := by decide
  have d1 : ((-1 : ℤ) ^ (2 - (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))).down.card)) = -1 := by decide
  have d2 : ((-1 : ℤ) ^ (2 - (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))).down.card)) = -1 := by decide
  have d3 : ((-1 : ℤ) ^ (2 - (⟨{0, 1}⟩ : ULift.{0} (Finset (Fin 2))).down.card)) = 1 := by decide
  rw [d0, d1, d2, d3]
  simp only [zpow_one, zpow_neg_one, sumL_empty, sumL_zero, sumL_one, sumL_both]
  rw [l1, l2, l3, k]
  have e1 := Complex.exp_ne_zero (↑Real.pi * hf Hm (halfL g v) (halfL g w) + ↑Real.pi / 2 * hf Hm (halfL g w) (halfL g w))
  have e2 := Complex.exp_ne_zero (↑Real.pi * hf Hm (halfR g v) (halfR g w) + ↑Real.pi / 2 * hf Hm (halfR g w) (halfR g w))
  field_simp

end GlobalTheory.LamPullFrame

namespace GlobalTheory.LamPullFrame

open GlobalTheory.ProdUnifSq

variable {g : ℕ}

def twistMap (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun v := Fin.append (halfL g v) (Fl (halfR g v))
  map_add' v w := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_add, Pi.add_apply]
  map_smul' c v := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem halfL_twist (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfL g (twistMap Fl v) = halfL g v := halfL_append _ _

theorem halfR_twist (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfR g (twistMap Fl v) = Fl (halfR g v) := halfR_append _ _

end GlobalTheory.LamPullFrame

open GlobalTheory.LamPullFrame GlobalTheory.ProdUnifSq in

theorem GlobalTheory.TorusRM.lbIso_lam_pull_of_selfAdjoint : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M₁ M₂ : LB A.left) (u₁ : HolUnif A M₁ g) (u₂ : HolUnif A M₂ g) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
      (χ₁ : u₁.Λ → ℂ) (χ₂ : u₂.Λ → ℂ) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    M₁.IsLB → M₂.IsLB → u₂.ex = u₁.ex → IsFactorAH u₁ H₁ χ₁ → IsFactorAH u₂ H₂ χ₂ → IsMonHom f →
    (∀ z, u₁.ex (Fl z) = u₁.ex z ≫ f) →
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (Fl w))) →
    (∀ z w, Fl z ⬝ᵥ H₁.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (Fl w))) →
    LBIso (abelian₂ A M₂) ((abelian₂ A M₁).pull (lift (fst A A) (snd A A ≫ f)).left) := by
  intro g A _ hA hp M₁ M₂ u₁ u₂ H₁ H₂ χ₁ χ₂ f Fl hM₁ hM₂ hex hF₁ hF₂ hfm hFl hH hsa
  haveI : IsCommMonObj A := hA.comm
  haveI : IsMonHom f := hfm
  have hFm : ∀ v, (lamUnif u₁ u₁ rfl).ex (twistMap Fl v) =
      (sqUnif A u₁).ex v ≫ lift (fst A A) (snd A A ≫ f) := by
    intro v
    change lift (u₁.ex (halfL g (twistMap Fl v))) (u₁.ex (halfR g (twistMap Fl v))) =
      lift (u₁.ex (halfL g v)) (u₁.ex (halfR g v)) ≫ lift (fst A A) (snd A A ≫ f)
    rw [halfL_twist, halfR_twist, hFl, comp_lift, lift_fst, lift_snd_assoc]
  let UP := GlobalTheory.linCombUnif (sqUnif A u₁) (lamUnif u₁ u₁ rfl) (fun _ : PUnit => lift (fst A A) (snd A A ≫ f))
    (fun _ => twistMap Fl) (fun _ => 1) (fun _ v => hFm v)
  let UN := GlobalTheory.SameFactor.divUnif (lamUnif u₁ u₂ hex) UP rfl
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
    (GlobalTheory.ProjSpace.isProjOver_pullback hp hp) _
    (LB.isLB_div (LB.isLB_linComb (LB.isLB_linComb hM₁ _ _) _ _) (LB.isLB_linComb hM₂ _ _)) (g + g) UN
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro w hw p z hz
  obtain ⟨hz1, hz2⟩ := (top_le_preimage_inf _ _ _).1 hz
  have hw' : w ∈ sqLat u₁.Λ := hw
  obtain ⟨hl, hr⟩ := (mem_sqLat _ _).1 hw'
  have hwt : twistMap Fl w ∈ sqLat u₁.Λ := by
    refine (mem_sqLat _ _).2 ⟨by rw [halfL_twist]; exact hl, ?_⟩
    rw [halfR_twist, ← u₁.ker, hFl, (u₁.ker _).2 hr, MonObj.one_comp]
  have hc1 : ⊤ ≤ ((sqUnif A u₁).ex (twistMap Fl z)).left ⁻¹ᵁ (abelian₂ A M₁).U (p.1 PUnit.unit) := by
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u₁).ex z).left (abelian₂ A M₁)
      (fun _ : PUnit => (lift (fst A A) (snd A A ≫ f)).left) p.1).1 hz1 PUnit.unit
    rw [← Over.comp_left, ← hFm] at h
    exact h
  have fac1 := lam_factor hM₁ u₁ u₁ rfl hF₁ (p.1 PUnit.unit) (twistMap Fl z) (twistMap Fl w) hwt hc1
  have fac2 := lam_factor hM₂ u₁ u₂ hex hF₂ p.2 z w hw' hz2
  rw [halfL_twist, halfL_twist, halfR_twist, halfR_twist, ← map_add] at fac1
  have hE : (hf H₁ (halfL g z) (Fl (halfR g w)) + hf H₁ (Fl (halfR g z)) (halfL g w) +
      hf H₁ (halfL g w) (Fl (halfR g w))) =
      hf H₂ (halfL g z) (halfR g w) + hf H₂ (halfR g z) (halfL g w) + hf H₂ (halfL g w) (halfR g w) := by
    have e1 := hH (halfL g z) (halfR g w)
    have e2 := hH (halfR g z) (halfL g w)
    have e3 := hH (halfL g w) (halfR g w)
    have e4 := hsa (halfR g z) (halfL g w)
    simp only [hf]
    rw [e1, e2, e3, e4]
  rw [hE] at fac1
  have hz2' : ⊤ ≤ ((sqUnif A u₁).ex (z + w)).left ⁻¹ᵁ (abelian₂ A M₂).U p.2 := by
    rw [ex_add_mem _ _ hw']; exact hz2
  have n2 := (lamUnif u₁ u₂ hex).fr_ne p.2 (z + w) hz2'
  have hPf : ∀ v, UP.fr p.1 v = (lamUnif u₁ u₁ rfl).fr (p.1 PUnit.unit) (twistMap Fl v) := fun v => by
    show (∏ k : PUnit, (lamUnif u₁ u₁ rfl).fr (p.1 k) (twistMap Fl v) ^ (1 : ℤ)) = _
    simp
  change 1 * (UP.fr p.1 (z + w) * ((lamUnif u₁ u₂ hex).fr p.2 (z + w))⁻¹) =
    1 * (UP.fr p.1 z * ((lamUnif u₁ u₂ hex).fr p.2 z)⁻¹)
  rw [hPf, hPf, fac1, fac2]
  have ne := Complex.exp_ne_zero (↑Real.pi * (hf H₂ (halfL g z) (halfR g w) + hf H₂ (halfR g z) (halfL g w) +
    hf H₂ (halfL g w) (halfR g w)))
  field_simp
