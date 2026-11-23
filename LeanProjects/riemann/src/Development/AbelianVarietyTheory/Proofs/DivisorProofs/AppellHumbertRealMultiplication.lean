import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosatiAH

open GlobalTheory.PullHermitian in

theorem hermForm_pull_eq_of_lbIso_pow_factor :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), IsFactorAH u Hm χ → IsFactorAH u' Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∀ m n : ℕ, LBIso (lbPow (L'.pull f.left) m) (lbPow L n) →
  ∀ z w, (m : ℂ) * hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF m n ⟨w, hw⟩
  have hFl : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by
    rw [hF, Over.comp_left]
  have hΛ : ∀ l : u.Λ, F l ∈ u'.Λ := fun l => by
    rw [← u'.ker, hF, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hF, map_zero]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun p : L.ι × L'.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩
      F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
    (fun p => (u.hol _ 0).1.inter ((u'.hol _ 0).1.preimage hFd.continuous))
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
      exact ⟨(i, j), hi, hj⟩)
    (fun p z => valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val *
      u'.fr p.2 (F z) ^ m / u.fr p.1 z ^ n)
    (fun p => by
      have d1 := (u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2.mono
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        fun z hz => idx_chart _ _ _ _ _ _ hz.1 (hFl z ▸ hz.2)
      have d2 := (u'.fr_hol p.2).comp
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        hFd.differentiableOn fun z hz => hz.2
      have d3 := (u.fr_hol p.1).mono
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        Set.inter_subset_left
      simp only [div_eq_mul_inv]
      exact (d1.mul (d2.pow m)).mul
        ((d3.pow n).inv fun z hz => pow_ne_zero n (u.fr_ne p.1 z hz.1)))
    (fun p q z hp hq => by
      have h := val_iso_pow (u.ex z).left f.left m n w hw p.1 q.1 p.2 q.2 hp.1 hq.1
        (hFl z ▸ hp.2) (hFl z ▸ hq.2)
      have h1 := u.fr_compat p.1 q.1 z (inf_of _ hp.1 hq.1)
      have h2 := u'.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)
      rw [hFl] at h2
      rw [div_eq_div_iff (pow_ne_zero _ (u.fr_ne _ _ hp.1)) (pow_ne_zero _ (u.fr_ne _ _ hq.1)),
        h1, h2, mul_pow, mul_pow, ← _root_.mul_assoc, h]
      ring)
  set H₂ := (LinearMap.toMatrix' F).transpose * Hm' * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu'.1
  have hchart : ∀ z, ∃ i j, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j :=
    fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
      exact ⟨i, j, hi, hj⟩
  haveI := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    ((n : ℂ) • Hm - (m : ℂ) • H₂) (fun l => χ l ^ n / χ' ⟨F l, hΛ l⟩ ^ m) r
    ((hu.1.smul (by simp [IsSelfAdjoint])).sub (hH₂h.smul (by simp [IsSelfAdjoint])))
    (fun l => by simp [hu.2.1, hu'.2.1]) hr
    (fun z => by
      obtain ⟨i, j, hi, hj⟩ := hchart z
      rw [hrφ (i, j) z ⟨hi, hj⟩, valAt'_eq_unitVal _ (idx_chart _ _ _ _ _ _ hi (hFl z ▸ hj))]
      exact div_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne _ _ hj)))
        (pow_ne_zero _ (u.fr_ne _ _ hi)))
    (fun l z => by
      obtain ⟨i, j, hi, hj⟩ := hchart z
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have hj' : ⊤ ≤ (u'.ex (F (z + l))).left ⁻¹ᵁ L'.U j := by rwa [hF, hper, ← hF]
      have h1 := hu.2.2 l i z hi
      have h2 := hu'.2.2 ⟨F l, hΛ l⟩ j (F z) hj
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.1]; exact one_ne_zero)
      have h4 : χ' ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu'.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ (i, j) z ⟨hi, hj⟩, hrφ (i, j) (z + l) ⟨hi', hj'⟩]
      simp only [hper, hermForm_sub_smul, hH₂, hermForm_pull, map_add]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ Hm'.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ Hm'.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (n * a - m * a') + Real.pi / 2 * (n * b - m * b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ n /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') ^ m := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      simp only [mul_pow]
      field_simp)
  intro z v
  have h := hermForm_sub_smul Hm H₂ n m z v
  rw [key.1, hH₂, hermForm_pull] at h
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at h
  exact (sub_eq_zero.1 h.symm).symm

theorem hermForm_eq_of_lbIso_pull :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), IsFactorAH u Hm χ → IsFactorAH u' Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  LBIso L (L'.pull f.left) → ∀ z w, hermForm Hm z w = hermForm Hm' (F z) (F w) := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF hiso z w
  have hP : (L'.pull f.left).IsLB := LB.isLB_pull hL' _
  have i1 : LBIso (lbPow (L'.pull f.left) 1) (lbPow L 1) :=
    ((GlobalTheory.lbIso_lbPow_one hP).trans (GlobalTheory.isLB_lbPow hP 1) hP hL (LBIso.symm hiso)).trans
      (GlobalTheory.isLB_lbPow hP 1) hL (GlobalTheory.isLB_lbPow hL 1) (LBIso.symm (GlobalTheory.lbIso_lbPow_one hL))
  have := hermForm_pull_eq_of_lbIso_pow_factor A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF 1 1 i1 z w
  simpa using this.symm

end GlobalTheory.RosatiAH

namespace GlobalTheory.RosatiAH

open GlobalTheory.AppellHumbertTrivial

variable {g : ℕ}

theorem append_split (x y : Fin g → ℂ) : Fin.append x y = Fin.append x 0 + Fin.append 0 y := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, Pi.add_apply, Pi.zero_apply, add_zero]
  · simp only [Fin.append_right, Pi.add_apply, Pi.zero_apply, zero_add]

theorem herm_append (H : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (x y x' y' : Fin g → ℂ) :
    hermForm H (Fin.append x y) (Fin.append x' y') =
      hermForm H (Fin.append x 0) (Fin.append x' 0) + hermForm H (Fin.append x 0) (Fin.append 0 y') +
        hermForm H (Fin.append 0 y) (Fin.append x' 0) + hermForm H (Fin.append 0 y) (Fin.append 0 y') := by
  rw [append_split x y, append_split x' y', hermForm_add_left, hermForm_add_right, hermForm_add_right]
  ring

theorem append_smul (t : ℂ) (x y : Fin g → ℂ) : Fin.append (t • x) (t • y) = t • Fin.append x y := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, Pi.smul_apply]
  · simp only [Fin.append_right, Pi.smul_apply]

theorem rosati_alg (Hm : Matrix (Fin g) (Fin g) ℂ) (Hc Hd H2 : Matrix (Fin (g + g)) (Fin (g + g)) ℂ)
    (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hD : ∀ z w, hermForm Hm z w = hermForm Hc (Fin.append z z) (Fin.append w w))
    (hSc : ∀ x y x' y', hermForm Hc (Fin.append x y) (Fin.append x' y') = hermForm Hc (Fin.append y x) (Fin.append y' x'))
    (hSd : ∀ x y x' y', hermForm Hd (Fin.append x y) (Fin.append x' y') = hermForm Hd (Fin.append y x) (Fin.append y' x'))
    (hMd : ∀ x y x' y', hermForm Hd (Fin.append x y) (Fin.append x' y') =
      hermForm Hc (Fin.append x (D y)) (Fin.append x' (D y')))
    (hS2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') = hermForm H2 (Fin.append y x) (Fin.append y' x'))
    (hM2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') =
      hermForm Hc (Fin.append x ((2 : ℂ) • y)) (Fin.append x' ((2 : ℂ) • y'))) :
    ∀ z w, hermForm Hm (D z) w = hermForm Hm z (D w) := by

  have hA : ∀ x x', hermForm Hc (Fin.append x 0) (Fin.append x' 0) = 0 := by
    intro x x'
    have e1 := hM2 x 0 x' 0
    have e2 := hS2 x 0 x' 0
    have e3 := hM2 0 x 0 x'
    have e4 := hSc x 0 x' 0
    simp only [smul_zero] at e1
    have e5 : Fin.append (0 : Fin g → ℂ) ((2 : ℂ) • x) = (2 : ℂ) • Fin.append 0 x := by
      rw [← append_smul, smul_zero]
    have e6 : Fin.append (0 : Fin g → ℂ) ((2 : ℂ) • x') = (2 : ℂ) • Fin.append 0 x' := by
      rw [← append_smul, smul_zero]
    rw [e5, e6, hermForm_smul_left, hermForm_smul_right] at e3
    have hs : (star (2 : ℂ)) = 2 := by simp
    rw [hs] at e3

    have : hermForm Hc (Fin.append x 0) (Fin.append x' 0) =
        4 * hermForm Hc (Fin.append x 0) (Fin.append x' 0) := by
      calc _ = hermForm H2 (Fin.append x 0) (Fin.append x' 0) := e1.symm
        _ = hermForm H2 (Fin.append 0 x) (Fin.append 0 x') := e2
        _ = 2 * (2 * hermForm Hc (Fin.append 0 x) (Fin.append 0 x')) := e3
        _ = 4 * hermForm Hc (Fin.append x 0) (Fin.append x' 0) := by rw [e4]; ring
    linear_combination (-1/3 : ℂ) * this
  have hA2 : ∀ y y', hermForm Hc (Fin.append 0 y) (Fin.append 0 y') = 0 := by
    intro y y'
    rw [← hSc y 0 y' 0]
    exact hA y y'

  have hBC : ∀ x y', hermForm Hc (Fin.append 0 x) (Fin.append y' 0) = hermForm Hc (Fin.append x 0) (Fin.append 0 y') :=
    fun x y' => (hSc x 0 0 y').symm
  have hB : ∀ x y', hermForm Hc (Fin.append (D x) 0) (Fin.append 0 y') = hermForm Hc (Fin.append x 0) (Fin.append 0 (D y')) := by
    intro x y'
    have e1 := hMd x 0 0 y'
    have e2 := hSd x 0 0 y'
    have e3 := hMd 0 x y' 0
    rw [map_zero] at e1 e3
    rw [← hBC, ← e3, ← e2, e1]
  intro z w
  rw [hD, hD, herm_append Hc (D z) (D z) w w, herm_append Hc z z (D w) (D w)]
  simp only [hA, hA2, zero_add, add_zero, hBC, hB]

end GlobalTheory.RosatiAH

namespace GlobalTheory.RosatiAH

variable {g : ℕ}

def dmul (s : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z j := s j * z j
  map_add' z w := by funext j; simp [mul_add]
  map_smul' t z := by funext j; simp; ring

theorem dmul_apply (s z : Fin g → ℂ) : dmul s z = fun j => s j * z j := rfl

def fdiag (g : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun z := Fin.append z z
  map_add' z w := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply]
  map_smul' t z := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply, RingHom.id_apply]
    · simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]

def fmul (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun v := Fin.append (fun i => v (Fin.castAdd g i)) (D fun i => v (Fin.natAdd g i))
  map_add' v w := by
    have : (fun i => (v + w) (Fin.natAdd g i)) = (fun i => v (Fin.natAdd g i)) + fun i => w (Fin.natAdd g i) := rfl
    rw [this, map_add]
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply]
  map_smul' t v := by
    have : (fun i => (t • v) (Fin.natAdd g i)) = t • fun i => v (Fin.natAdd g i) := rfl
    rw [this, map_smul]
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply, RingHom.id_apply]
    · simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]

def fswap (g : ℕ) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun v := Fin.append (fun i => v (Fin.natAdd g i)) (fun i => v (Fin.castAdd g i))
  map_add' v w := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply]
  map_smul' t v := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply, RingHom.id_apply]
    · simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]

theorem fdiag_apply (z : Fin g → ℂ) : fdiag g z = Fin.append z z := rfl

theorem fmul_append (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (x y : Fin g → ℂ) :
    fmul D (Fin.append x y) = Fin.append x (D y) := by
  show Fin.append (fun i => Fin.append x y (Fin.castAdd g i)) (D fun i => Fin.append x y (Fin.natAdd g i)) = _
  simp only [Fin.append_left, Fin.append_right]

theorem fswap_append (x y : Fin g → ℂ) : fswap g (Fin.append x y) = Fin.append y x := by
  show Fin.append (fun i => Fin.append x y (Fin.natAdd g i)) (fun i => Fin.append x y (Fin.castAdd g i)) = _
  simp only [Fin.append_left, Fin.append_right]

theorem eq_append (v : Fin (g + g) → ℂ) :
    v = Fin.append (fun i => v (Fin.castAdd g i)) (fun i => v (Fin.natAdd g i)) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

end GlobalTheory.RosatiAH

open GlobalTheory.RosatiAH in

theorem GlobalTheory.RosatiAH.rosati_diag : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) → (F →+* ℂ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ e j (a : F) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    ∀ (a : 𝓞 F) i j, e i (a : F) * Hm i j = Hm i j * starRingEnd ℂ (e j (a : F)) := by
  intro F _ _ _ 𝔠 X c _ u e hu Hm χ hAH a i j
  obtain ⟨U0, hU0⟩ := GlobalTheory.T.product_abelian_uniformization X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have frame : ∀ c' : 𝔠.elt, ∃ (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F))
      (H : Matrix (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) ℂ)
      (χ : U.Λ → ℂ), (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) ∧ IsFactorAH U H χ := fun c' => by
    obtain ⟨U, H, χ', hex, hF⟩ := GlobalTheory.T.exists_appell_humbert_line_bundle (X.A ⊗ X.A) hAb2 _ _ U0 (X.P c') (X.isLB c')
    exact ⟨U, H, χ', fun x y => by rw [hex]; exact hU0 x y, hF⟩
  obtain ⟨Uc, Hc, χc, hexc, hFc⟩ := frame c
  obtain ⟨Ud, Hd, χd, hexd, hFd⟩ := frame (a • c)
  obtain ⟨U2, H2, χ2, hex2, hF2⟩ := frame ((2 : 𝓞 F) • c)

  have hswap : ∀ {c' : 𝔠.elt} (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F)),
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) →
      ∀ v, U.ex (fswap _ v) = U.ex v ≫ lift (snd X.A X.A) (fst X.A X.A) := by
    intro c' U hex v
    rw [eq_append v, fswap_append, hex, hex]
    simp
  have hmul : ∀ {c' c'' : 𝔠.elt} (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F))
      (U' : HolUnif (X.A ⊗ X.A) (X.P c'') (Module.finrank ℚ F + Module.finrank ℚ F)),
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) →
      (∀ x y, U'.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → ∀ (b : 𝓞 F) v,
      U'.ex (fmul (dmul fun j => e j (b : F)) v) = U.ex v ≫ lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b) := by
    intro c' c'' U U' hex hex' b v
    rw [eq_append v, fmul_append, hex, hex', dmul_apply, hu]
    simp
  have hdiag : ∀ z, Uc.ex (fdiag _ z) = u.ex z ≫ lift (𝟙 X.A) (𝟙 X.A) := by
    intro z
    rw [fdiag_apply, hexc]
    simp
  have hdLB : (X.diag c).IsLB := LB.isLB_pull (X.isLB c) _
  have hD := hermForm_eq_of_lbIso_pull X.A (X.A ⊗ X.A) (X.diag c) (X.P c) hdLB (X.isLB c) _ _ u Uc Hm χ Hc χc
    (isFactorAH_of_isAH hAH) hFc (lift (𝟙 X.A) (𝟙 X.A)) (fdiag _) hdiag (by unfold Obj.diag; exact GlobalTheory.lbIso_refl hdLB)
  have hS : ∀ {c' : 𝔠.elt} (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F)) H χ',
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → IsFactorAH U H χ' →
      ∀ x y x' y', hermForm H (Fin.append x y) (Fin.append x' y') = hermForm H (Fin.append y x) (Fin.append y' x') := by
    intro c' U H χ' hex hF x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P c') (X.P c') (X.isLB c') (X.isLB c') _ _ U U H χ' H χ'
      hF hF (lift (snd X.A X.A) (fst X.A X.A)) (fswap _) (hswap U hex) (X.symm c') (Fin.append x y) (Fin.append x' y')
    rwa [fswap_append, fswap_append] at this
  have hM : ∀ (b : 𝓞 F) {U : HolUnif (X.A ⊗ X.A) (X.P (b • c)) (Module.finrank ℚ F + Module.finrank ℚ F)} {H χ'},
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → IsFactorAH U H χ' →
      ∀ x y x' y', hermForm H (Fin.append x y) (Fin.append x' y') =
        hermForm Hc (Fin.append x (dmul (fun j => e j (b : F)) y)) (Fin.append x' (dmul (fun j => e j (b : F)) y')) := by
    intro b U H χ' hex hF x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P (b • c)) (X.P c) (X.isLB _) (X.isLB c) _ _ U Uc H χ'
      Hc χc hF hFc (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)) (fmul (dmul fun j => e j (b : F)))
      (hmul U Uc hex hexc b) (X.smul b c) (Fin.append x y) (Fin.append x' y')
    rwa [fmul_append, fmul_append] at this
  have h2F : (((2 : 𝓞 F)) : F) = 2 := by norm_cast
  have h2 : (dmul fun j => e j (((2 : 𝓞 F) : F))) = (2 : ℂ) • LinearMap.id := by
    refine LinearMap.ext fun z => funext fun k => ?_
    simp only [dmul_apply, h2F, map_ofNat, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  have key := rosati_alg Hm Hc Hd H2 (dmul fun j => e j (a : F)) hD (hS Uc Hc χc hexc hFc) (hS Ud Hd χd hexd hFd)
    (hM a hexd hFd) (hS U2 H2 χ2 hex2 hF2) (fun x y x' y' => by rw [hM 2 hex2 hF2, h2]; rfl)
    (Pi.single i 1) (Pi.single j 1)
  have e1 : (dmul fun j => e j (a : F)) (Pi.single i 1) = Pi.single i (e i (a : F)) := by
    funext k; by_cases hk : k = i <;> simp [dmul_apply, Pi.single_apply, hk]
  have e2 : (dmul fun j => e j (a : F)) (Pi.single j 1) = Pi.single j (e j (a : F)) := by
    funext k; by_cases hk : k = j <;> simp [dmul_apply, Pi.single_apply, hk]
  rw [e1, e2] at key
  simp only [hermForm] at key
  have s1 : star (Pi.single j (1:ℂ) : Fin (Module.finrank ℚ F) → ℂ) = Pi.single j 1 := by simp
  have s2 : star (Pi.single j (e j (a : F)) : Fin (Module.finrank ℚ F) → ℂ) = Pi.single j (star (e j (a : F))) := by simp
  rw [s1, s2, Matrix.mulVec_single, Matrix.mulVec_single, single_dotProduct, single_dotProduct] at key
  simpa using key
