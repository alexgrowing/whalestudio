import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BiRoot

open GlobalTheory.ProdUnifSq GlobalTheory.TorusRM

theorem ahFactor_trivial_of_theta : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) → (∀ l, ‖χ l‖ = 1) →
    (∀ (l : Λ) (z : Fin g → ℂ), θ (z + l) = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * θ z) →
    Hm = 0 ∧ ∀ l, χ l = 1 := by
  intro g Λ hΛ Hm χ θ hH hθ hθ0 hχ hfac

  have hint : ∀ w : Fin g → ℂ, ∀ l ∈ Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n := by
    intro w
    refine GlobalTheory.ThetaLiouville.im_form_mem_int g Λ hΛ Hm hH w (fun z => θ (z + w) * (θ z)⁻¹)
      ((hθ.comp (differentiable_id.add_const w)).mul (hθ.inv hθ0)) (fun z => mul_ne_zero (hθ0 _) (inv_ne_zero (hθ0 _))) ?_
    intro l hl z
    have e1 := hfac ⟨l, hl⟩ (z + w)
    have e2 := hfac ⟨l, hl⟩ z
    simp only at e1 e2 ⊢
    rw [show z + l + w = z + w + l by abel, e1, e2, add_dotProduct]
    have hE : Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star l) + w ⬝ᵥ Hm.mulVec (star l)) +
        Real.pi / 2 * (l ⬝ᵥ Hm.mulVec (star l))) =
        Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) *
          Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star l)) + Real.pi / 2 * (l ⬝ᵥ Hm.mulVec (star l))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hE]
    have n1 := hθ0 z
    have n2 : χ ⟨l, hl⟩ ≠ 0 := fun h => by have := hχ ⟨l, hl⟩; rw [h, norm_zero] at this; exact zero_ne_one this
    have n3 := Complex.exp_ne_zero (Real.pi * (z ⬝ᵥ Hm.mulVec (star l)) + Real.pi / 2 * (l ⬝ᵥ Hm.mulVec (star l)))
    field_simp

  have him : ∀ w : Fin g → ℂ, ∀ l ∈ Λ, (w ⬝ᵥ Hm.mulVec (star l)).im = 0 := by
    intro w l hl
    set a := (w ⬝ᵥ Hm.mulVec (star l)).im with ha
    have ht : (0 : ℝ) < 2 * (|a| + 1) := by positivity
    obtain ⟨n, hn⟩ := hint (((1 / (2 * (|a| + 1)) : ℝ) : ℂ) • w) l hl
    rw [smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul, ← ha] at hn
    have hlt : |(n : ℝ)| < 1 := by
      rw [← hn, abs_mul, abs_of_pos (by positivity), one_div, inv_mul_lt_iff₀ ht]
      linarith [abs_nonneg a]
    have hn0 : n = 0 := by
      have : |n| < 1 := by exact_mod_cast hlt
      exact Int.abs_lt_one_iff.1 this
    rw [hn0, Int.cast_zero] at hn
    have hne : (1 / (2 * (|a| + 1)) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.1 hn).resolve_left hne
  have hzero : ∀ w : Fin g → ℂ, ∀ l ∈ Λ, w ⬝ᵥ Hm.mulVec (star l) = 0 := by
    intro w l hl
    have h2 := him (Complex.I • w) l hl
    rw [smul_dotProduct, smul_eq_mul, Complex.I_mul_im] at h2
    exact Complex.ext h2 (him w l hl)

  have hHm : Hm = 0 := by
    ext k j
    let φ : (Fin g → ℂ) →ₗ[ℝ] ℂ :=
      { toFun := fun v => (Hm.mulVec (star v)) k
        map_add' := fun v v' => by simp [Matrix.mulVec_add]
        map_smul' := fun c v => by
          simp only [RingHom.id_apply]
          rw [show star (c • v) = c • star v by
            funext i; simp [Complex.real_smul, Complex.conj_ofReal]]
          rw [Matrix.mulVec_smul]; rfl }
    have hφ : ∀ v ∈ (Λ : Set (Fin g → ℂ)), φ v = 0 := by
      intro v hv
      have := hzero (Pi.single k 1) v hv
      simpa [φ, single_one_dotProduct] using this
    have hall : φ (Pi.single j 1) = 0 := by
      have hmem : Pi.single j (1 : ℂ) ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hΛ]; trivial
      exact LinearMap.eqOn_span' (f := φ) (g := 0) hφ hmem
    simpa [φ, Matrix.mulVec_single_one] using hall
  refine ⟨hHm, ?_⟩
  subst hHm
  have hper : ∀ (l : Λ) z, θ (z + l) = χ l * θ z := fun l z => by simpa using hfac l z
  have hnorm : ∀ l ∈ Λ, ∀ z, ‖θ (z + l)‖ = ‖θ z‖ := fun l hl z => by
    rw [hper ⟨l, hl⟩ z, norm_mul, hχ, _root_.one_mul]
  obtain ⟨s, b, hfin, hbΛ⟩ := GlobalTheory.ThetaLiouville.exists_basis_in Λ hΛ
  haveI : Fintype s := Fintype.ofFinite s
  have hspan : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hbΛ i
    | zero => exact Λ.zero_mem
    | add x y _ _ hx hy => exact Λ.add_mem hx hy
    | smul n x _ hx => exact Λ.toAddSubgroup.zsmul_mem hx n
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hθ.continuous.continuousOn
  have hbd : Bornology.IsBounded (Set.range θ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
      rw [ZSpan.fract_apply]; abel
    rw [hz, hnorm _ (hspan _ (ZSpan.floor b z).2)]
    exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b z))
  intro l
  have hc : θ (0 + l) = θ 0 := hθ.apply_eq_apply_of_bounded hbd _ _
  rw [hper l 0] at hc
  exact (mul_eq_right₀ (hθ0 0)).1 hc

theorem exists_theta_of_gen : ∀ (B : Over (Sp ℂ)) [GrpObj B] (N : LB B.left) (n : ℕ) (u : HolUnif B N n), N.IsLB →
    (∃ t : N.Gen, t.IsGen) → ∃ θ : (Fin n → ℂ) → ℂ, Differentiable ℂ θ ∧ (∀ z, θ z ≠ 0) ∧
      ∀ l ∈ u.Λ, ∀ (i : N.ι) (z : Fin n → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i →
        θ (z + l) * u.fr i (z + l) = θ z * u.fr i z := by
  intro B _ N n u hN ht
  obtain ⟨t, ht⟩ := ht
  have hch : ∀ z, ∃ j, ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U j := fun z => ahFactor_im_int_chart N hN (u.ex z).left
  choose J hJ using hch
  have hv : ∀ j j' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U j' →
      valAt' (u.ex z).left _ (t.s j).val / u.fr j z = valAt' (u.ex z).left _ (t.s j').val / u.fr j' z := by
    intro j j' z hj hj'
    exact TransFrame.gen_div_eq _ _ t ht j j' hj hj' _ _
      (u.fr_compat j j' z ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hj, hj'⟩)) (u.fr_ne _ z hj')
  refine ⟨fun z => valAt' (u.ex z).left _ (t.s (J z)).val / u.fr (J z) z, fun z => ?_, fun z => ?_,
    fun l hl i z hi => ?_⟩
  · obtain ⟨ho, hd⟩ := u.hol _ (t.s (J z)).val
    have hn := ho.mem_nhds (hJ z)
    have hq := (hd.differentiableAt hn).mul (((u.fr_hol (J z)).differentiableAt hn).inv (u.fr_ne _ z (hJ z)))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with y hy
    simp only [Pi.mul_apply, Pi.inv_apply, ← div_eq_mul_inv]
    exact hv (J y) (J z) y (hJ y) hy
  · exact div_ne_zero (TransFrame.unitValue_ne_zero _ _ (hJ z) _) (u.fr_ne _ z (hJ z))
  · have hzl : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ N.U i := by rw [hzl]; exact hi
    show valAt' (u.ex (z + l)).left _ (t.s (J (z + l))).val / u.fr (J (z + l)) (z + l) * u.fr i (z + l) =
      valAt' (u.ex z).left _ (t.s (J z)).val / u.fr (J z) z * u.fr i z
    rw [hv (J (z + l)) i (z + l) (hJ _) hi', hv (J z) i z (hJ z) hi, hzl]
    have n1 := u.fr_ne i (z + l) hi'
    have n2 := u.fr_ne i z hi
    field_simp

theorem exists_pull_isFactorAH : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ)
    (u : HolUnif A L g) (u' : HolUnif A' L' g') (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (Hm : Matrix (Fin g') (Fin g') ℂ) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ),
    IsFactorAH u' Hm χ → Hm'.IsHermitian → (∀ z l, F z ⬝ᵥ Hm.mulVec (star (F l)) = z ⬝ᵥ Hm'.mulVec (star l)) →
    (∀ z, u'.ex (F z) = u.ex z ≫ f) → (∀ l ∈ u.Λ, F l ∈ u'.Λ) →
    ∃ (v : HolUnif A (L'.pull f.left) g) (χ' : v.Λ → ℂ), v.ex = u.ex ∧ v.Λ = u.Λ ∧ IsFactorAH v Hm' χ' ∧
      ∀ (l : v.Λ) (h : F l ∈ u'.Λ), χ' l = χ ⟨F l, h⟩ := by
  intro A A' _ _ L L' g g' u u' f F Hm Hm' χ hF hH hid hex hlat
  let v : HolUnif A (L'.pull f.left) g :=
    GlobalTheory.linCombUnif u u' (fun _ : PUnit => f) (fun _ => F) (fun _ => 1) (fun _ z => hex z)
  refine ⟨v, fun l => χ ⟨F l, hlat l l.2⟩, rfl, rfl, ⟨hH, fun l => hF.2.1 _, fun l j z hz => ?_⟩, fun l h => rfl⟩
  have hl : (u'.ex (F z)).left = (u.ex z).left ≫ f.left := by rw [hex z]; rfl
  have hc : ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U (j PUnit.unit) := by
    rw [hl]
    exact (GlobalTheory.CubeValues.le_preimage_wchart (u.ex z).left L' (fun _ : PUnit => f.left) j).1 hz PUnit.unit
  have e := hF.2.2 ⟨F l, hlat l l.2⟩ (j PUnit.unit) (F z) hc
  show ∏ k : PUnit, u'.fr (j k) (F z) ^ (1 : ℤ) =
    _ * ∏ k : PUnit, u'.fr (j k) (F (z + l)) ^ (1 : ℤ)
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one, map_add]
  rw [e, hid, hid]

theorem dot_blocks : ∀ (g : ℕ) (Hm : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (z l : Fin (g + g) → ℂ),
    z ⬝ᵥ Hm.mulVec (star l) =
      halfL g z ⬝ᵥ (Hm.submatrix (Fin.castAdd g) (Fin.castAdd g)).mulVec (star (halfL g l)) +
      halfL g z ⬝ᵥ (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)).mulVec (star (halfR g l)) +
      halfR g z ⬝ᵥ (Hm.submatrix (Fin.natAdd g) (Fin.castAdd g)).mulVec (star (halfL g l)) +
      halfR g z ⬝ᵥ (Hm.submatrix (Fin.natAdd g) (Fin.natAdd g)).mulVec (star (halfR g l)) := by
  intro g Hm z l
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_add, Matrix.submatrix_apply, halfL_apply, halfR_apply,
    Pi.star_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem dot_comp_equiv : ∀ (n : ℕ) (e : Fin n ≃ Fin n) (Hm : Matrix (Fin n) (Fin n) ℂ) (z l : Fin n → ℂ),
    (z ∘ e) ⬝ᵥ Hm.mulVec (star (l ∘ e)) = z ⬝ᵥ (Hm.submatrix e.symm e.symm).mulVec (star l) := by
  intro n e Hm z l
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Function.comp_apply, Pi.star_apply]
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.apply_symm_apply]
  congr 1
  rw [← Equiv.sum_comp e.symm]
  simp only [Equiv.apply_symm_apply]

theorem sum_finset_fin_two_four_terms (f : ULift.{0} (Finset (Fin 2)) → ℂ) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [← Fintype.sum_equiv Equiv.ulift.symm (fun I : Finset (Fin 2) => f ⟨I⟩) f (fun _ => rfl)]
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem factor_eq_lamExp : ∀ (g : ℕ) (Hm : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (c : ℂ) (z l : Fin (g + g) → ℂ),
    Hm.submatrix (Fin.castAdd g) (Fin.castAdd g) = 0 → Hm.submatrix (Fin.natAdd g) (Fin.natAdd g) = 0 →
    Hm.submatrix (Fin.natAdd g) (Fin.castAdd g) = Hm.submatrix (Fin.castAdd g) (Fin.natAdd g) →
    c * Complex.exp (Real.pi / 2 * (LamAdd.B Hm (Fin.append (halfL g l) 0) (Fin.append 0 (halfR g l)) +
      LamAdd.B Hm (Fin.append 0 (halfR g l)) (Fin.append (halfL g l) 0))) =
      Complex.exp (Real.pi * LamAdd.B Hm (Fin.append (halfL g l) 0) (Fin.append 0 (halfR g l))) →
    c * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star l)) + Real.pi / 2 * (l ⬝ᵥ Hm.mulVec (star l))) =
      Complex.exp (LamAdd.Q (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) z l) := by
  intro g Hm c z l h11 h22 h21 hc
  have hB : ∀ x y : Fin (g + g) → ℂ, LamAdd.B Hm x y =
      LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfL g x) (halfR g y) + LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfR g x) (halfL g y) := by
    intro x y
    unfold LamAdd.B
    rw [dot_blocks, h11, h22, h21]
    simp
  have hB0 : ∀ x : Fin g → ℂ, LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) x 0 = 0 := fun x => by simp [LamAdd.B]
  have hd : ∀ x y : Fin (g + g) → ℂ, x ⬝ᵥ Hm.mulVec (star y) = LamAdd.B Hm x y := fun _ _ => rfl
  rw [hB, hB, halfL_append, halfR_append, halfL_append, halfR_append] at hc
  simp only [hB0, LamAdd.B_zero_left, add_zero, zero_add] at hc
  rw [hd, hd, hB, hB]
  unfold LamAdd.Q
  rw [sum_finset_fin_two_four_terms]
  have c0 : ∀ v, LamAdd.cmap g ⟨∅⟩ v = 0 := fun v => by simp [LamAdd.cmap]
  have c1 : ∀ v, LamAdd.cmap g ⟨{0}⟩ v = halfL g v := fun v => by simp [LamAdd.cmap]
  have c2 : ∀ v, LamAdd.cmap g ⟨{1}⟩ v = halfR g v := fun v => by simp [LamAdd.cmap]
  have c3 : ∀ v, LamAdd.cmap g ⟨{0, 1}⟩ v = halfL g v + halfR g v := fun v => by simp [LamAdd.cmap]
  have e0 : LamAdd.ε ⟨∅⟩ = 1 := by decide
  have e1 : LamAdd.ε ⟨{0}⟩ = -1 := by decide
  have e2 : LamAdd.ε ⟨{1}⟩ = -1 := by decide
  have e3 : LamAdd.ε ⟨{0, 1}⟩ = 1 := by decide
  rw [c0, c0, c1, c1, c2, c2, c3, c3, e0, e1, e2, e3]
  simp only [LamAdd.B_add_left, LamAdd.B_add_right, LamAdd.B_zero_left, hB0]
  have key : (Real.pi : ℂ) * (LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfL g z) (halfR g l) + LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfR g z) (halfL g l)) +
      Real.pi / 2 * (LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfL g l) (halfR g l) + LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfR g l) (halfL g l)) =
      Real.pi / 2 * (LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfL g l) (halfR g l) + LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfR g l) (halfL g l)) +
      Real.pi * (LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfL g z) (halfR g l) + LamAdd.B (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) (halfR g z) (halfL g l)) := by ring
  rw [key, Complex.exp_add, ← _root_.mul_assoc, hc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end GlobalTheory.BiRoot

namespace GlobalTheory.BiRoot

open GlobalTheory.ProdUnifSq GlobalTheory.TorusRM

theorem trivial_factor {B : Over (Sp ℂ)} [GrpObj B] {N : LB B.left} {n : ℕ} (v : HolUnif B N n)
    {H : Matrix (Fin n) (Fin n) ℂ} {ψ : v.Λ → ℂ} (hN : N.IsLB) (hv : IsFactorAH v H ψ)
    (ht : ∃ t : N.Gen, t.IsGen) : H = 0 ∧ ∀ l, ψ l = 1 := by
  obtain ⟨θ, hθ, hθ0, hper⟩ := exists_theta_of_gen B N n v hN ht
  refine ahFactor_trivial_of_theta n v.Λ v.full H ψ θ hv.1 hθ hθ0 hv.2.1 fun l z => ?_
  obtain ⟨i, hi⟩ := ahFactor_im_int_chart N hN (v.ex z).left
  have hzl : v.ex (z + l) = v.ex z := by rw [v.ex_add, (v.ker l).2 l.2, _root_.mul_one]
  have hi' : ⊤ ≤ (v.ex (z + l)).left ⁻¹ᵁ N.U i := by rw [hzl]; exact hi
  have e1 := hper l l.2 i z hi
  have e2 := hv.2.2 l i z hi
  have hne := v.fr_ne i (z + l) hi'
  rw [e2] at e1
  apply mul_right_cancel₀ hne
  linear_combination e1

def inl (g : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero, Pi.smul_apply,
        smul_eq_mul, mul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero, Pi.smul_apply,
        smul_eq_mul, mul_zero, RingHom.id_apply]

def inr (g : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun y := Fin.append 0 y
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero, Pi.smul_apply,
        smul_eq_mul, mul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero, Pi.smul_apply,
        smul_eq_mul, mul_zero, RingHom.id_apply]

def swapE (g : ℕ) : Fin (g + g) ≃ Fin (g + g) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)

theorem swapE_castAdd (g : ℕ) (k : Fin g) : swapE g (Fin.castAdd g k) = Fin.natAdd g k := by
  simp only [swapE, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumComm_apply, Sum.swap_inl,
    finSumFinEquiv_apply_right]

theorem swapE_natAdd (g : ℕ) (k : Fin g) : swapE g (Fin.natAdd g k) = Fin.castAdd g k := by
  simp only [swapE, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumComm_apply, Sum.swap_inr,
    finSumFinEquiv_apply_left]

theorem swapE_symm (g : ℕ) : (swapE g).symm = swapE g := Equiv.ext fun q => by
  rw [Equiv.symm_apply_eq]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) q
  · rw [swapE_castAdd, swapE_natAdd]
  · rw [swapE_natAdd, swapE_castAdd]

theorem halfL_swap (g : ℕ) (z : Fin (g + g) → ℂ) : halfL g (z ∘ swapE g) = halfR g z := by
  funext k; simp only [halfL_apply, halfR_apply, Function.comp_apply, swapE_castAdd]

theorem halfR_swap (g : ℕ) (z : Fin (g + g) → ℂ) : halfR g (z ∘ swapE g) = halfL g z := by
  funext k; simp only [halfL_apply, halfR_apply, Function.comp_apply, swapE_natAdd]

end GlobalTheory.BiRoot

namespace GlobalTheory.BiRoot

open GlobalTheory.ProdUnifSq GlobalTheory.TorusRM

theorem exists_lbIso_lam_of_birigid_symm : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∃ M : LB A.left, M.IsLB ∧ LBIso P (cubeLB A ![fst A A, snd A A] M) := by
  intro A _ _ g hA hg P hP h0A hA0 hsym
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨M₀, u₁, H₀, χ₀, hM₀, -, -, hAH⟩ := GlobalTheory.AHExists.exists_isAH A g hA L₀ u₀
  have hp : IsProjOver A.hom := GlobalTheory.ProjSpace.isProjOver_of_relAmple
    (GlobalTheory.LefschetzAmple.relAmple_of_isAH g A hA M₀ u₁ H₀ χ₀ hM₀ hAH)
  have hPP : IsProjOver (A ⊗ A).hom := GlobalTheory.ProjSpace.isProjOver_pullback hp hp
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨uP, Hm, χ, hexP, hF⟩ :=
    GlobalTheory.exists_isFactorAH_frame_of_unif (A ⊗ A) hAA _ (g + g) (sqUnif A u₁) P hP
  have hmemP : ∀ v, v ∈ uP.Λ ↔ v ∈ sqLat u₁.Λ := fun v => by
    rw [← uP.ker, hexP]; exact (sqUnif A u₁).ker v
  have hexS : ∀ v, uP.ex v = lift (u₁.ex (halfL g v)) (u₁.ex (halfR g v)) := fun v => by
    rw [hexP]; rfl
  have ex0 : u₁.ex 0 = 1 := (u₁.ker 0).2 (Submodule.zero_mem _)
  have hinl : ∀ l ∈ u₁.Λ, inl g l ∈ uP.Λ := fun l hl => (hmemP _).2 ((mem_sqLat _ _).2
      ⟨by rw [show inl g l = Fin.append l 0 from rfl, halfL_append]; exact hl,
       by rw [show inl g l = Fin.append l 0 from rfl, halfR_append]; exact Submodule.zero_mem _⟩)
  have hinr : ∀ l ∈ u₁.Λ, inr g l ∈ uP.Λ := fun l hl => (hmemP _).2 ((mem_sqLat _ _).2
      ⟨by rw [show inr g l = Fin.append 0 l from rfl, halfL_append]; exact Submodule.zero_mem _,
       by rw [show inr g l = Fin.append 0 l from rfl, halfR_append]; exact hl⟩)

  have hx1 := exists_pull_isFactorAH A (A ⊗ A) M₀ P g (g + g) u₁ uP (lift (𝟙 A) 1) (inl g) Hm
    (Hm.submatrix (Fin.castAdd g) (Fin.castAdd g)) χ hF (hF.1.submatrix _)
    (fun z l => by
      rw [dot_blocks]
      simp [inl, halfL_append, halfR_append])
    (fun z => by
      rw [hexS]
      show lift (u₁.ex (halfL g (Fin.append z 0))) (u₁.ex (halfR g (Fin.append z 0))) = _
      rw [halfL_append, halfR_append, ex0, comp_lift, Category.comp_id, comp_one])
    hinl
  obtain ⟨v₁, χ₁, -, hv₁Λ, hv₁, hχ₁⟩ := hx1
  obtain ⟨H11, c11⟩ := trivial_factor v₁ (LB.isLB_linComb hP _ _) hv₁ hA0

  have hx2 := exists_pull_isFactorAH A (A ⊗ A) M₀ P g (g + g) u₁ uP (lift 1 (𝟙 A)) (inr g) Hm
    (Hm.submatrix (Fin.natAdd g) (Fin.natAdd g)) χ hF (hF.1.submatrix _)
    (fun z l => by
      rw [dot_blocks]
      simp [inr, halfL_append, halfR_append])
    (fun z => by
      rw [hexS]
      show lift (u₁.ex (halfL g (Fin.append 0 z))) (u₁.ex (halfR g (Fin.append 0 z))) = _
      rw [halfL_append, halfR_append, ex0, comp_lift, Category.comp_id, comp_one])
    hinr
  obtain ⟨v₂, χ₂, -, hv₂Λ, hv₂, hχ₂⟩ := hx2
  obtain ⟨BorelApproximation, c22⟩ := trivial_factor v₂ (LB.isLB_linComb hP _ _) hv₂ h0A

  have hx3 := exists_pull_isFactorAH (A ⊗ A) (A ⊗ A) P P (g + g) (g + g) uP uP (lift (snd A A) (fst A A))
    (LinearMap.funLeft ℂ ℂ (swapE g)) Hm (Hm.submatrix (swapE g).symm (swapE g).symm) χ hF (hF.1.submatrix _)
    (fun z l => dot_comp_equiv (g + g) (swapE g) Hm z l)
    (fun z => by
      rw [hexS, hexS, comp_lift, lift_fst, lift_snd]
      show lift (u₁.ex (halfL g (z ∘ swapE g))) (u₁.ex (halfR g (z ∘ swapE g))) = _
      rw [halfL_swap, halfR_swap])
    (fun l hl => by
      rw [hmemP, mem_sqLat] at hl ⊢
      show halfL g (l ∘ swapE g) ∈ u₁.Λ ∧ halfR g (l ∘ swapE g) ∈ u₁.Λ
      rw [halfL_swap, halfR_swap]
      exact ⟨hl.2, hl.1⟩)
  obtain ⟨vs, χs, hvsex, -, hvs, -⟩ := hx3
  have hd := GlobalTheory.AHBundle.isFactorAH_divUnif uP vs hvsex hF hvs
  obtain ⟨Hsym, -⟩ := trivial_factor _ (LB.isLB_div (LB.isLB_linComb hP _ _) hP) hd hsym
  rw [sub_eq_zero] at Hsym
  have H21 : Hm.submatrix (Fin.natAdd g) (Fin.castAdd g) = Hm.submatrix (Fin.castAdd g) (Fin.natAdd g) := by
    ext i j
    have := congrFun (congrFun Hsym (Fin.castAdd g i)) (Fin.natAdd g j)
    simp only [Matrix.submatrix_apply, swapE_symm, swapE_castAdd, swapE_natAdd] at this
    simpa only [Matrix.submatrix_apply] using this
  have hH12 : (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hF.1.apply]
    exact congrFun (congrFun H21 i) j
  have hint : ∀ l ∈ u₁.Λ, ∀ l' ∈ u₁.Λ, ∃ n : ℤ,
      (l ⬝ᵥ (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)).mulVec (star l')).im = n := by
    intro l hl l' hl'
    obtain ⟨n, hn⟩ := ahFactor_im_int (g + g) (A ⊗ A) P uP Hm χ hP hF (inl g l) (hinl l hl) (inr g l') (hinr l' hl')
    refine ⟨n, ?_⟩
    rw [← hn, dot_blocks]
    simp [inl, inr, halfL_append, halfR_append]
  obtain ⟨M, uM, χM, hM, hexM, hFM⟩ :=
    GlobalTheory.AHBundle.exists_lb_of_hermitian_int g A hA M₀ u₁ H₀ χ₀ hM₀ hAH _ hH12 hint
  have hexL : (LamAdd.lamUnif u₁ uM hexM).ex = uP.ex := by rw [LamAdd.lamUnif_ex, hexP]
  have hG := GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) hAA hPP (LB.div (abelian₂ A M) P)
    (LB.isLB_div (LB.isLB_linComb hM _ _) hP) (g + g)
    (GlobalTheory.SameFactor.divUnif uP (LamAdd.lamUnif u₁ uM hexM) hexL) (fun _ => 1) (differentiable_const _)
    (fun _ => one_ne_zero) ?_
  · exact ⟨M, hM, hG⟩
  intro l hl p z hz
  have hl' : l ∈ uP.Λ := hl
  obtain ⟨hz1, hz2⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
  have hzl : uP.ex (z + l) = uP.ex z := by rw [uP.ex_add, (uP.ker l).2 hl', _root_.mul_one]
  have hsq := (hmemP l).1 hl'
  have e1 := LamAdd.lam_shift u₁ uM hexM hM hFM p.1 z l hsq (by rw [hexL]; exact hz1)
  have e2 := hF.2.2 ⟨l, hl'⟩ p.2 z hz2
  have hsq1 : halfL g l ∈ u₁.Λ := hsq.1
  have hsq2 : halfR g l ∈ u₁.Λ := hsq.2
  have ha : inl g (halfL g l) ∈ uP.Λ := hinl _ hsq1
  have hb : inr g (halfR g l) ∈ uP.Λ := hinr _ hsq2
  have hab : inl g (halfL g l) + inr g (halfR g l) = l := by
    rw [← append_halves l]
    show Fin.append (halfL g (Fin.append (halfL g l) (halfR g l))) 0 +
      Fin.append 0 (halfR g (Fin.append (halfL g l) (halfR g l))) = _
    rw [halfL_append, halfR_append]
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero, zero_add]
  have χa : LamAdd.ext uP.Λ χ (inl g (halfL g l)) = 1 := by
    rw [LamAdd.ext_of_mem _ _ ha]
    have hm : halfL g l ∈ v₁.Λ := by rw [hv₁Λ]; exact hsq1
    exact (hχ₁ ⟨halfL g l, hm⟩ ha).symm.trans (c11 _)
  have χb : LamAdd.ext uP.Λ χ (inr g (halfR g l)) = 1 := by
    rw [LamAdd.ext_of_mem _ _ hb]
    have hm : halfR g l ∈ v₂.Λ := by rw [hv₂Λ]; exact hsq2
    exact (hχ₂ ⟨halfR g l, hm⟩ hb).symm.trans (c22 _)
  have hs := LamAdd.semichar hP hF (inl g (halfL g l)) (inr g (halfR g l)) ha hb
  rw [χa, χb, _root_.one_mul, _root_.one_mul, hab, LamAdd.ext_of_mem _ _ hl'] at hs
  have e3 := factor_eq_lamExp g Hm (χ ⟨l, hl'⟩) z l H11 BorelApproximation H21 hs
  have n1 := uP.fr_ne p.2 (z + l) (by rw [hzl]; exact hz2)
  show 1 * ((LamAdd.lamUnif u₁ uM hexM).fr p.1 (z + l) * (uP.fr p.2 (z + l))⁻¹) =
    1 * ((LamAdd.lamUnif u₁ uM hexM).fr p.1 z * (uP.fr p.2 z)⁻¹)
  rw [e1, e2, e3]
  have n2 := Complex.exp_ne_zero (LamAdd.Q (Hm.submatrix (Fin.castAdd g) (Fin.natAdd g)) z l)
  field_simp

end GlobalTheory.BiRoot
