import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.SelfCube

private theorem exists_bound_of_continuous_lattice_periodic {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h : (Fin g → ℂ) → ℝ) (hc : Continuous h)
    (hp : ∀ z, ∀ l ∈ Λ, h (z + l) = h z) : ∃ M, ∀ z, h z ≤ M := by
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (Fin g → ℂ),
      Submodule.span ℤ (Set.range b) = Λ :=
    ⟨_, (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ⟩
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨M, hM⟩ := (hK.image hc).bddAbove
  refine ⟨M, fun z => ?_⟩
  have hfl : (ZSpan.floor b z : Fin g → ℂ) ∈ Λ := by
    exact Eq.mp (congrArg (fun S : Submodule ℤ (Fin g → ℂ) => (ZSpan.floor b z : Fin g → ℂ) ∈ S) hb)
      (ZSpan.floor b z).2
  have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
    rw [ZSpan.fract_apply]; abel
  rw [hz, hp _ _ hfl]
  exact hM ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), rfl⟩

theorem quad_nonneg {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ψ : (Fin g → ℂ) → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ψ 0 ≠ 0)
    (q : (Fin g → ℂ) → ℝ) (hq : Continuous q) (hs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w)
    (hper : ∀ z, ∀ l ∈ Λ, ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z)) (w) :
    0 ≤ q w := by
  by_contra hneg'
  have hneg := not_le.1 hneg'
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖ * Real.exp (-q z))
    (hψ.continuous.norm.mul (Real.continuous_exp.comp hq.neg)) (fun z l hl => hper z l hl)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  have hbd : ∀ t : ℂ, ‖ψ (t • w)‖ ≤ M * Real.exp (‖t‖ ^ 2 * q w) := by
    intro t
    have h1 := hM (t • w)
    simp only [hs] at h1
    have h2 : ‖ψ (t • w)‖ =
        ‖ψ (t • w)‖ * Real.exp (-(‖t‖ ^ 2 * q w)) * Real.exp (‖t‖ ^ 2 * q w) := by
      rw [_root_.mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, _root_.mul_one]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hdiff : Differentiable ℂ (fun t : ℂ => ψ (t • w)) :=
    hψ.comp (differentiable_id.smul_const w)
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => ψ (t • w)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨t, rfl⟩
    refine (hbd t).trans ?_
    have he : Real.exp (‖t‖ ^ 2 * q w) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le)
    exact mul_le_of_le_one_right hM0 he
  have hc : ∀ t : ℂ, ψ (t • w) = ψ 0 := fun t => by
    have := hdiff.apply_eq_apply_of_bounded hb t 0
    simpa using this
  have hlim : Filter.Tendsto (fun r : ℝ => M * Real.exp (‖(r : ℂ)‖ ^ 2 * q w)) Filter.atTop
      (𝓝 (M * 0)) := by
    refine Filter.Tendsto.const_mul M (Real.tendsto_exp_atBot.comp ?_)
    have h1 : Filter.Tendsto (fun r : ℝ => r ^ 2 * (-q w)) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_mul_const (neg_pos.2 hneg)
    refine (Filter.tendsto_neg_atTop_atBot.comp h1).congr (fun r => ?_)
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hle : ‖ψ 0‖ ≤ M * 0 :=
    ge_of_tendsto' hlim (fun r => by rw [← hc (r : ℂ)]; exact hbd _)
  rw [mul_zero] at hle
  exact h0 (norm_le_zero_iff.1 hle)

theorem form_eq_zero_of_unit {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ψ : (Fin g → ℂ) → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ∀ z, ψ z ≠ 0)
    (D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (hc : Continuous fun z => D z z)
    (hadd : ∀ z z' w, D (z + z') w = D z w + D z' w)
    (hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (hst : ∀ z w, D w z = starRingEnd ℂ (D z w))
    (ρ : Λ → ℂ) (hρ : ∀ l, ‖ρ l‖ = 1)
    (hper : ∀ z (l : Λ), ψ (z + l) = ρ l * cexp (π * D z l + π / 2 * D l l) * ψ z) :
    (∀ z w, D z w = 0) ∧ ∀ l, ρ l = 1 := by
  have hadd2 : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    rw [hst, hadd, map_add, ← hst, ← hst]
  have hsm2 : ∀ (t : ℂ) z w, D z (t • w) = starRingEnd ℂ t * D z w := fun t z w => by
    rw [hst, hsm, map_mul, ← hst]
  have hdiag_im : ∀ z, (D z z).im = 0 := fun z => by
    have := congrArg Complex.im (hst z z)
    rw [Complex.conj_im] at this
    linarith
  set q : (Fin g → ℂ) → ℝ := fun z => π / 2 * (D z z).re with hqdef
  have hqc : Continuous q := continuous_const.mul (Complex.continuous_re.comp hc)
  have hqs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w := fun t w => by
    simp only [hqdef, hsm, hsm2]
    rw [← _root_.mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
    ring
  have hexpand : ∀ z l, D (z + l) (z + l) = D z z + D z l + D l z + D l l := fun z l => by
    rw [hadd, hadd2, hadd2]; ring
  have hreal : ∀ z l, (D l z).re = (D z l).re := fun z l => by rw [hst, Complex.conj_re]
  have hnorm : ∀ z (l : Λ),
      ‖ψ (z + l)‖ = Real.exp (π * (D z l).re + π / 2 * (D l l).re) * ‖ψ z‖ := fun z l => by
    rw [hper, norm_mul, norm_mul, hρ, _root_.one_mul, Complex.norm_exp]
    congr 2
    simp [Complex.add_re, Complex.mul_re, hdiag_im]
  have hper_q : ∀ z (l : Λ),
      ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z) := fun z l => by
    rw [hnorm, mul_comm (Real.exp _) _, _root_.mul_assoc, ← Real.exp_add]
    congr 2
    simp only [hqdef, hexpand, Complex.add_re, hreal z l]
    ring
  have hq1 : ∀ w, 0 ≤ q w := fun w =>
    quad_nonneg Λ ψ hψ (h0 0) q hqc hqs (fun z l hl => hper_q z ⟨l, hl⟩) w
  have hq2 : ∀ w, 0 ≤ -q w := fun w =>
    quad_nonneg Λ (fun z => (ψ z)⁻¹) (hψ.inv h0) (inv_ne_zero (h0 0)) (fun z => -q z) hqc.neg
      (fun t w => by simp only [hqs]; ring) (fun z l hl => by
        have := hper_q z ⟨l, hl⟩
        simp only [norm_inv, neg_neg]
        have e1 : Real.exp (q (z + l)) = (Real.exp (-q (z + l)))⁻¹ := by rw [Real.exp_neg, inv_inv]
        have e2 : Real.exp (q z) = (Real.exp (-q z))⁻¹ := by rw [Real.exp_neg, inv_inv]
        rw [e1, e2, ← mul_inv, ← mul_inv]
        exact congrArg _ this) w
  have hdiag : ∀ z, D z z = 0 := fun z => by
    have hre : (D z z).re = 0 := by
      have h3 : q z = 0 := le_antisymm (by linarith [hq2 z]) (hq1 z)
      simp only [hqdef] at h3
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (by positivity)
      · exact h
    exact Complex.ext_iff.2 ⟨by simpa using hre, by simpa using hdiag_im z⟩
  have hD0 : ∀ z w, D z w = 0 := fun z w => by
    have e1 := hexpand z w
    rw [hdiag, hdiag, hdiag] at e1
    have e2 := hexpand (I • z) w
    rw [hdiag, hdiag, hdiag, hsm, hsm2, Complex.conj_I] at e2
    have hb : D w z = -D z w := by linear_combination (-1 : ℂ) * e1
    rw [hb] at e2
    have h2 : (2 * I) * D z w = 0 := by linear_combination -e2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero I_ne_zero)
    · exact h
  have hper' : ∀ z (l : Λ), ψ (z + l) = ρ l * ψ z := fun z l => by
    rw [hper, hD0, hD0]; simp
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖) hψ.continuous.norm (fun z l hl =>
    (congrArg norm (hper' z ⟨l, hl⟩)).trans (by rw [norm_mul, hρ, _root_.one_mul]))
  have hb : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM z⟩
  have hconst : ∀ z, ψ z = ψ 0 := fun z => hψ.apply_eq_apply_of_bounded hb z 0
  refine ⟨hD0, fun l => ?_⟩
  have h4 := hper' 0 l
  rw [hconst (0 + (l : Fin g → ℂ))] at h4
  exact mul_right_cancel₀ (h0 0) (h4.symm.trans (_root_.one_mul _).symm)

theorem exists_glue {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z) :
    ∃ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ ∀ j z, z ∈ D j → F z = G j z := by
  choose c hc' using hcov
  refine ⟨fun z => G (c z) z, fun z => ?_, fun j z hz => hc _ _ _ (hc' z) hz⟩
  have hev : (fun w => G (c w) w) =ᶠ[𝓝 z] G (c z) := by
    filter_upwards [(hD (c z)).mem_nhds (hc' z)] with w hw using hc _ _ _ (hc' w) hw
  exact ((hG (c z)).differentiableAt ((hD (c z)).mem_nhds (hc' z))).congr_of_eventuallyEq hev

section Herm

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem herm_add_left (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp only [hermForm, add_dotProduct]

theorem herm_add_right (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, mulVec_add, dotProduct_add]

theorem herm_smul_left (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem herm_zero_left (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  simp only [hermForm, zero_dotProduct]

theorem herm_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = starRingEnd ℂ (hermForm Hm z w) := by
  have hH' : Hmᴴ = Hm := hH
  simp only [hermForm]
  rw [starRingEnd_apply, ← star_dotProduct_star, Matrix.star_mulVec, star_star, hH',
    Matrix.dotProduct_mulVec]

theorem herm_continuous {a b : (Fin g → ℂ) → Fin g → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun z => hermForm Hm (a z) (b z) := by
  simp only [hermForm, dotProduct, mulVec]
  fun_prop

end Herm

theorem prod_finset_fin_two (f : Finset (Fin 2) → ℂ) :
    ∏ I : ULift.{0} (Finset (Fin 2)), f I.down = f ∅ * f {0} * f {1} * f {0, 1} := by
  rw [Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f (fun _ => rfl)]
  rw [← Finset.powerset_univ, show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    Finset.prod_powerset_insert (by decide),
    show ({1} : Finset (Fin 2)).powerset = {∅, {1}} by decide,
    Finset.prod_pair (by decide), Finset.prod_pair (by decide)]
  have h0 : (insert (0 : Fin 2) (∅ : Finset (Fin 2))) = {0} := by decide
  rw [h0]
  ring

theorem exp_pi_I_int (n : ℤ) : cexp (π * I * n) = (-1) ^ n := by
  rw [show (π : ℂ) * I * n = n * (π * I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem differentiableOn_prod' {g : ℕ} {α : Type*} {f : α → (Fin g → ℂ) → ℂ} {S : Set (Fin g → ℂ)}
    (s : Finset α) (hf : ∀ i, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const 1
  | insert a s ha ih => simp only [Finset.prod_insert ha]; exact (hf a).mul ih

open GlobalTheory.CubeValues

theorem val_div (hv : ValueRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (M L : LB X)
    (p q : M.ι × L.ι) (hp : ⊤ ≤ x ⁻¹ᵁ (M.U p.1 ⊓ L.U p.2)) (hq : ⊤ ≤ x ⁻¹ᵁ (M.U q.1 ⊓ L.U q.2)) :
    valAt' x ((LB.div M L).U p ⊓ (LB.div M L).U q) ((LB.div M L).g p q).val *
      valAt' x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2).val =
      valAt' x (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1).val := by
  have hp' := (le_preimage_inf x _ _).1 hp
  have hq' := (le_preimage_inf x _ _).1 hq
  have hL : ⊤ ≤ x ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2) := (le_preimage_inf x _ _).2 ⟨hp'.2, hq'.2⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ ((M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) :=
    (le_preimage_inf x _ _).2 ⟨hp, hq⟩
  obtain ⟨e, he⟩ := (hv X x).2.1 _ hW
  have hinv : ∀ u : Γ(X, (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2))ˣ,
      valAt' x _ (u⁻¹).val = (valAt' x _ u.val)⁻¹ := fun u => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [he, he, ← map_mul, Units.inv_mul, map_one]
  unfold LB.div
  dsimp only
  rw [val_unit_mul x hv hW, hinv, val_res x hv _ hW, val_res x hv _ hW,
    inv_mul_cancel_right₀ (val_unit_ne_zero x hv hL _)]

theorem exists_chart (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) : ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  obtain ⟨hcov, -, -⟩ := hL
  have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  exact ⟨i, ((hv _ _).1 _).2 hi⟩

theorem exists_unit_of_iso (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]
    {L : LB A.left} (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) {n : ℕ} (y : Fin n → (A ⟶ A))
    (Y : Fin n → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hY : ∀ k, ∀ l ∈ u.Λ, Y k l ∈ u.Λ)
    (hy : ∀ k z, u.ex z ≫ y k = u.ex (Y k z))
    (a : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (ha : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l z * u.fr i (z + l))
    (hiso : LBIso L (cubeLB A y L)) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ (∀ z, ψ z ≠ 0) ∧ ∀ z, ∀ l ∈ u.Λ,
      ψ (z + l) * a l z = (∏ I : ULift.{0} (Finset (Fin n)),
        a (∑ k ∈ I.down, Y k l) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) * ψ z := by
  classical
  obtain ⟨w, hw⟩ := hiso
  have hpt : ∀ z (I : ULift.{0} (Finset (Fin n))),
      (u.ex z).left ≫ (psum A y I.down).left = (u.ex (∑ k ∈ I.down, Y k z)).left := fun z I => by
    rw [← Over.comp_left, comp_psum u (u.ex z) y (fun k => Y k z) (fun k => hy k z)]
  have hMc : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j ↔
        ∀ I : ULift.{0} (Finset (Fin n)), ⊤ ≤ (u.ex (∑ k ∈ I.down, Y k z)).left ⁻¹ᵁ L.U (j I) :=
    fun z j => by
      have h1 := le_preimage_wchart (u.ex z).left L
        (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left) j
      simp only [hpt] at h1
      exact h1
  have hMg : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' →
      valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j') ((cubeLB A y L).g j j').val =
        ∏ I : ULift.{0} (Finset (Fin n)), valAt' (u.ex (∑ k ∈ I.down, Y k z)).left
          (L.U (j I) ⊓ L.U (j' I)) (L.g (j I) (j' I)).val ^ ((-1 : ℤ) ^ (n - I.down.card)) :=
    fun z j j' hj hj' => by
      have h1 := val_linComb (u.ex z).left hv L
        (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left)
        (fun I => (-1 : ℤ) ^ (n - I.down.card)) j j' hj hj'
      simp only [hpt] at h1
      exact h1
  obtain ⟨Fc, hFc⟩ : ∃ Fc : (ULift.{0} (Finset (Fin n)) → L.ι) → (Fin g → ℂ) → ℂ,
      Fc = fun j z => ∏ I : ULift.{0} (Finset (Fin n)),
        u.fr (j I) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card)) := ⟨_, rfl⟩
  have hFc_ne : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → Fc j z ≠ 0 := fun z j hj => by
    simp only [hFc]
    exact Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (u.fr_ne _ _ ((hMc z j).1 hj I))
  have hFc_g : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' →
      Fc j z = valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j')
        ((cubeLB A y L).g j j').val * Fc j' z := fun z j j' hj hj' => by
    rw [hMg z j j' hj hj']
    simp only [hFc]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [← mul_zpow, ← u.fr_compat _ _ _
      ((le_preimage_inf _ _ _).2 ⟨(hMc z j).1 hj I, (hMc z j').1 hj' I⟩)]
  have hdiv : ∀ z (p : (LB.div (cubeLB A y L) L).ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p ↔
        ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U p.1 ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2 :=
    fun z p => le_preimage_inf _ _ _
  have hex : ∀ z l, l ∈ u.Λ → u.ex (z + l) = u.ex z := fun z l hl => by
    rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  obtain ⟨G, hG⟩ : ∃ G : (LB.div (cubeLB A y L) L).ι → (Fin g → ℂ) → ℂ,
      G = fun p z => valAt' (u.ex z).left ((LB.div (cubeLB A y L) L).U p) (w.s p).val *
        u.fr p.2 z / Fc p.1 z := ⟨_, rfl⟩
  have hG_ne : ∀ p z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p → G p z ≠ 0 := by
    intro p z hz
    have h2 := (hdiv z p).1 hz
    simp only [hG]
    exact div_ne_zero (mul_ne_zero (val_unit_ne_zero _ hv hz _) (u.fr_ne _ _ h2.2))
      (hFc_ne z _ h2.1)
  have hcov : ∀ z, ∃ p, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := fun z => by
    obtain ⟨i, hi⟩ := exists_chart hv hL u z
    choose j hj using fun I : ULift.{0} (Finset (Fin n)) => exists_chart hv hL u (∑ k ∈ I.down, Y k z)
    exact ⟨(j, i), (hdiv z (j, i)).2 ⟨(hMc z j).2 hj, hi⟩⟩
  have hopen : ∀ p, IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} :=
    fun p => (u.hol _ (w.s p).val).1
  have hYd : ∀ I : ULift.{0} (Finset (Fin n)), Differentiable ℂ (fun z => ∑ k ∈ I.down, Y k z) :=
    fun I => by
      have h : ∀ k, Differentiable ℂ (Y k) := fun k => by
        simpa using (LinearMap.toContinuousLinearMap (Y k)).differentiable
      have h2 : ∀ s : Finset (Fin n), Differentiable ℂ (fun z => ∑ k ∈ s, Y k z) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact differentiable_const 0
        | insert b s hb ih => simp only [Finset.sum_insert hb]; exact (h b).add ih
      exact h2 I.down
  have hGd : ∀ p, DifferentiableOn ℂ (G p)
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := fun p => by
    have hsub2 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} ⊆
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2} := fun z hz => ((hdiv z p).1 hz).2
    have hF : DifferentiableOn ℂ (Fc p.1)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := by
      simp only [hFc]
      refine differentiableOn_prod' Finset.univ fun I => ?_
      have hc : DifferentiableOn ℂ (fun z => u.fr (p.1 I) (∑ k ∈ I.down, Y k z))
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} :=
        (u.fr_hol (p.1 I)).comp (hYd I).differentiableOn
          (fun z hz => (hMc z p.1).1 ((hdiv z p).1 hz).1 I)
      rcases neg_one_pow_eq_or ℤ (n - I.down.card) with h | h
      · simp only [h, zpow_one]; exact hc
      · simp only [h, _root_.zpow_neg_one]
        exact hc.inv fun z hz => u.fr_ne _ _ ((hMc z p.1).1 ((hdiv z p).1 hz).1 I)
    simp only [hG, div_eq_mul_inv]
    exact (((u.hol _ (w.s p).val).2).mul ((u.fr_hol p.2).mono hsub2)).mul
      (hF.inv fun z hz => hFc_ne z _ ((hdiv z p).1 hz).1)
  have hcompat : ∀ p q z, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} →
      z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U q} → G p z = G q z := by
    intro p q z hp hq
    have hp' := (hdiv z p).1 hp
    have hq' := (hdiv z q).1 hq
    have hpq : ⊤ ≤ (u.ex z).left ⁻¹ᵁ
        ((LB.div (cubeLB A y L) L).U p ⊓ (LB.div (cubeLB A y L) L).U q) :=
      (le_preimage_inf _ _ _).2 ⟨hp, hq⟩
    have hL2 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2) :=
      (le_preimage_inf _ _ _).2 ⟨hp'.2, hq'.2⟩
    have e1 := val_gen (u.ex z).left hv w hw p q hp hq
    have e2 := val_div hv (u.ex z).left (cubeLB A y L) L p q hp hq
    have e3 := u.fr_compat p.2 q.2 z hL2
    have e4 := hFc_g z p.1 q.1 hp'.1 hq'.1
    have n1 := val_unit_ne_zero _ hv hpq ((LB.div (cubeLB A y L) L).g p q)
    have n2 := val_unit_ne_zero _ hv hL2 (L.g p.2 q.2)
    have n3 := hFc_ne z q.1 hq'.1
    simp only [hG]
    rw [e1, e3, e4, ← e2]
    field_simp
  obtain ⟨F, hFd, hFG⟩ := exists_glue
    (fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}) G hopen hcov hGd hcompat
  refine ⟨F, hFd, fun z => ?_, fun z l hl => ?_⟩
  · obtain ⟨p, hp⟩ := hcov z
    rw [hFG p z hp]
    exact hG_ne p z hp
  · obtain ⟨p, hp⟩ := hcov z
    have hp' := (hdiv z p).1 hp
    have hpl : z + l ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := by
      rw [Set.mem_ofPred_eq, hex z l hl]
      exact hp
    rw [hFG p z hp, hFG p (z + l) hpl]
    simp only [hG]
    rw [hex z l hl]
    have e1 := ha l hl p.2 z hp'.2
    have hSl : ∀ I : ULift.{0} (Finset (Fin n)), ∑ k ∈ I.down, Y k l ∈ u.Λ :=
      fun I => Submodule.sum_mem _ fun k _ => hY k l hl
    have e2 : Fc p.1 z = (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l)
        (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) * Fc p.1 (z + l) := by
      simp only [hFc]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← mul_zpow, ha _ (hSl I) (p.1 I) _ ((hMc z p.1).1 hp'.1 I)]
      rw [show ∑ k ∈ I.down, Y k (z + l) = ∑ k ∈ I.down, Y k z + ∑ k ∈ I.down, Y k l by
        simp only [map_add, Finset.sum_add_distrib]]
    have n0 := hFc_ne z p.1 hp'.1
    have n1 : Fc p.1 (z + l) ≠ 0 := hFc_ne (z + l) p.1 (by rw [hex z l hl]; exact hp'.1)
    have n2 : (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l)
        (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) ≠ 0 := fun h => n0 (by
      rw [e2, h, zero_mul])
    rw [e1, e2]
    field_simp

theorem semicharacter_rule (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (χ : u.Λ → ℂ)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z =
      (χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)) * u.fr i (z + l))
    (l m : u.Λ) (n : ℤ) (hn : (n : ℝ) = (hermForm Hm l m).im) :
    χ (l + m) = χ l * χ m * (-1) ^ n := by
  obtain ⟨i, hi⟩ := exists_chart hv hL u 0
  have hper : ∀ (a : u.Λ) z, u.ex (z + a) = u.ex z := fun a z => by
    rw [u.ex_add, (u.ker a).2 a.2, _root_.mul_one]
  have hne : u.fr i (0 + (l : Fin g → ℂ) + m) ≠ 0 := u.fr_ne i _ (by rw [hper m, hper l]; exact hi)
  have h1 := hfr (l + m) i 0 hi
  have h2 := hfr l i 0 hi
  have h3 := hfr m i (0 + l) (by rw [hper l]; exact hi)
  rw [Submodule.coe_add, ← add_assoc] at h1
  rw [h3] at h2
  have key := mul_right_cancel₀ hne (h1.symm.trans (h2.trans (_root_.mul_assoc _ _ _).symm))
  simp only [herm_zero_left, mul_zero, zero_add] at key
  have hsum : hermForm Hm (↑l + ↑m) (↑l + ↑m) = hermForm Hm l l + hermForm Hm l m +
      starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m := by
    rw [herm_add_left, herm_add_right, herm_add_right, ← herm_conj Hm hH]; ring
  rw [hsum] at key
  have hc : hermForm Hm l m - starRingEnd ℂ (hermForm Hm l m) =
      2 * ((hermForm Hm l m).im : ℂ) * I := by
    rw [Complex.sub_conj]; push_cast; ring
  have hn' : (n : ℂ) = ((hermForm Hm l m).im : ℂ) := by exact_mod_cast hn
  have hX := Complex.exp_ne_zero (π / 2 * (hermForm Hm l l + hermForm Hm l m +
      starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m))
  rw [← exp_pi_I_int n]
  refine mul_right_cancel₀ hX ?_
  rw [key]
  have hE : cexp (↑π / 2 * hermForm Hm ↑l ↑l) * cexp (↑π * hermForm Hm ↑l ↑m + ↑π / 2 * hermForm Hm ↑m ↑m) =
      cexp (↑π * I * ↑n) * cexp (↑π / 2 * (hermForm Hm ↑l ↑l + hermForm Hm ↑l ↑m +
      starRingEnd ℂ (hermForm Hm ↑l ↑m) + hermForm Hm ↑m ↑m)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination ((π : ℂ) / 2) * hc - ((π : ℂ) * I) * hn'
  linear_combination (χ l * χ m) * hE

theorem appellHumbert_data_of_iso_cube :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (P : Out.PolAV (Sp ℂ)) [IsCommMonObj P.A] (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (f : P.A ⟶ P.A) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u.Λ), (∀ z, u.ex (F z) = u.ex z ≫ f) → LBIso P.L (cubeLB P.A ![𝟙 P.A, f] P.L) → (∀ z w, hermForm Hm z w = hermForm Hm z (F w) + hermForm Hm (F z) w) ∧ ∀ l : u.Λ, χ l = (-1) ^ Ef l ⟨F l, hF l l.2⟩) := by
  classical
  intro hv hh P _ u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ f F hF hexF hiso
  have hv' : ValueRules := hv
  clear hv hh
  have : DiscreteTopology u.Λ := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hfr' : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z =
      (χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)) * u.fr i (z + l) := hfr
  have hχne : ∀ l, χ l ≠ 0 := fun l h => by
    have h1 := hχ l
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hχ0 : χ 0 = 1 := by
    have h := semicharacter_rule hv' P.isLB u hH χ hfr' 0 0 0 (by simp [herm_zero_left])
    simp only [add_zero, zpow_zero, _root_.mul_one] at h
    exact mul_right_cancel₀ (hχne 0) (h.symm.trans (_root_.one_mul _).symm)
  obtain ⟨a, ha_def⟩ : ∃ a : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, a = fun l z =>
      if h : l ∈ u.Λ then χ ⟨l, h⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) else 1 :=
    ⟨_, rfl⟩
  have ha_mem : ∀ l (hl : l ∈ u.Λ) z,
      a l z = χ ⟨l, hl⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) := fun l hl z => by
    simp only [ha_def, dif_pos hl]
  have ha : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = a l z * u.fr i (z + l) :=
    fun l hl i z hz => by rw [ha_mem l hl]; exact hfr' ⟨l, hl⟩ i z hz
  obtain ⟨ψ, hψd, hψ0, hψp⟩ := exists_unit_of_iso hv' P.isLB u ![𝟙 P.A, f] ![LinearMap.id, F]
    (by intro k; fin_cases k
        · simp
        · simpa using hF)
    (by intro k z; fin_cases k
        · simp
        · simp [hexF])
    a ha hiso
  have hprod : ∀ z l, l ∈ u.Λ → ψ (z + l) * a l z =
      a 0 0 * (a l z)⁻¹ * (a (F l) (F z))⁻¹ * a (l + F l) (z + F z) * ψ z := by
    intro z l hl
    rw [hψp z l hl, prod_finset_fin_two (fun J => a (∑ k ∈ J, (![LinearMap.id, F] k) l)
      (∑ k ∈ J, (![LinearMap.id, F] k) z) ^ ((-1 : ℤ) ^ (2 - J.card)))]
    simp
  obtain ⟨D, hD⟩ : ∃ D : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, D = fun z w =>
      hermForm Hm z (F w) + hermForm Hm (F z) w - hermForm Hm z w := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : u.Λ → ℂ, ρ = fun l => χ (l + ⟨F l, hF l l.2⟩) * (χ l)⁻¹ * (χ l)⁻¹ *
      (χ ⟨F l, hF l l.2⟩)⁻¹ := ⟨_, rfl⟩
  have hFc : Continuous F := F.continuous_of_finiteDimensional
  have hc : Continuous fun z => D z z := by
    simp only [hD]
    exact ((herm_continuous Hm continuous_id hFc).add (herm_continuous Hm hFc continuous_id)).sub
      (herm_continuous Hm continuous_id continuous_id)
  have hadd : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [hD, herm_add_left, map_add]; ring
  have hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w := fun t z w => by
    simp only [hD, herm_smul_left, map_smul]; ring
  have hst : ∀ z w, D w z = starRingEnd ℂ (D z w) := fun z w => by
    simp only [hD, map_sub, map_add, ← herm_conj Hm hH]; ring
  have hρ : ∀ l, ‖ρ l‖ = 1 := fun l => by
    simp [hρdef, hχ]
  have hper : ∀ z (l : u.Λ), ψ (z + l) = ρ l * cexp (π * D z l + π / 2 * D l l) * ψ z := by
    intro z l
    have hl := l.2
    have hFl := hF l l.2
    have hlF : (l : Fin P.g → ℂ) + F l ∈ u.Λ := Submodule.add_mem _ hl hFl
    have key := hprod z l hl
    rw [ha_mem 0 (Submodule.zero_mem _), ha_mem l hl, ha_mem (F l) hFl, ha_mem _ hlF] at key
    have h0' : (⟨0, Submodule.zero_mem _⟩ : u.Λ) = 0 := rfl
    have hlF' : (⟨(l : Fin P.g → ℂ) + F l, hlF⟩ : u.Λ) = l + ⟨F l, hFl⟩ := rfl
    rw [h0', hχ0, hlF'] at key
    simp only [herm_zero_left, mul_zero, zero_add, Complex.exp_zero, _root_.mul_one,
      _root_.one_mul] at key
    have hX : cexp (π * D z l + π / 2 * D l l) =
        cexp (π * hermForm Hm (z + F z) (l + F l) + π / 2 * hermForm Hm (l + F l) (l + F l)) *
        (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ *
        (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ *
        (cexp (π * hermForm Hm (F z) (F l) + π / 2 * hermForm Hm (F l) (F l)))⁻¹ := by
      simp only [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      simp only [hD, herm_add_left, herm_add_right]
      ring
    rw [hX, hρdef]
    have e1 := Complex.exp_ne_zero (π * hermForm Hm z l + π / 2 * hermForm Hm l l)
    have e2 := Complex.exp_ne_zero (π * hermForm Hm (F z) (F l) + π / 2 * hermForm Hm (F l) (F l))
    have c1 := hχne l
    have c2 := hχne ⟨F l, hFl⟩
    have hmul := mul_ne_zero c1 e1
    rw [← mul_inv_cancel_right₀ hmul (ψ (z + l)), key]
    field_simp
  obtain ⟨hD0, hρ1⟩ := form_eq_zero_of_unit u.Λ ψ hψd hψ0 D hc hadd hsm hst ρ hρ hper
  refine ⟨fun z w => ?_, fun l => ?_⟩
  · have h1 := hD0 z w
    simp only [hD] at h1
    linear_combination -h1
  · have h1 := hρ1 l
    simp only [hρdef] at h1
    have h2 := semicharacter_rule hv' P.isLB u hH χ hfr' l ⟨F l, hF l l.2⟩ (Ef l ⟨F l, hF l l.2⟩)
      (hE _ _)
    rw [h2] at h1
    have c1 := hχne l
    have c2 := hχne ⟨F l, hF l l.2⟩
    field_simp at h1
    exact h1.symm

end GlobalTheory.SelfCube
