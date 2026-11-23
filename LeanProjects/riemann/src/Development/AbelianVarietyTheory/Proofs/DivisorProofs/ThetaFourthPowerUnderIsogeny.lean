import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannForm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaShift

section Reindex

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE h3).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem unitsRes_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res h3 x :=
  Units.ext (res_res h1 h2 h3 (x : Γ(X, U)))

theorem chart_le (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
  fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem chart_ge (L : LB X) (k : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k PUnit.unit) :=
  fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit

end Reindex

section Reindex2

variable {X : Scheme.{0}}

theorem basicOpen_res' {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

theorem g_finOne (L : LB X) (n : ℕ) (i j : Fin 1 → L.ι) :
    (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))).g i j =
      res (inf_le_inf (chart_le L i) (chart_le L j)) ((lbPow L n).g (fun _ => i 0) (fun _ => j 0)) := by
  simp only [lbPow, LB.LinComb, Fin.prod_univ_one, Finset.univ_unique, Finset.prod_singleton, map_zpow]
  congr 1
  exact (unitsRes_res _ _ _ _).symm

def secFinOne {L : LB X} {n : ℕ} (s : (lbPow L n).Sec) : Out.H0 L n where
  f j := (X.presheaf.map (homOfLE (chart_le L j)).op).hom (s.f (fun _ => j 0))
  compat i j := by
    have K := inf_le_inf (chart_le L i) (chart_le L j)
    have hc := congrArg (X.presheaf.map (homOfLE K).op).hom (s.compat (fun _ => i 0) (fun _ => j 0))
    have hl : LB.wchart L (fun _ : Fin 1 => 𝟙 X) i ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤
        LB.wchart L (fun _ : Fin 1 => 𝟙 X) i := inf_le_left
    have hr : LB.wchart L (fun _ : Fin 1 => 𝟙 X) i ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤
        LB.wchart L (fun _ : Fin 1 => 𝟙 X) j := inf_le_right
    have hl0 : LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) ≤
        LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) := inf_le_left
    have hr0 : LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) ≤
        LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) := inf_le_right
    have e1 := res_res (chart_le L i) hl (K.trans hl0) (s.f (fun _ => i 0))
    have e2 := res_res hl0 K (K.trans hl0) (s.f (fun _ => i 0))
    have e3 := res_res (chart_le L j) hr (K.trans hr0) (s.f (fun _ => j 0))
    have e4 := res_res hr0 K (K.trans hr0) (s.f (fun _ => j 0))
    have e5 := RingHom.map_mul (X.presheaf.map (homOfLE K).op).hom
      ((lbPow L n).g (fun _ => i 0) (fun _ => j 0)).val ((X.presheaf.map (homOfLE hr0).op).hom (s.f (fun _ => j 0)))
    have e6 := congrArg Units.val (g_finOne L n i j)
    exact e1.trans (e2.symm.trans (hc.trans (e5.trans (congrArg₂ (· * ·) e6.symm (e4.trans e3.symm)))))

theorem nonzeroLocus_secFinOne {L : LB X} {n : ℕ} (s : (lbPow L n).Sec) :
    Out.nonzeroLocus (secFinOne s) = Out.nonzeroLocus s := by
  apply le_antisymm
  · refine iSup_le fun (j : Fin 1 → L.ι) => ?_
    exact (basicOpen_res' (chart_le L j) _).le.trans (inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) _))
  · refine iSup_le fun (k : PUnit → L.ι) => ?_
    refine le_trans ?_ (le_iSup (fun j => X.basicOpen ((secFinOne s).f j)) (fun _ => k PUnit.unit))
    exact (le_inf ((X.basicOpen_le _).trans (chart_ge L k)) le_rfl).trans (basicOpen_res' (chart_le L _) _).ge

end Reindex2

section Theta

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {A' : Over (Sp ℂ)} [GrpObj A'] {M' : LB A'.left} {g : ℕ}

theorem differentiable_hermForm_left (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin g → ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => hermForm Hm z a) := by
  simp only [hermForm, dotProduct]
  fun_prop

theorem isThetaFn_shift (u : HolUnif A M g) (u' : HolUnif A' M' g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ} (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ)
    (hχ : ∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im))
    {θ : (Fin g → ℂ) → ℂ} (hθ : u'.IsThetaFn Hm χ' 4 θ) :
    u.IsThetaFn Hm χ 4 (fun z => θ (z + a) * Complex.exp (-(4 * Real.pi) * hermForm Hm z a)) := by
  refine ⟨(hθ.1.comp (differentiable_id.add_const a)).mul
    (((differentiable_hermForm_left Hm a).const_mul _).cexp), fun l z => ?_⟩
  have hl : z + (l : Fin g → ℂ) + a = (z + a) + ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) := by
    simp only [Submodule.coe_inclusion]; abel
  have e1 : hermForm Hm (z + a) ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) =
      hermForm Hm z l + hermForm Hm a l := by
    simp [hermForm, add_dotProduct]
  have e2 : hermForm Hm (z + l) a = hermForm Hm z a + hermForm Hm l a := by
    simp [hermForm, add_dotProduct]
  have e3 : hermForm Hm ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) =
      hermForm Hm l l := rfl
  have e4 : hermForm Hm l a = (starRingEnd ℂ) (hermForm Hm a l) := GlobalTheory.LatticeHom.hermForm_swap_of_isHermitian hH a l
  have hw : (starRingEnd ℂ) (hermForm Hm a l) = hermForm Hm a l - 2 * Complex.I * ((hermForm Hm a l).im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  show θ (z + (l : Fin g → ℂ) + a) * _ = _ * (θ (z + a) * _)
  rw [hl, hθ.2, e1, e3, e2, e4, hw, hχ l]
  have key : Complex.exp (Real.pi * (hermForm Hm z l + hermForm Hm a l) + Real.pi / 2 * hermForm Hm l l) ^ 4 *
      Complex.exp (-(4 * Real.pi) * (hermForm Hm z a + (hermForm Hm a l - 2 * Complex.I * ((hermForm Hm a l).im : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) ^ 4 *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ 4 *
      Complex.exp (-(4 * Real.pi) * hermForm Hm z a) := by
    simp only [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, mul_pow]
  linear_combination (χ' (Submodule.inclusion h l) ^ 4 * θ (z + a)) * key

end Theta

open GlobalTheory.LatticeHom in

theorem exists_morphism_affine_cover : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → (∀ θ, u.IsThetaFn Hm χ 4 θ → ∃ s, u.IsFnPow 4 s θ) →
    ∀ (P : Out.PolAV (Sp ℂ)) (u' : HolUnif P.A P.L g) (χ' : u'.Λ → ℂ) (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ),
    P.g = g → u'.IsAH Hm χ' →
    (∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im)) →
    ∃ ψ : A.left ⟶ P.A.left, ψ ≫ P.A.hom = A.hom ∧ (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) ∧
      ∀ x : A.left, ∃ (s : Out.H0 M 4) (V : P.A.left.Opens), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen V ∧
        Out.nonzeroLocus s = ψ ⁻¹ᵁ V := by
  intro g A _ hA M u Hm χ hM hAH hsec P u' χ' h a hg hAH' hχ
  subst hg
  have hsm : Smooth A.hom := hA.smooth
  have hred : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hsm
  obtain ⟨-, -, -, -, -, -, -, hsecfn, -⟩ := AnyAppellHumbert.isAH_properties abelianSchemeLaws_all.1
    abelianSchemeLaws_all.2 (fun S P M hM => AbLaw.CubeAssembly.cube_gen S P M hM) thetaUnifAV_all P u' Hm χ' hAH'
  obtain ⟨m, t, hcov, hD⟩ := veryAmple_lbPow abelianSchemeLaws_all.1.ample ℂ P 4 le_rfl
  choose θ hθ hθt using fun j => ((hsecfn 4).1 (t j)).exists
  have hG : ∀ z, Complex.exp (-(4 * Real.pi) * hermForm Hm z a) ≠ 0 := fun z => Complex.exp_ne_zero _
  choose s hs using fun j => hsec _ (isThetaFn_shift u u' hAH'.1 h a hχ (hθ j))
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ A) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    fun y => u'.ex (Function.surjInv u.ex_onto y + a)
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (z + a) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (z + a) ⟨_, h h1⟩
    rw [← this]
    show u'.ex _ = u'.ex _
    congr 1
    simp only
    abel
  have hmem : ∀ j z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ Out.nonzeroLocus (t j) ↔ θ j z ≠ 0 :=
    fun j => le_preimage_nonzeroLocus_iff u' P.isLB (hθt j)
  have hmemA : ∀ j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus (s j) ↔
      θ j (z + a) * Complex.exp (-(4 * Real.pi) * hermForm Hm z a) ≠ 0 :=
    fun j => le_preimage_nonzeroLocus_iff u hM (hs j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P.A A hred inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (z₀ + a)).left _ hcov
    obtain ⟨haff, r, hrr, hgen⟩ := hD i
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u hM hs i (mul_ne_zero ((hmem i _).1 hi) (hG z₀))
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun φ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem i _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen φ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem i _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P.isLB (hθt i) (hθt j) (r j) (hrr j) h1,
        mul_div_mul_right _ _ h2]
  have hfe : ∀ z, (u.ex z).left ≫ f.left = (u'.ex (z + a)).left := fun z => by
    rw [← Over.comp_left, hf, hΦ]
  have heq : ∀ j, Out.nonzeroLocus (s j) = f.left ⁻¹ᵁ Out.nonzeroLocus (t j) := fun j => by
    have hpt : ∀ x' : Sp ℂ ⟶ A.left, x' ≫ A.hom = 𝟙 _ → (⊤ ≤ x' ⁻¹ᵁ Out.nonzeroLocus (s j) ↔
        ⊤ ≤ (x' ≫ f.left) ⁻¹ᵁ Out.nonzeroLocus (t j)) := by
      intro x' hx'
      obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x' hx')
      have hz' : (u.ex z).left = x' := by rw [hz]; rfl
      rw [← hz', hfe, hmemA, hmem]
      exact ⟨left_ne_zero_of_mul, fun h0 => mul_ne_zero h0 (hG z)⟩
    exact le_antisymm (ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun x' hx' => (hpt x' hx').1)
      (ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun x' hx' => (hpt x' hx').2)
  refine ⟨f.left, Over.w f, hfe, fun x => ?_⟩
  have hx : x ∈ f.left ⁻¹ᵁ (⨆ j, Out.nonzeroLocus (t j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨secFinOne (s j), Out.nonzeroLocus (t j), ?_, (hD j).1, ?_⟩
  · rw [nonzeroLocus_secFinOne, heq]
    exact hj
  · rw [nonzeroLocus_secFinOne, heq]

end GlobalTheory.ThetaShift
