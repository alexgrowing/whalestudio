import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.TorusRM GlobalTheory.RosatiAH GlobalTheory.AppellHumbertTrivial in

theorem GlobalTheory.RosatiAH.hermForm_prod_halfDiag : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (U : HolUnif (X.A ⊗ X.A) (X.P c) (Module.finrank ℚ F + Module.finrank ℚ F))
      (H : Matrix (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) ℂ)
      (χ' : U.Λ → ℂ), (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    ∀ x y x' y' : Fin (Module.finrank ℚ F) → ℂ,
      hermForm H (Fin.append x y) (Fin.append x' y') =
        (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x y' + hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) y x') / 2 := by
  intro F _ _ _ 𝔠 X c _ u e hu h χ hAH U H χ' hexU hFU
  set Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ := Matrix.diagonal fun j ↦ (h j : ℂ) with hHm
  obtain ⟨U0, hU0⟩ := GlobalTheory.T.product_abelian_uniformization X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  obtain ⟨U2, H2, χ2, hex2', hF2⟩ := GlobalTheory.T.exists_appell_humbert_line_bundle (X.A ⊗ X.A) hAb2 _ _ U0 (X.P ((2 : 𝓞 F) • c)) (X.isLB _)
  have hex2 : ∀ x y, U2.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := fun x y => by rw [hex2']; exact hU0 x y
  have hswap : ∀ {c' : 𝔠.elt} (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F)),
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) →
      ∀ v, U.ex (fswap _ v) = U.ex v ≫ lift (snd X.A X.A) (fst X.A X.A) := by
    intro c' U hex v
    rw [eq_append v, fswap_append, hex, hex]
    simp
  have hS : ∀ {c' : 𝔠.elt} (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F)) H χ',
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → IsFactorAH U H χ' →
      ∀ x y x' y', hermForm H (Fin.append x y) (Fin.append x' y') = hermForm H (Fin.append y x) (Fin.append y' x') := by
    intro c' U H χ' hex hF x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P c') (X.P c') (X.isLB c') (X.isLB c') _ _ U U H χ' H χ'
      hF hF (lift (snd X.A X.A) (fst X.A X.A)) (fswap _) (hswap U hex) (X.symm c') (Fin.append x y) (Fin.append x' y')
    rwa [fswap_append, fswap_append] at this
  have h2F : (((2 : 𝓞 F)) : F) = 2 := by norm_cast
  have h2 : (dmul fun j => ((e j (((2 : 𝓞 F) : F)) : ℝ) : ℂ)) = (2 : ℂ) • LinearMap.id := by
    refine LinearMap.ext fun z => funext fun k => ?_
    simp only [dmul_apply, h2F, map_ofNat, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  have hmul2 : ∀ v, U.ex (fmul (dmul fun j => ((e j (((2 : 𝓞 F) : F)) : ℝ) : ℂ)) v) =
      U2.ex v ≫ lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act (2 : 𝓞 F)) := by
    intro v
    rw [eq_append v, fmul_append, hex2, hexU, dmul_apply, hu]
    simp
  have hM2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') =
      hermForm H (Fin.append x ((2 : ℂ) • y)) (Fin.append x' ((2 : ℂ) • y')) := by
    intro x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P ((2 : 𝓞 F) • c)) (X.P c) (X.isLB _) (X.isLB c) _ _ U2 U H2 χ2
      H χ' hF2 hFU (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act (2 : 𝓞 F))) (fmul (dmul fun j => ((e j (((2 : 𝓞 F) : F)) : ℝ) : ℂ)))
      hmul2 (X.smul (2 : 𝓞 F) c) (Fin.append x y) (Fin.append x' y')
    rwa [fmul_append, fmul_append, h2] at this
  have hSc := hS U H χ' hexU hFU
  have hS2 := hS U2 H2 χ2 hex2 hF2
  have hA : ∀ x x', hermForm H (Fin.append x 0) (Fin.append x' 0) = 0 := by
    intro x x'
    have e1 := hM2 x 0 x' 0
    have e2 := hS2 x 0 x' 0
    have e3 := hM2 0 x 0 x'
    have e4 := hSc x 0 x' 0
    simp only [smul_zero] at e1
    have e5 : Fin.append (0 : Fin (Module.finrank ℚ F) → ℂ) ((2 : ℂ) • x) = (2 : ℂ) • Fin.append 0 x := by
      rw [← append_smul, smul_zero]
    have e6 : Fin.append (0 : Fin (Module.finrank ℚ F) → ℂ) ((2 : ℂ) • x') = (2 : ℂ) • Fin.append 0 x' := by
      rw [← append_smul, smul_zero]
    rw [e5, e6, hermForm_smul_left, hermForm_smul_right] at e3
    have hs : (star (2 : ℂ)) = 2 := by simp
    rw [hs] at e3
    have : hermForm H (Fin.append x 0) (Fin.append x' 0) =
        4 * hermForm H (Fin.append x 0) (Fin.append x' 0) := by
      calc _ = hermForm H2 (Fin.append x 0) (Fin.append x' 0) := e1.symm
        _ = hermForm H2 (Fin.append 0 x) (Fin.append 0 x') := e2
        _ = 2 * (2 * hermForm H (Fin.append 0 x) (Fin.append 0 x')) := e3
        _ = 4 * hermForm H (Fin.append x 0) (Fin.append x' 0) := by rw [e4]; ring
    linear_combination (-1/3 : ℂ) * this
  have hA2 : ∀ y y', hermForm H (Fin.append 0 y) (Fin.append 0 y') = 0 := by
    intro y y'
    rw [← hSc y 0 y' 0]
    exact hA y y'
  have hBC : ∀ x y', hermForm H (Fin.append 0 x) (Fin.append y' 0) = hermForm H (Fin.append x 0) (Fin.append 0 y') :=
    fun x y' => (hSc x 0 0 y').symm
  have hdiag : ∀ z, U.ex (fdiag _ z) = u.ex z ≫ lift (𝟙 X.A) (𝟙 X.A) := by
    intro z
    rw [fdiag_apply, hexU]
    simp
  have hdLB : (X.diag c).IsLB := LB.isLB_pull (X.isLB c) _
  have hD := hermForm_eq_of_lbIso_pull X.A (X.A ⊗ X.A) (X.diag c) (X.P c) hdLB (X.isLB c) _ _ u U Hm χ H χ'
    (isFactorAH_of_isAH hAH) hFU (lift (𝟙 X.A) (𝟙 X.A)) (fdiag _) hdiag (by unfold Obj.diag; exact GlobalTheory.lbIso_refl hdLB)
  have hB : ∀ z w, hermForm Hm z w = 2 * hermForm H (Fin.append z 0) (Fin.append 0 w) := by
    intro z w
    rw [hD, fdiag_apply, fdiag_apply, herm_append H z z w w, hA, hA2, hBC]
    ring
  intro x y x' y'
  rw [hB, hB, herm_append H x y x' y', hA, hA2, hBC]
  ring
