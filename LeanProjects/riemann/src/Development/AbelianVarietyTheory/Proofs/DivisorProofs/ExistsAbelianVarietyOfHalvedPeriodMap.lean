import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HalvedPeriod

open GlobalTheory.CechPic GlobalTheory.Models GlobalTheory.ZM

theorem exists_abelian_of_isPeriod : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D' : PLat O bar) (Q : D'.La →+ (Fin g → ℂ)) (E₁ : LinearMap.BilinForm ℤ D'.La), IsPeriod D' ρ Q → D'.EF = (2 : ℤ) • E₁ → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (_ : IsCommMonObj A) (act : OActN O A) (P : LB (G2 A).left) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ IsExp (𝟙 (Sp ℂ)) e ∧ (∀ z, e z = 1 ↔ z ∈ Q.range) ∧ (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ act.act a) ∧ (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) := by
  intro O _ bar g ρ D' Q E₁ hP hE
  obtain ⟨hlin, -, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  let Λ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  have hmem : ∀ z, z ∈ Λ ↔ z ∈ Q.range := fun z => Iff.rfl
  have hΛd : DiscreteTopology Λ := hdisc
  have hΛs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
    have e : (Λ : Set (Fin g → ℂ)) = Set.range Q := by
      ext z; exact AddMonoidHom.mem_range
    rw [e]; exact hspan
  let H₁ : Matrix (Fin g) (Fin g) ℂ := (2⁻¹ : ℂ) • Hm
  have hH₁ : H₁.IsHermitian := by
    unfold Matrix.IsHermitian at hHm ⊢
    simp only [H₁, Matrix.conjTranspose_smul, hHm, star_inv₀, star_ofNat]
  have hH₁v : ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁ *ᵥ star w = 2⁻¹ * hermForm Hm z w := fun z w => by
    simp only [H₁, hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hH₁pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁ *ᵥ star z).re := fun z hz => by
    rw [hH₁v]
    have := hpos z hz
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.re_ofReal_mul]
    positivity
  have hH₁int : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ H₁ *ᵥ star l').im = n := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    refine ⟨E₁ x y, ?_⟩
    have h := him x y
    rw [hE] at h
    rw [hH₁v]
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.im_ofReal_mul, h]
    simp
  obtain ⟨A, _, hA, hdim, M, u, χ, hM, hu, hAH⟩ :=
    GlobalTheory.riemann_polarised_torus g Λ H₁ hΛd hΛs hH₁ hH₁pos hH₁int
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ Q.range := fun z => (u.ker z).trans (hu z)
  obtain ⟨u', χ', hex, hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u H₁ χ hM
    (GlobalTheory.TorusRM.isFactorAH_of_isAH hAH)
  have h2H : (2 : ℂ) • H₁ = Hm := by simp only [H₁, smul_smul]; norm_num
  rw [h2H] at hF'
  have hAH' : u'.IsAH Hm χ' := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' (fun z hz => hpos z hz)
  have hker' : ∀ z, z ∈ u'.Λ ↔ z ∈ Q.range := fun z => by rw [← u'.ker, hex, hker]
  have hPLB := GlobalTheory.FullSiegel.isLB_lam hM
  have hΔLB := pull_isLB hPLB (lift (𝟙 A) (𝟙 A)).left

  have hid : IsGrpPullback A A (𝟙 _) (𝟙 A.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl A) (inferInstanceAs (IsMonHom (𝟙 A)))
  have htb := GlobalTheory.TorusTransfer.tangent_bijective u hdim
  have hexp : IsExp (𝟙 (Sp ℂ)) u.ex :=
    GlobalTheory.PointUnif.isExp_push hid u htb.1 htb.2 (MulEquiv.refl _) (fun x => (Category.comp_id _).symm)

  have hρΛ : ∀ a, ∀ x ∈ u.Λ, Matrix.mulVecLin (ρ a) x ∈ u.Λ := by
    intro a x hx
    rw [hu, hmem] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [Matrix.mulVecLin_apply, hlin]⟩
  choose ψ hψ hlift using fun a =>
    GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA hdim M u (Matrix.mulVecLin (ρ a)) (hρΛ a)
  haveI : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hA.smooth
  have hext : ∀ f f' : A ⟶ A, (∀ z, u.ex z ≫ f = u.ex z ≫ f') → f = f' := fun f f' h =>
    GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u.ex_onto x
      exact h z
  let act : OActN O A :=
    { act := ψ
      hom := hψ
      one := hext _ _ fun z => by
        rw [← hlift, map_one, Matrix.mulVecLin_one, LinearMap.id_apply, Category.comp_id]
      mul := fun a b => hext _ _ fun z => by
        rw [← hlift, ← Category.assoc, ← hlift, ← hlift]
        congr 1
        simp only [Matrix.mulVecLin_apply, map_mul, Matrix.mulVec_mulVec]
      add := fun a b => hext _ _ fun z => by
        rw [← hlift, comp_mul, ← hlift, ← hlift, ← u.ex_add]
        congr 1
        simp [Matrix.add_mulVec] }
  refine ⟨A, inferInstance, inferInstance, act, abelian₂ A M, u.ex, hA, hdim, hPLB, ?_, ?_, GlobalTheory.FullSiegel.lam_symm hM,
    GlobalTheory.LefschetzAmple.relAmple_of_isAH g A hA _ u' Hm χ' hΔLB hAH', hexp, hker, fun a z => ?_, ?_⟩
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_left _ _))
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_right _ _))
  · rw [← Matrix.mulVecLin_apply]; exact hlift a z
  · intro k a b c hk hc
    have h := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hΔLB g u' Hm χ' hAH' k (Q a) (Q b) c hk
      ((hker' _).2 ⟨a, rfl⟩) ((hker' _).2 ⟨b, rfl⟩) (by
        rw [hc]
        have e : (Q a ⬝ᵥ Hm *ᵥ star (Q b)).im = (D'.EF a b : ℝ) := him a b
        rw [e]; push_cast; rfl)
    rw [hex] at h
    exact h

end GlobalTheory.HalvedPeriod
