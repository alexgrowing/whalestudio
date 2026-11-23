import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLatt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianIsogenyExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (u v u' v' : T ⟶ A) : lift u v * lift u' v' = lift (u * u') (v * v') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst]
  · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd]

theorem one_eq_lift {T : Over S} : (1 : T ⟶ A ⊗ A) = lift (1 : T ⟶ A) 1 := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.one_comp, lift_fst]
  · rw [MonObj.one_comp, lift_snd]

theorem lam_diag (p : Pic (A ⊗ A).left)
    (hmul : ∀ {T : Over S} (X X' Y : T ⟶ A ⊗ A), lam p (X * X') Y = lam p X Y + lam p X' Y)
    (r₁ : ∀ {T : Over S} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left p = 0)
    (r₂ : ∀ {T : Over S} (u : T ⟶ A), pull (lift u (1 : T ⟶ A)).left p = 0)
    {T : Over S} (a b : T ⟶ A) :
    lam (pull (lift (𝟙 A) (𝟙 A)).left p) a b = pull (lift a b).left p + pull (lift b a).left p := by
  rw [lam_pull, comp_lift, comp_lift]
  simp only [Category.comp_id]
  have ha : lift a a = lift a (1 : T ⟶ A) * lift 1 a := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hb : lift b b = lift b (1 : T ⟶ A) * lift 1 b := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hmul' : ∀ (X Y Y' : T ⟶ A ⊗ A), lam p X (Y * Y') = lam p X Y + lam p X Y' := fun X Y Y' ↦ by
    rw [lam_comm, hmul, lam_comm, lam_comm p Y']
  rw [ha, hb, hmul, hmul', hmul']
  simp only [lam, lift_mul_lift, one_eq_lift, _root_.mul_one, _root_.one_mul, r₁, r₂]
  abel

end GlobalTheory.KerPoincare

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_pow_eq_one_of_kernel : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
      (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q →
    Submodule.span ℝ (Set.range Q) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Q.range) →
    (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
    ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A,
      (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) →
      ∃ k : ℕ, 0 < k ∧ x ^ k = 1 := by
  intro A _ _ g hA hsm P hP hr₁ hr₂ hsym hamp e La _ Q EF he _ _ _ _ x hx
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hsm (𝟙 _) e he
  obtain ⟨L₀, u₀, -⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, -, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have pos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hAH.1 hAH.2.1 hAH.2.2
  obtain ⟨PP, ψ, ρ, N, hN, hψ, hρ, h₁, h₂, h₃⟩ := GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL
    (GlobalTheory.TorusRM.isAH_of_isFactorAH hAH pos)
  refine ⟨N * N, Nat.mul_pos hN hN,
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL PP ψ ρ N hψ hρ h₁ h₂ h₃ _ x ?_⟩
  have hG : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ (A ⊗ A) hG P hP
  have r₁ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift (1 : T ⟶ A) v = v ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₁, map_zero]
  have r₂ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift v (1 : T ⟶ A)).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift v (1 : T ⟶ A) = v ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₂, map_zero]
  have e₀ : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have hsymm : ∀ {T : Over (Sp ℂ)} (u v : T ⟶ A),
      pull (lift u v).left (cls P hP) = pull (lift v u).left (cls P hP) := fun {T} u v ↦ by
    conv_lhs => rw [e₀]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hxA : pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left (cls P hP) = 0 := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 hx
  refine (cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hL _ _) _)).1
    ((GlobalTheory.RealMult.Elliptic.cls_pull_lam hL _ _ _).trans ?_)
  rw [cls_pull hP _ hL,
    lam_diag (cls P hP) (fun X X' Y ↦ lam_mul_left hP hΘ X X' Y) r₁ r₂, hsymm, hxA, add_zero]

end GlobalTheory.KerPoincare
