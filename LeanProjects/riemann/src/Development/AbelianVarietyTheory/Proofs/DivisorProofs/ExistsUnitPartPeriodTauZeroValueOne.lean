import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTauZero

theorem exists_isUnitTau_zero_val_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  have hF : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim
      (K' := Fin 4) ![(P.D.toPre.c (mu + 0)).left, (P.D.toPre.c mu).left, (P.D.toPre.c 0).left, (P.D.toPre.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [add_zero, Finset.univ_eq_empty, Finset.prod_empty, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    simp [Matrix.vecHead, Matrix.vecTail]
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen P.D.toPre.P.isLB hF (LB.oneGen P.D.toPre.P.L) (LB.isGen_oneGen _)
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨τ₀, ⟨hτ, 1, ?_, fun zz J hJ => ?_⟩, h1⟩
  · simp
  · have hB : P.D.toPre.TauBimult := P.D.tau_bimult
    rw [h1 _ _ zz J hJ, _root_.mul_one]
    have vτ : val (P.D.toPre.tau mu 0) (𝟙 _) zz J =
        val (P.D.toPre.psi (mu + 0)) (𝟙 _) zz J * (val (P.D.toPre.psi mu) (𝟙 _) zz J)⁻¹ *
          (val (P.D.toPre.psi 0) (𝟙 _) zz J)⁻¹ * (val P.D.toPre.rigK (𝟙 _) zz J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have vρ : val P.D.toPre.rigK (𝟙 _) zz J = val P.D.toPre.rig (jK _) zz J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ a : P.D.toPre.X, a = mu → val (P.D.toPre.psi a) (𝟙 _) zz J = val (P.D.toPre.psi mu) (𝟙 _) zz J := by
      rintro a rfl; rfl
    have h0 := GlobalTheory.PsiZero.val_psi_zero hB hJ
    have hu : unitOn (1 : (FractionRing (ChartRing k m d))ˣ) = 1 := map_one _
    rw [vτ, hp _ (add_zero mu), h0, vρ, hu, map_one, mul_inv_cancel, _root_.one_mul, inv_inv, mul_inv_cancel]

end GlobalTheory.UnitTauZero
