import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem exists_gen_pfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), y ^ p = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), κ.IsGen → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), τ.IsGen → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p := by
  intro E _ _ _ H X0 t k _ x p y hy κ hκ τ hτ
  have hpow : (fst (Tm x p) t.G ≫ y) ^ p = 1 := by
    have e := map_pow (preHom (fst (Tm x p) t.G)) y p
    rw [hy, map_one] at e
    exact e.symm
  have e₁ : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫ cφG t ![fst t.G t.G ^ p, snd t.G t.G] I =
      (psum t.G ![1, snd (Tm x p) t.G] I.down).left := by
    intro I
    refine congrArg (fun q => q.left) ((psum_hom (preHom (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G))) _ I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_)))
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      refine (map_pow (preHom _) _ p).trans ?_
      simpa [preHom] using hpow
    · simp [preHom]
  have e₂ : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫ cφG t ![fst t.G t.G, snd t.G t.G] I =
      (psum t.G ![fst (Tm x p) t.G ≫ y, snd (Tm x p) t.G] I.down).left := by
    intro I
    refine congrArg (fun q => q.left) ((psum_hom (preHom (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G))) _ I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_)))
    fin_cases i <;> simp [preHom]
  refine Exists.elim (exists_gen t.PP.isLB (φ' := ![pa t.G x y, pb t.G x p]) (ε' := ![(p : ℤ), -(p : ℤ)]) ?_
    (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ κ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left))
      (genPowG t _ _ (LB.pullGen t.PP.L _ _ τ (fst (Tm x p) t.G).left) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hκ _))
      (GermD.genPowG_isGen t _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _) p))) ?_
  · intro U _ f
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    have h₁ : ∏ a₁ : ULift.{0} (Finset (Fin 2)), f ((lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫
          cφG t ![fst t.G t.G ^ p, snd t.G t.G] a₁) ^ (-cε 2 a₁) =
        (∏ I : ULift.{0} (Finset (Fin 2)), f (psum t.G ![1, snd (Tm x p) t.G] I.down).left ^
          ((-1 : ℤ) ^ (2 - I.down.card)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [e₁ I, zpow_neg]
      rfl
    have h₂ : ∏ a₂ : ULift.{0} (Finset (Fin 2)), f ((lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫
          cφG t ![fst t.G t.G, snd t.G t.G] a₂) ^ (- -((p : ℤ) * cε 2 a₂)) =
        (∏ I : ULift.{0} (Finset (Fin 2)), f (psum t.G ![fst (Tm x p) t.G ≫ y, snd (Tm x p) t.G] I.down).left ^
          ((-1 : ℤ) ^ (2 - I.down.card))) ^ (p : ℤ) := by
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [e₂ I, neg_neg, _root_.mul_comm, zpow_mul]
      rfl
    have h₃ : (fst (Tm x p) t.G).left ≫ (1 : Tm x p ⟶ t.G).left = (1 : Tm x p ⊗ t.G ⟶ t.G).left :=
      by
        have e : fst (Tm x p) t.G ≫ (1 : Tm x p ⟶ t.G) = 1 := map_one (preHom (fst (Tm x p) t.G))
        rw [← Over.comp_left, e]
    have h₄ : pa t.G x y = (fst (Tm x p) t.G ≫ y * snd (Tm x p) t.G).left := rfl
    have h₅ : pb t.G x p = (snd (Tm x p) t.G).left := rfl
    rw [h₁, h₂, prod_cube₂, prod_cube₂, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_mul, h₃, h₄, h₅, ← Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rintro C ⟨hC, hv⟩
    refine ⟨C, hC, fun Z' r z J hJ => ?_⟩
    rw [hv Z' r z J hJ, val_mul hJ, val_inv, val_pull hJ, GermD.val_genPowG, val_pull hJ]

end GlobalTheory.CompanionTheory.Ar.Coc
