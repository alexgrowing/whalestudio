import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem left_comp_of_comp {S : Scheme.{0}} {X Y Z : Over S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) :
    f.left ≫ g.left = h.left := by
  rw [← Over.comp_left, e]

theorem exists_birigidified_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b M S s o A' _ _ ψ hψ m P₀ hP₀ H
  let φ : Fin 4 → ((G2 A').left ⟶ (G2 A').left) := ![𝟙 _, (lift (fst A' A') (1 : G2 A' ⟶ A')).left,
    (lift (1 : G2 A' ⟶ A') (snd A' A')).left, (lift (1 : G2 A' ⟶ A') (1 : G2 A' ⟶ A')).left]
  let ε : Fin 4 → ℤ := ![1, -1, -1, 1]
  have hε : ε 0 = 1 ∧ ε 1 = -1 ∧ ε 2 = -1 ∧ ε 3 = 1 := ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨LB.LinComb P₀ φ ε, DVR.linComb_isLB P₀ hP₀ φ ε, ?_, ?_, ?_⟩
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 0 = (lift (1 : A' ⟶ A') (𝟙 A')).left := Category.comp_id _
    have e1 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 1 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (𝟙 A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_right_comm _ _ (GlobalTheory.PrimNorm.cls P₀ _)⁻¹, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 0 = (lift (𝟙 A') (1 : A' ⟶ A')).left := Category.comp_id _
    have e1 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 1 = (lift (𝟙 A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · haveI := hψ
    let ρ : Fin 4 → ((G2 o.A).left ⟶ (G2 o.A).left) := ![𝟙 _, (lift (fst o.A o.A) (1 : G2 o.A ⟶ o.A)).left,
      (lift (1 : G2 o.A ⟶ o.A) (snd o.A o.A)).left, (lift (1 : G2 o.A ⟶ o.A) (1 : G2 o.A ⟶ o.A)).left]
    have hsq : ∀ k, sq2 ψ ≫ φ k = ρ k ≫ sq2 ψ := by
      intro k
      fin_cases k
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      all_goals
        refine (left_comp_of_comp rfl).trans ((left_comp_of_comp ?_).symm)
        apply CartesianMonoidalCategory.hom_ext <;> simp
    have hP := o.isLB
    have cls1 : ∀ (r : (G2 o.A).left ⟶ (G2 o.A).left),
        GlobalTheory.MulPull.HasGen o.P (fun _ : PUnit => r) (fun _ => 1) → GlobalTheory.PrimNorm.cls o.P r = 1 := by
      intro r h
      have := (GlobalTheory.PrimNorm.hasGen_iff hP _ _).1 h
      rwa [Fintype.prod_unique, zpow_one] at this
    have h1 : GlobalTheory.PrimNorm.cls o.P (ρ 1) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A).left
      have e : (fst o.A o.A).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 1 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h2 : GlobalTheory.PrimNorm.cls o.P (ρ 2) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left)
        (ε := fun _ => 1) o.rig₁ (snd o.A o.A).left
      have e : (snd o.A o.A).left ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left = ρ 2 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h3 : GlobalTheory.PrimNorm.cls o.P (ρ 3) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left
      have e : (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 3 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have L1 : (lbPow o.P m).IsLB := DVR.linComb_isLB o.P hP _ _
    have L2 : (LB.LinComb (lbPow o.P m) ρ ε).IsLB := DVR.linComb_isLB _ L1 _ _
    have L3 : (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε).IsLB := DVR.linComb_isLB _ hP₀ _ _
    have L4 : ((LB.LinComb P₀ φ ε).pull (sq2 ψ)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hP₀ _ _) _ _
    have I1 : LBIso (lbPow o.P m) (LB.LinComb (lbPow o.P m) ρ ε) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP (fun _ : Fin m => 𝟙 _) (fun _ => 1) ρ ε
        (fun _ : Fin m => 𝟙 _) (fun _ => 1) ?_)
      simp only [Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Fin.prod_univ_four, h1, h2, h3, one_pow, one_zpow, _root_.mul_one, hε.1]
      rfl
    obtain ⟨w, hw⟩ := H
    have I2 : LBIso (LB.LinComb (lbPow o.P m) ρ ε) (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) :=
      iso_linComb ((isGen_iff w).1 hw) ρ ε
    have I3 : LBIso (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) ((LB.LinComb P₀ φ ε).pull (sq2 ψ)) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP₀ φ ε (fun _ : PUnit => sq2 ψ) (fun _ => 1)
        (fun k => ρ k ≫ sq2 ψ) ε ?_)
      rw [Fintype.prod_unique, zpow_one]
      exact Finset.prod_congr rfl fun k _ => by rw [hsq k]
    exact LBIso.trans L1 L2 L4 I1 (LBIso.trans L2 L3 L4 I2 I3)
end GlobalTheory.UPel.HT.Hecke
