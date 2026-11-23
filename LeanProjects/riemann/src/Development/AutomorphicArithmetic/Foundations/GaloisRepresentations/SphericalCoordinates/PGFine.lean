import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem diag_comp' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂) :
    (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left := by
  apply pullback.hom_ext
  · have h1 := hs.1
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (fst A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := hs.2
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (snd A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

private theorem diag_lbIso' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂)
    {P' : LB (G2 A').left} {P : LB (G2 A).left} (hP' : P'.IsLB) (hP : P.IsLB) (hpol : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  have h₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp hpol _ (diag_comp' hs).symm
  have h₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP _)) φ rfl
  exact LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) h₁ h₂.symm

theorem gFine_of : GFine := by
  intro p _ D b gb N M X ρ h hL f hf hG hpts hfine
  obtain ⟨φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ := hG
  have hX : SmoothOfRelativeDimension D.g X.univ.A.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} D.g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.g) hcart.1 h
  have hL' : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB := pull_isLB X.univ.isLB _
  have hB := diag_lbIso' hsq X.univ.isLB M.univ.isLB hpol
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap, Sp]
  have key := fun (D' : PLat D.O D.inv) (t : D.La → D'.La) P (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ)) =>
    GlobalTheory.T.uniformisationAt_correspond_of_cartesian D.O D.inv D.g ρ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) D.La (M.univ.fam h hL) (gfam X.univ hX hL') N f φA
      hcart hact hB heta D' t P y hy (by
        show (y ≫ f) ≫ M.s = _
        rw [Category.assoc, hf, hy])
  refine ⟨hX, hL', ?_, ?_, ?_⟩
  · intro (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ))
    have hy' : (y ≫ f) ≫ M.s = spMap (RingHom.id ℂ) := by rw [Category.assoc, hf, hy]
    obtain ⟨D', t, P, e, hC, hU⟩ := hfine.pts (y ≫ f) hy'
    obtain ⟨e', he', -⟩ := (key D' t P y hy).2 e hU
    exact ⟨D', t, P, e', hC, he'⟩
  · intro D' t P hC hP
    obtain ⟨y', e, hU⟩ := hfine.occ D' t P hC hP
    obtain ⟨y, ⟨hy, rfl⟩, -⟩ := hpts y' (hU.1)
    obtain ⟨e', he', -⟩ := (key D' t P y (hy.trans hid.symm)).2 e hU
    exact ⟨y, e', he'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w u hw hQ
    obtain ⟨e₁, he₁, -⟩ := (key D' t P y hU.1).1 e hU
    obtain ⟨e₂, he₂, -⟩ := (key D'' t' P' y' hU'.1).1 e' hU'
    have hyy := hfine.sep D' D'' t t' P P' (y ≫ f) (y' ≫ f) e₁ e₂ he₁ he₂ w u hw hQ
    obtain ⟨z, -, huniq⟩ := hpts (y ≫ f) he₁.1
    have a₁ : y = z := huniq y ⟨hU.1.trans hid, rfl⟩
    have a₂ : y' = z := huniq y' ⟨hU'.1.trans hid, hyy.symm⟩
    rw [a₁, a₂]

end UpperTheory.Gal.W2
