import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitFiniteExtensionClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitPullbackThetaSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLatticeMovesByRingActionCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.UTraitLab

theorem q_eq_of_isMonomial : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (lb : u.Lab) (ϖ : u.V) (be : LinearMap.BilinForm ℤ u.D.toPre.X), ϖ ≠ 0 → IsMonomial u.D.toPre ![ϖ] ![be] → ∀ χ, lb.q χ = -Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ * (be χ χ : ℝ) / 2 := by
  intro o Ω _ _ _ S ρ p _ y₀ u lb ϖ be hϖ hmono χ
  obtain ⟨v, n, hn, hc⟩ := hmono χ
  obtain ⟨jc, hjc, hval⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre χ _ hc
  have hq := lb.q_eq χ jc hjc
  rw [hval] at hq
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hq
  have hunit : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ = 1 := by
    have h1 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ ≤ 1 := (u.norm_le _).2 ⟨_, rfl⟩
    have h2 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ ≤ 1 :=
      (u.norm_le _).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
  set a := ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ with ha
  have hapos : 0 < a := by
    rw [ha, norm_pos_iff]
    intro h0
    have h1 : algebraMap u.V (FractionRing u.V) ϖ = 0 :=
      (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (by rw [h0, map_zero])
    exact hϖ (IsFractionRing.injective u.V (FractionRing u.V) (by rw [h1, map_zero]))
  have hl : -lb.q χ = (n 0 : ℝ) * Real.log a := by
    rw [← Real.log_pow, hq, Real.log_exp]
  have hb : (be χ χ : ℝ) = 2 * (n 0 : ℝ) := by
    have := hn 0
    simp only [Matrix.cons_val_zero] at this
    rw [this]; push_cast; ring
  rw [hb]
  linarith

end GlobalTheory.UPoinc.UTraitLab

namespace GlobalTheory.UPoinc

open GlobalTheory.UPoinc.UTraitLab in

theorem uTraitLabels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₁ (toRat S.R (algebraMap o S.R a))‖ ≤ 1) → ∃ (u : ρ.UTest p (y₁.comp (toRat S.R))) (lb : u.Lab) (j : u.D.toPre.X ≃+ T.P.D.toPre.X), (∀ χ, lb.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (T.be (j χ) (j χ) : ℝ) / 2) ∧ ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y) := by
  intro E _ _ _ H Dw hpq l Xo cf o Ω _ _ _ _ S ρ u' G _ α β hα hβ hL p _ y₁ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hbe⟩ := GlobalTheory.T.exists_unitaryTrait_finiteExtension_classicalPoint E H Dw l Xo cf o Ω S u' p y₁ T ι hι hsp
  obtain ⟨φ, cart, lb, hact⟩ := GlobalTheory.T.exists_unitaryTrait_pullback_thetaSystem E H Dw l Xo cf o Ω S ρ u' G inferInstance α β hα hβ hL T' yK hy'
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p (y₁.comp (toRat S.R)) :=
    { V := T'.V, complete := T'.cdvr.2.1, norm_le := hι', yK := yK.comp (toRat S.R),
      fac := by rw [← RingHom.comp_assoc, RingHom.algebraMap_toAlgebra, hfac],
      A := T'.P.A, φ := φ, cart := cart, lb := lb, G := T'.t.G, semi := T'.t.semi, D := T'.P.D, U := T'.P.U }
  obtain ⟨lab⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p _ u
    hint
  refine ⟨u, lab, e.toAddEquiv, ?_, ?_⟩
  · intro χ
    have hq := q_eq_of_isMonomial o Ω S ρ p _ u lab T'.ϖ T'.be T'.irr.ne_zero T'.mono χ
    rw [hq]
    change -Real.log ‖ι' (algebraMap T'.V _ T'.ϖ)‖ * ((T'.be χ χ : ℤ) : ℝ) / 2 =
      -Real.log ‖ι (algebraMap T.V _ T.ϖ)‖ * ((T.be (e χ) (e χ) : ℤ) : ℝ) / 2
    rw [hϖ, Real.log_pow, hbe χ χ]
    push_cast
    ring
  · intro m a pk pk' x x' w w' hm h1 h2 hw hw' hww
    have hx : x' = x ≫ T'.P.oA.act a := hact _ x x' w w' a hw hw' hww
    obtain ⟨z, hz⟩ := GlobalTheory.T.torsionLattice_moves_by_ringAction_completeDVR E H T'.V T'.cdvr T'.t T'.P (PadicAlgCl p) m a pk pk' x x' hm h1 h2 hx
    exact ⟨e z, by simp [hz, map_add, map_nsmul]⟩

end GlobalTheory.UPoinc
