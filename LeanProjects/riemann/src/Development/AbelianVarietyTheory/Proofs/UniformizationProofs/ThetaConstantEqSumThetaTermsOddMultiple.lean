import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperatorStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaSum

theorem exists_gen_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hσ : σ.IsGen) (m : ℕ) (a : G ⟶ G)
    (ha : a = 𝟙 G ^ m) :
    ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 _, a.left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen := by
  subst ha
  have hL := L.isLB
  have hcube : MulPull.HasGen L.L (thφ G (x3 G)) thε := ⟨c.t, c.isGen⟩
  have hrig : MulPull.HasGen L.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) := ⟨L.rig, L.rigGen⟩
  have hsym : MulPull.HasGen L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨σ, hσ⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull G.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) m
  refine h.of_formEq hL fun U _ h => ?_
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Nat.cast_pow]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem coef_congr {k : ℕ} (g : GtPtF D F) {w w' : Frm D F k g.b} (hw : w.IsGen)
    (h : ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g w' χ = coef s g w χ := by
  refine CoefBasic.coef_eq fun z J hJ => ?_
  rw [h z J hJ]
  exact CoefBasic.isCoef_coef g hw χ s z J hJ

theorem zero_isAdd {o : GtPtF D F} (ho : o.IsZero) (g : GtPtF D F) : o.IsAdd g g := by
  obtain ⟨hb, hv⟩ := (isZero_iff o).1 ho
  refine (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.one_mul], fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [hv χ y J hJ, hb, C.face₂, _root_.mul_one, _root_.one_mul]

theorem theta_const_sum : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∀ w, TXFrame (m ^ 2) p w → ∀ (g' : GtPtF D.toPre F), GtPtF.IsNsmul m p.g g' → ∀ (κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)), Normd κ → ∀ w' : Frm D.toPre F 1 g'.b, w'.IsGen → (∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J) → SumF I F (coef ϑ g' w') c ∧ ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero → FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧ ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ w₀ ρ hN th ϑ hϑ m hm p x t c hx hc w hw g' hg' κ hκ w' hw' hv
  obtain ⟨α, s₁, θ, hα, hαn, htw, hθ, hact, hval⟩ := hc
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hm0)
  have hbij := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F (m ^ 2) hm2 w₀ hN.1
  obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
  obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 m
  have hsm : Function.Injective fun χ : D.toPre.X => m • χ := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  have hpull := (GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hinj (m ^ 2) 1 le_rfl hm2
    (exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
    (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hϑ hσ₁ htw
  rw [hEB] at hpull
  obtain ⟨q₁, q₂⟩ := hpull κ hκ p.g g' ((hEact F p.g g').2 hg') w w' hw.1 hw' hv
  have main : ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero →
      FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧
        ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
    intro s hs o w₁ ho hw₁
    have hΦ := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hL R I hI D A G hG U F (m ^ 2) hm.pow p x hx θ hθ w₀ hN.1 w hw s₁ t σ₁ s hσ₁ hs hact
    obtain ⟨ω₁, hω₁, hωv, hco⟩ := CoefPhi.coef_phi hL R I hI D F (m ^ 2) hm2 p w hw.1 o p.g (zero_isAdd ho p.g) w₁ hw₁.1
    have key : ∀ a, coef s o w₁ (a + p.y) = coef σ₁ p.g w a := fun a =>
      (hco 1 (m ^ 2) le_rfl (Nat.mul_one _).symm p (one_nsmul _).symm rfl w w₁ ω₁
        ⟨hw.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩
        ⟨hω₁, fun _ _ _ => (pow_one _).symm⟩ σ₁ s hΦ a).trans (coef_congr p.g hw.1 (hωv ho hw₁) σ₁ a)
    refine ⟨fun χ => by rw [key, ← hEh, q₁], fun β hβ => ?_⟩
    rw [← sub_add_cancel β p.y, key]
    refine q₂ _ ?_
    rintro ⟨χ, e⟩
    exact hβ χ (by rw [← hEh, e, sub_add_cancel])
  refine ⟨?_, main⟩
  obtain ⟨s, hs, -⟩ := hbij.1 t
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (CoefBasic.coef_basic R D.toPre F (m ^ 2) o).2.1 ((isZero_iff o).1 ho).1
  obtain ⟨r₁, r₂⟩ := main s hs o w₁ ho hw₁
  have hsum := (EvalZero.value_at_origin hL R I hI D A G hG U F).2.2 w₀ ρ hN (m ^ 2) t s hs o w₁ ho hw₁ c hval
  have := ((AdicSum.sumF_calculus R I hI F D.toPre.X (coef s o w₁) (coef s o w₁) c c).2.2 D.toPre.X
    (fun χ => m • χ + p.y) (fun a b h => hsm (add_right_cancel h))
    (fun β hβ => r₂ β fun χ e => hβ ⟨χ, e.symm⟩)).2 hsum
  rwa [show (coef s o w₁ ∘ fun χ => m • χ + p.y) = coef ϑ g' w' from funext r₁] at this

end GlobalTheory.UT.ThetaSum
end
