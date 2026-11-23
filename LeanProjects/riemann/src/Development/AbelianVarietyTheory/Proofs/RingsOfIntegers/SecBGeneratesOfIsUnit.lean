import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocalStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecBGenerates

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaLocalDomain

open GlobalTheory.IndivisibleSection

theorem vanish_of_terms_mem {R : Type} [CommRing R] [IsDomain R] {I I' : Ideal R} (hI : I ≤ I') {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α, ∃ a ∈ I' ^ (e + 1), ∃ f' : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom a (f α) f') (j) :
    ((fstG I' e G).left.app _).hom (σ.f j) = 0 := by
  have hle : I ^ (e + 1) ≤ I' ^ (e + 1) := Ideal.pow_right_mono hI _
  have hth : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)) ≫ thick R I e = thick R I' e := by
    simp only [thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (thickObj R I' e G).left ⟶ (thickObj R I e G).left, ρ ≫ fGl I G e = fGl I' G e :=
    ⟨pullback.lift (pullback.fst G.hom (thick R I' e))
      (pullback.snd G.hom (thick R I' e) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)))
      (by rw [Category.assoc, hth]; exact pullback.condition), pullback.lift_fst _ _ _⟩
  have hw : (ρ ≫ pGl U e) ≫ D.toPre.P.A.hom =
      pullback.snd G.hom (thick R I' e) ≫ spMap (Ideal.Quotient.mk (I' ^ (e + 1))) := by
    have w₁ : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
      (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
    rw [Category.assoc, w₁, ← Category.assoc, hρ]
    exact pullback.condition
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : (thickObj R I' e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hy' : (ρ ≫ fGl I G e) y ∈ U.LG.L.U jL := by rw [hρ]; exact Set.mem_iInter.1 hy 0
  have H := (hS _ ρ y J hJ).2 jL hy'
  have hz : ∀ α, sval (f α) (ρ ≫ pGl U e) y J = 0 := fun α => by
    obtain ⟨a, ha, f', hf'⟩ := h0 α
    have hc : cst ((ρ ≫ pGl U e) ≫ D.toPre.P.A.hom) y a = 0 := by
      rw [hw]
      refine (cst_comp _ _ y a).trans ?_
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, cst, map_zero]
      exact gs_zero _ y ⊤ trivial
    rw [sval_of_secIsMul hf' _ y hJ, hc, zero_mul]
  rw [Finset.sum_eq_zero fun α _ => by rw [hz α, zero_mul], hρ] at H
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_zero (𝟙 _) y _ hy).symm)
  rw [Category.id_comp]
  exact (Units.mul_right_eq_zero _).1 H

theorem secBGenerates_of_isUnit {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {k : ℕ}
    {α : D.toPre.X} {b g : D.toPre.SecB k α} (hb : SecBGenerates (D := D) k α b) {a₀ : R} (hu : IsUnit a₀)
    (ha₀ : SecIsMul D.toPre.P.A.hom a₀ g b) : SecBGenerates (D := D) k α g := by
  have hL := D.toPre.P.isLB
  have tr : ∀ {a c : R} {s t w : D.toPre.SecB k α}, SecIsMul D.toPre.P.A.hom a s t →
      SecIsMul D.toPre.P.A.hom c t w → SecIsMul D.toPre.P.A.hom (a * c) s w := fun h h' =>
    secIsMul_of_sval hL fun y J hJ => by
      rw [sval_of_secIsMul h _ y hJ, sval_of_secIsMul h' _ y hJ, Category.id_comp, cst_mul', _root_.mul_assoc]
  obtain ⟨u, rfl⟩ := hu
  have hinv : SecIsMul D.toPre.P.A.hom (↑u⁻¹ : R) b g := secIsMul_of_sval hL fun y J hJ => by
    rw [sval_of_secIsMul ha₀ _ y hJ, Category.id_comp, ← _root_.mul_assoc, ← cst_mul', Units.inv_mul, cst_one',
      _root_.one_mul]
  intro s
  obtain ⟨a, ha, hau⟩ := hb s
  refine ⟨a * ↑u⁻¹, tr ha hinv, fun a' ha' => ?_⟩
  rw [← hau _ (tr ha' ha₀), Units.mul_inv_cancel_right]

theorem main : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (s : H0 U.LG.L 1), NonzeroOnSpecial U s → IsTheta U s := by
  intro hLaws R _ _ _ _ I hI D A G _ _ U s hs
  obtain ⟨sK, hsK⟩ := exists_pull_val U.LG.isLB s (pullback.fst G.hom (jK R))
    (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by simp only [Category.comp_id])
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨g, hg, hgE⟩ := GlobalTheory.T.expansion_integralSection_integral_noetherianLocal R I hI D A G U.toUnifPre 1 s sK
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => (hsK _ _ y J hJ).symm) E hE
  obtain ⟨b, hb⟩ := exists_secBGenerates hLaws.secBaseChange R I D
  obtain ⟨a, ha, -⟩ := hb (g 0)
  have hu : IsUnit a := by
    by_contra hn
    obtain ⟨j, hj⟩ := hs
    refine hj (vanish_of_terms_mem hI U.toUnifPre 0 1 s g (hg 0) (fun α => ?_) j)
    rw [zero_add, pow_one]
    by_cases hα : α = 0
    · subst hα
      exact ⟨a, hn, b, ha⟩
    · obtain ⟨c, hc, g', hg'⟩ := GlobalTheory.LevelOneIdeal.main hLaws.globalFns R I D E g hgE α hα
      exact ⟨c, hI hc, g', hg'⟩
  exact fun e => ⟨g, hg e, secBGenerates_of_isUnit hb hu ha⟩

end GlobalTheory.ThetaLocalDomain
