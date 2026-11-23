import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_xfLevel_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.Mum.Base R)
    (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R)))
    (hI₀ : GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hL₂ : Laws2 := hLL.2.1
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (AlgebraicClosure (FractionRing R)) :=
    charZero_of_injective_ringHom (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).injective
  have hB := C.P.D.tau_bimult
  have he := C.P.D.psi_even
  let s : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F := IsAlgClosed.lift
  have hs : s.toRingHom.comp (algebraMap (FractionRing R) _) = algebraMap (FractionRing R) F := s.comp_algebraMap
  have hj : spMap s.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing R)) = jFK (R := R) F := by
    rw [jFK, jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
  let I := GlobalTheory.ArcExt.tateExt s.toRingHom hs hB hL I₀ (GlobalTheory.ArcOfModel.weilQkIs_qkExt hL hL₂ he hB s.toRingHom hs)
  have hext : ∀ n a, QkExt s.toRingHom (I₀.ev n a) (I.ev n a) := fun n a =>
    (GlobalTheory.TorusExt.qkExt_iff hB _ hs _ _).2 rfl
  refine ⟨I, ⟨?_, ?_⟩, fun n a => (hext n a).1⟩
  · show ((Units.map s.toRingHom.toMonoidHom (I₀.ζ l.M') : Fˣ) : F) = _
    rw [Units.coe_map]
    show s.toRingHom ((I₀.ζ l.M' : AlgebraicClosure (FractionRing R))) = _
    rw [hI₀.1]
    simp only [toF, RingHom.comp_apply]
    exact s.commutes _
  · intro k a σ hk x hx
    have hk1 : 1 ≤ k := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact l.A_pos
      · have := l.three_le; omega
    have hT := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR.1 C.t C.P
    obtain ⟨f₀, f₀₁, -⟩ := hT (AlgebraicClosure (FractionRing R)) k hk1
    obtain ⟨fF, fF₁, -⟩ := hT F k hk1
    obtain ⟨g₀, hg₁, hg₂⟩ := hI₀.2 k a σ hk (f₀ (I₀.ev k a)) ((f₀₁ _ _).2 rfl)
    let x' : TFK (R := R) F ⟶ C.P.A.A :=
      (Over.homMk (spMap s.toRingHom) hj : TFK (R := R) F ⟶ TFK (R := R) (AlgebraicClosure (FractionRing R))) ≫
        f₀ (I₀.ev k a)
    have hx' : C.P.ToA F k (I.ev k a) x' :=
      (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hLL R (maximalIdeal R) hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U _ F s k hk1
        (I₀.ev k a) (I.ev k a) _ x' (hext k a) rfl).1 ((f₀₁ _ _).2 rfl)
    have hxx : x = x' := ((fF₁ _ _).1 hx).trans ((fF₁ _ _).1 hx').symm
    refine ⟨spMap s.toRingHom ≫ g₀, ?_, ?_⟩
    · rw [Category.assoc, hg₁, hxx]
      simp only [x', Over.comp_left, Over.homMk_left, Category.assoc]
    · rw [Category.assoc, hg₂, ← hj]
      simp only [Category.assoc]

end GlobalTheory.LowDat
