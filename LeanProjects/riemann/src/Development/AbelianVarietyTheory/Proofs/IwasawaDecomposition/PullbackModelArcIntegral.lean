import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparisonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcValuation

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcChartExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cast_φ {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f₁ f₂ : S' ⟶ S} (h : f₁ = f₂)
    (n : SABMap t' t f₁) : (h ▸ n).φ = n.φ := by
  subst h; rfl

theorem exists_sab_cancel_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t f) : ∃ m' : SABMap t'' t' (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ n)
  exact ⟨m', (sabMap_cast_φ (Category.id_comp f).symm n).symm.trans hm'⟩

theorem exists_sab_comp_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t' (𝟙 S')) : ∃ m' : SABMap t'' t f, m'.φ = n.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_comp m n
  exact ⟨Category.id_comp f ▸ m', (sabMap_cast_φ (Category.id_comp f) m').trans hm'⟩

theorem isArcChart_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)),
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∀ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j → IsArcChart Z a ϖ χ := by
  intro E _ _ _ H D l Xo c p W hp hpW Z Y bV hbV O' _ _ _ b' ϖ a χ₀ hO hχ₀ x₀ hx₀ χ hχ
  have hPS : IsNoetherianRing (PowerSeries O') ∧ IsIntegrallyClosed (PowerSeries O') := by
    rcases hO with ⟨hF, -⟩ | ⟨hD, -, -⟩
    · letI := hF.toField
      exact ⟨inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
    · exact ⟨inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
  haveI := hPS.1
  haveI := hPS.2
  obtain ⟨t, m₁, m₂, hc⟩ := GlobalTheory.T.integral_point_pullback_comparison E H D l Xo c W Z Y bV hbV (PowerSeries O') χ χ₀ x₀ hχ hx₀
  haveI := GlobalTheory.PolArcData.mono_spMap_incl bV hbV
  have eF := GlobalTheory.PolArcData.spMap_algebraMap_eq bV hbV
  haveI : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [eF]
    haveI := mono_spMap_subtype (c.V W)
    infer_instance
  have hZj : Mono Z.j := GlobalTheory.ThetaShiftProofs.mono_j Z inferInstance
  have hab : ∀ x, χ x ∈ abLocus Z.t.G ↔ χ₀ x ∈ abLocus Y.t.G := fun x =>
    (abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 x).trans (abLocus_pullback abLocusOne Y.t.semi m₂.cart.1 x).symm

  have h1 : χ ≫ Z.s = spMap (PowerSeries.C (R := O')) ≫ spMap (b'.comp bV) := by
    refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) (Out.jK (PowerSeries O')) ?_
    have e1 : Out.jK (PowerSeries O') ≫ χ ≫ Z.s = x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype ≫ spMap bV := by
      rw [← Category.assoc, hχ, Category.assoc, Model.j_s, eF]
    have e2 : Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap (b'.comp bV) =
        x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype ≫ spMap bV := by
      calc Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap (b'.comp bV)
          = (Out.jK (PowerSeries O') ≫ χ₀) ≫ Y.s ≫ spMap bV := by
            rw [spMap_comp, Category.assoc, ← Category.assoc χ₀, hχ₀.1]; simp only [Category.assoc]
        _ = x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype ≫ spMap bV := by
            rw [hx₀, Category.assoc, ← Category.assoc Y.j, Model.j_s]; simp only [Category.assoc]
    rw [e1, e2]

  have h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Z.t.G ↔ PowerSeries.X ∉ x.asIdeal := fun x =>
    (hab x).trans (hχ₀.2.1 x)

  have h3 : ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Z.j := by
    intro x hx
    obtain ⟨q, hq⟩ := hχ₀.2.2.1 x hx
    have hab' : χ x ∈ abLocus Z.t.G := (hab x).2 (hq ▸ GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y q)
    have k1 : (χ ≫ Z.s) x = (χ₀ ≫ Y.s ≫ spMap bV) x := by
      rw [h1, ← Category.assoc, hχ₀.1, spMap_comp, Category.assoc]
    have k2 : (Y.j ≫ Y.s ≫ spMap bV) q = (pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F)) q := by
      rw [← Category.assoc, Model.j_s, eF, Category.assoc]
    have hs : Z.s (χ x) ∈ Set.range (spMap (algebraMap (𝓞 c.F) c.F)) := by
      refine ⟨pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) q, ?_⟩
      simp only [Scheme.Hom.comp_apply] at k1 k2
      rw [← k2, hq, k1]
    obtain ⟨r, hr⟩ : χ x ∈ Set.range (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
      rw [Scheme.Pullback.range_fst]; exact hs
    have hr' : r ∈ Set.range Z.jQ := by
      rw [← Z.ab_gen, Set.mem_preimage, hr]; exact hab'
    obtain ⟨z, rfl⟩ := hr'
    exact ⟨z, by rw [Model.j, Scheme.Hom.comp_apply, hr]⟩

  refine ⟨h1, h2, h3, ?_⟩
  obtain ⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩ := hχ₀.2.2.2
  obtain ⟨n, hn⟩ := exists_sab_cancel_id m₂ m'
  obtain ⟨mZ, hmZ⟩ := exists_sab_comp_id m₁ n
  refine ⟨t', mZ, P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
    ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩
  have hyx : yF = Out.jFK (R := PowerSeries O') F ≫ x₀ := by
    rw [← cancel_mono Z.j, hyF, Category.assoc, hχ]
  have hyY : yF ≫ Y.j = Out.jFK (R := PowerSeries O') F ≫ Out.jK (PowerSeries O') ≫ χ₀ := by
    rw [hyx, Category.assoc, ← hx₀]
  have go : ∀ σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G, σ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ →
      x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK (PowerSeries O')) ≫ m'.φ = yF ≫ σY.left ≫ Y.m.φ := by
    intro σY h0
    have b₁ : σ.left ≫ Z.oF.t.G.hom = 𝟙 _ := Over.w σ
    have b₂ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σY
    have := hc _ (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK (PowerSeries O')) ≫ n.φ)
      (yF ≫ σ.left) (yF ≫ σY.left) (by rw [hmZ] at e4; simpa only [Category.assoc] using e4)
      (by rw [Category.assoc, h0, Category.assoc]) (by rw [Category.assoc, b₁, Category.assoc, b₂])
    rw [hn]; simpa only [Category.assoc] using this
  rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
  · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
      (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))
  · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
      (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))

end GlobalTheory.ArcChartExt
