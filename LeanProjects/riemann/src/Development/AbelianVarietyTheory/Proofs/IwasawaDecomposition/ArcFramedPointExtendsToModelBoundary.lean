import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsChartPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom

theorem arc_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  intro E _ _ _ H Dw l Xo c σ O _ β Y a χ W _ e th y hF hχ hβ hB hA hab
  have hι : algebraMap (PowerSeries ℂ) ℂ⸨X⸩ = HahnSeries.ofPowerSeries ℤ ℂ := rfl
  have hFr : algebraMap c.F ℂ⸨X⸩ = ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))).comp σ :=
    RingHom.ext hF
  have hcond : χ ≫ Y.s = spMap ((PowerSeries.C (R := ℂ)).comp σ) ≫ spMap β := by
    rw [hχ, OpenReg.spMap_comp, OpenReg.spMap_comp]
  let χ' : Sp (PowerSeries ℂ) ⟶ gen Y := pullback.lift χ (spMap ((PowerSeries.C (R := ℂ)).comp σ)) hcond
  have hχ'1 : χ' ≫ genι Y = χ := pullback.lift_fst _ _ _
  have hχ'2 : χ' ≫ genStr Y = spMap ((PowerSeries.C (R := ℂ)).comp σ) := pullback.lift_snd _ _ _
  obtain ⟨v, hvL, hv⟩ := hB
  obtain ⟨z, t', m1, m2, φ, hz, hzx, hφ, h0, hm, hu, -⟩ := hA
  have hG : Out.GlobalFnsSt := known_holds.laws.globalFns

  have hzF : z = GlobalTheory.AllWt.ptF y := by
    apply pullback.hom_ext
    · rw [hzx, Descent.ptF_fst]
    · rw [Descent.ptF_snd]
      apply hβ.right_cancellation
      have e1 : z ≫ pullback.snd _ _ = z ≫ Y.jQ ≫ pullback.snd _ _ := by rw [Y.jQ_over]
      rw [e1, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc z, ← Category.assoc (z ≫ Y.jQ)]
      change (z ≫ Y.j) ≫ Y.s = _
      rw [hz, Category.assoc, hχ, OpenReg.spMap_comp, OpenReg.spMap_comp, OpenReg.spMap_comp, hFr]
  have hw : ∀ τ k, (v τ k).left ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
    fun τ k => (Over.w (v τ k)).trans (Category.comp_id _).symm
  let g : EigFrame Y ((PowerSeries.C (R := ℂ)).comp σ) (χ' ≫ genι Y) :=
    { v := fun τ k => (v τ k).left ≫ W.m.φ
      tan := fun τ k => by
        rw [hχ'1]
        exact (OpenReg.tan_iff W.m (Category.id_comp χ) (hw τ k)).2
          ((DepthExt.tan_iff W.t (v τ k)).1 ((hv τ).1 k).1)
      eig := fun τ k x => by
        exact (OpenReg.eig_iff W.m (hw τ k) x _).2 (((hv τ).1 k).2 x)
      basis := fun τ w htan heig => by
        rw [hχ'1] at htan ⊢
        obtain ⟨w0, hw01, hw02⟩ := OpenReg.exists_lift W.m (spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))))
          w (by rw [htan.1])
        subst hw02
        have hw0 : w0 ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
          hw01.trans (Category.comp_id _).symm
        let W0 : epsR (PowerSeries ℂ) ⟶ W.t.G := Over.homMk w0 hw01
        have t0 : IsTangent W0 := (DepthExt.tan_iff W.t W0).2 ((OpenReg.tan_iff W.m (Category.id_comp χ) hw0).1 htan)
        have e0 : ∀ x : 𝓞 E, (W0 ≫ W.t.act.act x).left =
            spMap (epsScaleR (PowerSeries.C (R := ℂ) ((σ.comp (embK c τ)) x))) ≫ W0.left := fun x =>
          (OpenReg.eig_iff W.m hw0 x _).1 (heig x)
        obtain ⟨cf, hcf, hu1⟩ := (hv τ).2 W0 t0 e0
        refine ⟨cf, ?_, fun cf' hcf' => hu1 cf' ?_⟩
        · exact (OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf hw0).2
            ((DepthExt.comb_iff W.t (v τ) cf W0).1 hcf)
        · exact (DepthExt.comb_iff W.t (v τ) cf' W0).2
            ((OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf' hw0).1 hcf') }
  refine ⟨χ', g, hχ'2, ?_, fun τ k => ?_, ?_⟩
  · rw [← hzF]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hχ'1]
      exact hz
    · rw [Category.assoc, Category.assoc, hχ'2, Y.jQ_over, hzF, Descent.ptF_snd, OpenReg.spMap_comp, hFr]
  · obtain ⟨v1, u', hL, h1, h2, h3⟩ := hu τ k
    obtain rfl : v1 = v τ k := (ConstLie.main hG E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W (e τ k)).1.unique hL (hvL τ k)
    refine ⟨u' ≫ φ, ?_, ?_, ?_⟩
    · rw [Category.assoc, hφ, ← Category.assoc, h3, hzF]
    · rw [Category.assoc, h0, h1]
    · rw [Category.assoc, hm, ← Category.assoc, h2, Category.assoc]
  · rw [mem_genBd_iff]
    rw [← hχ'1] at hab
    exact hab

end GlobalTheory.CuspFrom
