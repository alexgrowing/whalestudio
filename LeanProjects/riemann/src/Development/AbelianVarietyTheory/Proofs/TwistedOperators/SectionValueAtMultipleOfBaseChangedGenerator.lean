import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EvRBaseChangeOfFromTest
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.HkValueMul

theorem fibreSectionScale_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (0 : S) i = 0 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_zero]

theorem fibreSectionScale_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (1 : S) i = 1 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem evR_of_secBC_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  intro E _ _ _ H Dw l Xo c a n f hf T Ω _ _ _ _ _ χ z₀ z₁ a₀ hx hu hs
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨w, hw⟩ := hL.bc T Ω χ z₀
  have key : ∃ g : Ωˣ, (g : Ω) = χ a₀ ∧ FrBor (fun i => i.elim g fun _ => 1) w z₁ := by
    have hw' := hw
    obtain ⟨wx, wo, wu, wtan, weig, wbas, ws, wgen⟩ := w
    obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z₁
    obtain ⟨hwx, hwu, pm, hp1, hp2, hp3⟩ := hw'
    dsimp only at hx hu hs hwx hwu hp1 hp2 hp3 ⊢
    subst hx
    subst hwx
    have hSw : GlobalTheory.Frames.SecBC χ.toRingHom 1 z₀.x (spMap χ.toRingHom ≫ z₀.x) z₀.s ws :=
      ⟨pm, hp1, hp2, fun i h => by rw [show Formalism.L2.Pj.scal z₀.x (1 : T) i = 1 from fibreSectionScale_one z₀.x i, _root_.one_mul]; exact hp3 i h⟩
    have hcalc := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo T Ω Ω χ.toRingHom (RingHom.id Ω) z₀.x
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) rfl (by simp [spMap])
    have hz : ∀ i, zs.f i = Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (χ a₀) i * ws.f i :=
      (hcalc.2.2.1 a₀ z₀.s ws zs hSw).1 hs
    have hne : χ a₀ ≠ 0 := by
      intro h0
      have hz0 : ∀ i, zs.f i = 0 := fun i => by rw [hz i, h0, show Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (0 : Ω) i = 0 from fibreSectionScale_zero _ i, MulZeroClass.zero_mul]
      obtain ⟨b, -, hb⟩ := zgen zs
      have e0 := hb 0 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      have e1 := hb 1 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      exact zero_ne_one (e0.trans e1.symm)
    have hcalc' := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo Ω Ω Ω (RingHom.id Ω) (RingHom.id Ω)
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x)
      (by simp [spMap]) (by simp [spMap])
    refine ⟨Units.mk0 _ hne, rfl, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2
      ⟨fun τ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp, rfl, fun τ i => ?_, ?_⟩⟩
    · have e : (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i = Pi.single i 1 := by
        ext j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      show IsCombAt _ (wu τ) ((1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i) (zu τ i)
      rw [e, (hu τ i).trans (hwu τ i).symm]
      exact Formalism.L2.PjFree.isCombAt_single (wtan τ) i
    · exact (hcalc'.2.1 _ ws zs).2 (by simpa using hz)
  obtain ⟨g, hg, hb⟩ := key
  rw [GlobalTheory.ArcQ.evR_scale_of_isReduced hL hf χ g z₀ w z₁ hw hb, hg, map_mul, map_pow]

end GlobalTheory.HkValueMul
